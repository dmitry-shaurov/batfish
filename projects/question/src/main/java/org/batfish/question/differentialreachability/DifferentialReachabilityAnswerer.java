package org.batfish.question.differentialreachability;

import static com.google.common.base.MoreObjects.firstNonNull;
import static org.batfish.datamodel.acl.AclLineMatchExprs.match;
import static org.batfish.question.specifiers.PathConstraintsUtil.createPathConstraints;
import static org.batfish.question.traceroute.TracerouteAnswerer.diffFlowTracesToRows;
import static org.batfish.question.traceroute.TracerouteAnswerer.metadata;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.LinkedHashMultiset;
import com.google.common.collect.Multiset;
import com.google.common.collect.Sets;
import com.google.common.collect.Streams;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.batfish.common.Answerer;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.AclIpSpace;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.Flow;
import org.batfish.datamodel.FlowHistory;
import org.batfish.datamodel.FlowHistory.FlowHistoryInfo;
import org.batfish.datamodel.IpSpace;
import org.batfish.datamodel.PacketHeaderConstraints;
import org.batfish.datamodel.PacketHeaderConstraintsUtil;
import org.batfish.datamodel.PathConstraints;
import org.batfish.datamodel.UniverseIpSpace;
import org.batfish.datamodel.acl.AclLineMatchExpr;
import org.batfish.datamodel.answers.Schema;
import org.batfish.datamodel.collections.NodeInterfacePair;
import org.batfish.datamodel.flow.Trace;
import org.batfish.datamodel.questions.Question;
import org.batfish.datamodel.table.ColumnMetadata;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.datamodel.table.TableDiff;
import org.batfish.datamodel.table.TableMetadata;
import org.batfish.question.ReachabilityParameters;
import org.batfish.specifier.FlexibleInferFromLocationIpSpaceSpecifierFactory;
import org.batfish.specifier.InterfaceLinkLocation;
import org.batfish.specifier.InterfaceLocation;
import org.batfish.specifier.IpSpaceAssignment;
import org.batfish.specifier.IpSpaceAssignment.Entry;
import org.batfish.specifier.IpSpaceSpecifierFactory;
import org.batfish.specifier.Location;
import org.batfish.specifier.SpecifierContext;

/** An {@link Answerer} for {@link DifferentialReachabilityQuestion}. */
public class DifferentialReachabilityAnswerer extends Answerer {
  public static final String COL_FLOW = "flow";

  static final String COL_BASE_TRACES = TableDiff.baseColumnName(getTracesColumnName());

  static final String COL_DELTA_TRACES = TableDiff.deltaColumnName(getTracesColumnName());

  public DifferentialReachabilityAnswerer(Question question, IBatfish batfish) {
    super(question, batfish);
  }

  private static String getTracesColumnName() {
    return "traces";
  }

  @Override
  public TableAnswerElement answer() {
    return answerDiff();
  }

  private Stream<NodeInterfacePair> interfacesOfBlacklistedNodes(
      Set<String> blacklist, Map<String, Configuration> configs) {
    return blacklist
        .stream()
        .flatMap(
            node ->
                !configs.containsKey(node)
                    ? Stream.of()
                    : configs
                        .get(node)
                        .getAllInterfaces()
                        .keySet()
                        .stream()
                        .map(iface -> new NodeInterfacePair(node, iface)));
  }

  private DifferentialReachabilityParameters parameters() {
    DifferentialReachabilityQuestion question = (DifferentialReachabilityQuestion) _question;
    PacketHeaderConstraints headerConstraints = question.getHeaderConstraints();
    IpSpaceSpecifierFactory flexibleIpSpaceSpecifierFactory =
        new FlexibleInferFromLocationIpSpaceSpecifierFactory();
    SpecifierContext baseCtxt = _batfish.specifierContext();
    Set<String> baseNodeBlacklist = _batfish.getEnvironment().getNodeBlacklist();
    Set<NodeInterfacePair> baseInterfaceBlacklist =
        _batfish.getEnvironment().getInterfaceBlacklist();

    _batfish.pushDeltaSnapshot();
    SpecifierContext deltaCtxt = _batfish.specifierContext();
    SortedSet<String> deltaNodeBlacklist = _batfish.getEnvironment().getNodeBlacklist();
    Set<NodeInterfacePair> deltaInterfaceBlacklist =
        _batfish.getEnvironment().getInterfaceBlacklist();
    _batfish.popSnapshot();

    Set<String> nodeBlacklist = Sets.union(baseNodeBlacklist, deltaNodeBlacklist);
    Set<Location> locationBlacklist =
        Streams.concat(
                interfacesOfBlacklistedNodes(baseNodeBlacklist, baseCtxt.getConfigs()),
                interfacesOfBlacklistedNodes(deltaNodeBlacklist, deltaCtxt.getConfigs()),
                baseInterfaceBlacklist.stream(),
                deltaInterfaceBlacklist.stream())
            .flatMap(
                nip ->
                    Stream.of(
                        new InterfaceLinkLocation(nip.getHostname(), nip.getInterface()),
                        new InterfaceLocation(nip.getHostname(), nip.getInterface())))
            .collect(Collectors.toSet());

    PathConstraints pathConstraints = createPathConstraints(question.getPathConstraints());

    /*
     * Include forbidden and required transit nodes in either snapshot.
     */
    Set<String> forbiddenTransitNodes =
        Sets.union(
            pathConstraints.getForbiddenLocations().resolve(baseCtxt),
            pathConstraints.getForbiddenLocations().resolve(deltaCtxt));
    Set<String> requiredTransitNodes =
        Sets.union(
            pathConstraints.getTransitLocations().resolve(baseCtxt),
            pathConstraints.getTransitLocations().resolve(deltaCtxt));

    /*
     * Only consider startLocations and finalNodes that exist in both snapshots.
     */
    Set<Location> startLocations =
        Sets.difference(
            Sets.intersection(
                pathConstraints.getStartLocation().resolve(baseCtxt),
                pathConstraints.getStartLocation().resolve(deltaCtxt)),
            locationBlacklist);
    Set<String> finalNodes =
        Sets.difference(
            Sets.intersection(
                pathConstraints.getEndLocation().resolve(baseCtxt),
                pathConstraints.getEndLocation().resolve(deltaCtxt)),
            nodeBlacklist);

    IpSpaceAssignment ipSpaceAssignment =
        flexibleIpSpaceSpecifierFactory
            .buildIpSpaceSpecifier(headerConstraints.getSrcIps())
            .resolve(startLocations, baseCtxt);
    IpSpace dstIps =
        firstNonNull(
            AclIpSpace.union(
                flexibleIpSpaceSpecifierFactory
                    .buildIpSpaceSpecifier(headerConstraints.getDstIps())
                    .resolve(ImmutableSet.of(), baseCtxt)
                    .getEntries()
                    .stream()
                    .map(Entry::getIpSpace)
                    .collect(ImmutableList.toImmutableList())),
            UniverseIpSpace.INSTANCE);
    AclLineMatchExpr headerSpace =
        match(
            PacketHeaderConstraintsUtil.toHeaderSpaceBuilder(headerConstraints)
                .setDstIps(dstIps)
                .build());

    return new DifferentialReachabilityParameters(
        ReachabilityParameters.filterDispositions(question.getActions().getDispositions()),
        forbiddenTransitNodes,
        finalNodes,
        headerSpace,
        ipSpaceAssignment,
        requiredTransitNodes);
  }

  @Override
  public TableAnswerElement answerDiff() {
    DifferentialReachabilityResult result = _batfish.bddReducedReachability(parameters());

    Set<Flow> flows =
        Sets.union(result.getDecreasedReachabilityFlows(), result.getIncreasedReachabilityFlows());

    if (_batfish.debugFlagEnabled("oldtraceroute")) {
      _batfish.pushBaseSnapshot();
      _batfish.processFlows(flows, false);
      _batfish.popSnapshot();
      _batfish.pushDeltaSnapshot();
      _batfish.processFlows(flows, false);
      _batfish.popSnapshot();

      FlowHistory flowHistory = _batfish.getHistory();
      Multiset<Row> rows = flowHistoryToRows(flowHistory);
      TableAnswerElement table = new TableAnswerElement(createMetadata());
      table.postProcessAnswer(_question, rows);
      return table;
    } else {
      _batfish.pushBaseSnapshot();
      Map<Flow, List<Trace>> baseFlowTraces = _batfish.buildFlows(flows, false);
      _batfish.popSnapshot();

      _batfish.pushDeltaSnapshot();
      Map<Flow, List<Trace>> deltaFlowTraces = _batfish.buildFlows(flows, false);
      _batfish.popSnapshot();

      Multiset<Row> rows = diffFlowTracesToRows(baseFlowTraces, deltaFlowTraces);
      TableAnswerElement table = new TableAnswerElement(metadata(true));
      table.postProcessAnswer(_question,rows);
      return table;
    }
  }

  private static TableMetadata createMetadata() {
    ImmutableList<ColumnMetadata> columnMetadata =
        ImmutableList.of(
            new ColumnMetadata(COL_FLOW, Schema.FLOW, "The flow", true, true),
            new ColumnMetadata(
                COL_BASE_TRACES,
                Schema.set(Schema.FLOW_TRACE),
                "The flow traces in the BASE environment",
                false,
                true),
            new ColumnMetadata(
                COL_DELTA_TRACES,
                Schema.set(Schema.FLOW_TRACE),
                "The flow traces in the DELTA environment",
                false,
                true));
    return new TableMetadata(columnMetadata, "Flows with reduced reachability");
  }

  /**
   * Converts a flowHistory object into a set of Rows. Expects that the traces correspond to only
   * one environment.
   */
  private Multiset<Row> flowHistoryToRows(FlowHistory flowHistory) {
    Multiset<Row> rows = LinkedHashMultiset.create();
    for (FlowHistoryInfo historyInfo : flowHistory.getTraces().values()) {
      rows.add(
          Row.of(
              COL_FLOW,
              historyInfo.getFlow(),
              COL_BASE_TRACES,
              historyInfo.getPaths().get(Flow.BASE_FLOW_TAG),
              COL_DELTA_TRACES,
              historyInfo.getPaths().get(Flow.DELTA_FLOW_TAG)));
    }
    return rows;
  }
}
