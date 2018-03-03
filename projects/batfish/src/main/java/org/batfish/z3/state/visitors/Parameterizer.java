package org.batfish.z3.state.visitors;

import static org.batfish.z3.state.StateParameter.Type.ACL;
import static org.batfish.z3.state.StateParameter.Type.ACL_LINE;
import static org.batfish.z3.state.StateParameter.Type.INTERFACE;
import static org.batfish.z3.state.StateParameter.Type.NODE;
import static org.batfish.z3.state.StateParameter.Type.QUERY_NUMBER;
import static org.batfish.z3.state.StateParameter.Type.VRF;

import com.google.common.collect.ImmutableList;
import java.util.List;
import org.batfish.z3.expr.StateExpr;
import org.batfish.z3.state.Accept;
import org.batfish.z3.state.AclDeny;
import org.batfish.z3.state.AclLineMatch;
import org.batfish.z3.state.AclLineNoMatch;
import org.batfish.z3.state.AclPermit;
import org.batfish.z3.state.Debug;
import org.batfish.z3.state.Drop;
import org.batfish.z3.state.DropAcl;
import org.batfish.z3.state.DropAclIn;
import org.batfish.z3.state.DropAclOut;
import org.batfish.z3.state.DropNoRoute;
import org.batfish.z3.state.DropNullRoute;
import org.batfish.z3.state.NodeAccept;
import org.batfish.z3.state.NodeDrop;
import org.batfish.z3.state.NodeDropAcl;
import org.batfish.z3.state.NodeDropAclIn;
import org.batfish.z3.state.NodeDropAclOut;
import org.batfish.z3.state.NodeDropNoRoute;
import org.batfish.z3.state.NodeDropNullRoute;
import org.batfish.z3.state.NodeTransit;
import org.batfish.z3.state.NumberedQuery;
import org.batfish.z3.state.Originate;
import org.batfish.z3.state.OriginateVrf;
import org.batfish.z3.state.PostIn;
import org.batfish.z3.state.PostInInterface;
import org.batfish.z3.state.PostInVrf;
import org.batfish.z3.state.PostOutInterface;
import org.batfish.z3.state.PreInInterface;
import org.batfish.z3.state.PreOut;
import org.batfish.z3.state.PreOutEdge;
import org.batfish.z3.state.PreOutInterface;
import org.batfish.z3.state.Query;
import org.batfish.z3.state.StateParameter;

public class Parameterizer implements GenericStateExprVisitor<List<StateParameter>> {

  public static List<StateParameter> getParameters(StateExpr stateExpr) {
    Parameterizer visitor = new Parameterizer();
    return stateExpr.accept(visitor);
  }

  private Parameterizer() {}

  @Override
  public List<StateParameter> castToGenericStateExprVisitorReturnType(Object o) {
    return ((List<?>) o)
        .stream()
        .map(i -> (StateParameter) i)
        .collect(ImmutableList.toImmutableList());
  }

  @Override
  public List<StateParameter> visitAccept(Accept accept) {
    return ImmutableList.of();
  }

  @Override
  public List<StateParameter> visitAclDeny(AclDeny aclDeny) {
    return ImmutableList.of(
        new StateParameter(aclDeny.getHostname(), NODE), new StateParameter(aclDeny.getAcl(), ACL));
  }

  @Override
  public List<StateParameter> visitAclLineMatch(AclLineMatch aclLineMatch) {
    return ImmutableList.of(
        new StateParameter(aclLineMatch.getHostname(), NODE),
        new StateParameter(aclLineMatch.getAcl(), ACL),
        new StateParameter(Integer.toString(aclLineMatch.getLine()), ACL_LINE));
  }

  @Override
  public List<StateParameter> visitAclLineNoMatch(AclLineNoMatch aclLineNoMatch) {
    return ImmutableList.of(
        new StateParameter(aclLineNoMatch.getHostname(), NODE),
        new StateParameter(aclLineNoMatch.getAcl(), ACL),
        new StateParameter(Integer.toString(aclLineNoMatch.getLine()), ACL_LINE));
  }

  @Override
  public List<StateParameter> visitAclPermit(AclPermit aclPermit) {
    return ImmutableList.of(
        new StateParameter(aclPermit.getHostname(), NODE),
        new StateParameter(aclPermit.getAcl(), ACL));
  }

  @Override
  public List<StateParameter> visitDebug(Debug debug) {
    return ImmutableList.of();
  }

  @Override
  public List<StateParameter> visitDrop(Drop drop) {
    return ImmutableList.of();
  }

  @Override
  public List<StateParameter> visitDropAcl(DropAcl dropAcl) {
    return ImmutableList.of();
  }

  @Override
  public List<StateParameter> visitDropAclIn(DropAclIn dropAclIn) {
    return ImmutableList.of();
  }

  @Override
  public List<StateParameter> visitDropAclOut(DropAclOut dropAclOut) {
    return ImmutableList.of();
  }

  @Override
  public List<StateParameter> visitDropNoRoute(DropNoRoute dropNoRoute) {
    return ImmutableList.of();
  }

  @Override
  public List<StateParameter> visitDropNullRoute(DropNullRoute dropNullRoute) {
    return ImmutableList.of();
  }

  @Override
  public List<StateParameter> visitNodeAccept(NodeAccept nodeAccept) {
    return ImmutableList.of(new StateParameter(nodeAccept.getHostname(), NODE));
  }

  @Override
  public List<StateParameter> visitNodeDrop(NodeDrop nodeDrop) {
    return ImmutableList.of(new StateParameter(nodeDrop.getHostname(), NODE));
  }

  @Override
  public List<StateParameter> visitNodeDropAcl(NodeDropAcl nodeDropAcl) {
    return ImmutableList.of(new StateParameter(nodeDropAcl.getHostname(), NODE));
  }

  @Override
  public List<StateParameter> visitNodeDropAclIn(NodeDropAclIn nodeDropAclIn) {
    return ImmutableList.of(new StateParameter(nodeDropAclIn.getHostname(), NODE));
  }

  @Override
  public List<StateParameter> visitNodeDropAclOut(NodeDropAclOut nodeDropAclOut) {
    return ImmutableList.of(new StateParameter(nodeDropAclOut.getHostname(), NODE));
  }

  @Override
  public List<StateParameter> visitNodeDropNoRoute(NodeDropNoRoute nodeDropNoRoute) {
    return ImmutableList.of(new StateParameter(nodeDropNoRoute.getHostname(), NODE));
  }

  @Override
  public List<StateParameter> visitNodeDropNullRoute(NodeDropNullRoute nodeDropNullRoute) {
    return ImmutableList.of(new StateParameter(nodeDropNullRoute.getHostname(), NODE));
  }

  @Override
  public List<StateParameter> visitNodeTransit(NodeTransit nodeTransit) {
    return ImmutableList.of(new StateParameter(nodeTransit.getHostname(), NODE));
  }

  @Override
  public List<StateParameter> visitNumberedQuery(NumberedQuery numberedQuery) {
    return ImmutableList.of(
        new StateParameter(Integer.toString(numberedQuery.getLine()), QUERY_NUMBER));
  }

  @Override
  public List<StateParameter> visitOriginate(Originate originate) {
    return ImmutableList.of(new StateParameter(originate.getHostname(), NODE));
  }

  @Override
  public List<StateParameter> visitOriginateVrf(OriginateVrf originateVrf) {
    return ImmutableList.of(
        new StateParameter(originateVrf.getHostname(), NODE),
        new StateParameter(originateVrf.getVrf(), VRF));
  }

  @Override
  public List<StateParameter> visitPostIn(PostIn postIn) {
    return ImmutableList.of(new StateParameter(postIn.getHostname(), NODE));
  }

  @Override
  public List<StateParameter> visitPostInInterface(PostInInterface postInInterface) {
    return ImmutableList.of(
        new StateParameter(postInInterface.getHostname(), NODE),
        new StateParameter(postInInterface.getIface(), INTERFACE));
  }

  @Override
  public List<StateParameter> visitPostInVrf(PostInVrf postInVrf) {
    return ImmutableList.of(
        new StateParameter(postInVrf.getHostname(), NODE),
        new StateParameter(postInVrf.getVrf(), VRF));
  }

  @Override
  public List<StateParameter> visitPostOutInterface(PostOutInterface postOutInterface) {
    return ImmutableList.of(
        new StateParameter(postOutInterface.getHostname(), NODE),
        new StateParameter(postOutInterface.getIface(), INTERFACE));
  }

  @Override
  public List<StateParameter> visitPreInInterface(PreInInterface preInInterface) {
    return ImmutableList.of(
        new StateParameter(preInInterface.getHostname(), NODE),
        new StateParameter(preInInterface.getIface(), INTERFACE));
  }

  @Override
  public List<StateParameter> visitPreOut(PreOut preOut) {
    return ImmutableList.of(new StateParameter(preOut.getHostname(), NODE));
  }

  @Override
  public List<StateParameter> visitPreOutEdge(PreOutEdge preOutEdge) {
    return ImmutableList.of(
        new StateParameter(preOutEdge.getSrcNode(), NODE),
        new StateParameter(preOutEdge.getSrcIface(), INTERFACE),
        new StateParameter(preOutEdge.getDstNode(), NODE),
        new StateParameter(preOutEdge.getDstIface(), INTERFACE));
  }

  @Override
  public List<StateParameter> visitPreOutInterface(PreOutInterface preOutInterface) {
    return ImmutableList.of(
        new StateParameter(preOutInterface.getHostname(), NODE),
        new StateParameter(preOutInterface.getIface(), INTERFACE));
  }

  @Override
  public List<StateParameter> visitQuery(Query query) {
    return ImmutableList.of();
  }
}