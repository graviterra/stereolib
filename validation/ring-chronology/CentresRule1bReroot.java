import com.simolecule.centres.Digraph;
import com.simolecule.centres.Edge;
import com.simolecule.centres.Node;
import com.simolecule.centres.rules.Rule1b;

/** Probe only: all graph construction, rerooting and Rule1b comparison use pinned core bytes. */
public final class CentresRule1bReroot {
  static Node<Integer,Integer> step(Node<Integer,Integer> node, int atom) {
    for (Edge<Integer,Integer> edge : node.getOutEdges())
      if (edge.getEnd().getAtom().equals(atom) && !edge.getEnd().isDuplicate()) return edge.getEnd();
    throw new AssertionError("missing real path atom " + atom);
  }
  static Edge<Integer,Integer> duplicate(Node<Integer,Integer> node, int atom) {
    for (Edge<Integer,Integer> edge : node.getOutEdges())
      if (edge.getEnd().getAtom().equals(atom) && edge.getEnd().isSet(Node.RING_DUPLICATE)) return edge;
    throw new AssertionError("missing ring duplicate " + atom);
  }
  public static void main(String[] args) {
    CentresProbe mol = new CentresProbe("K-C4-C5-C-O-N; N-K,N-C");
    int[] zs = {6,6,6,6,8,7};
    for (int z : zs) mol.elements.add(z);
    int[][] bonds = {{0,1},{1,2},{2,3},{3,4},{4,5},{5,0},{5,3}};
    for (int[] bond : bonds) mol.edges.add(bond);
    Digraph<Integer,Integer> graph = new Digraph<>(mol);
    java.util.List<Node<Integer,Integer>> path = new java.util.ArrayList<>();
    Node<Integer,Integer> node = graph.init(0);
    path.add(node);
    for (int atom : new int[]{1,2,3,4,5}) {
      node = step(node, atom);
      path.add(node);
    }
    Edge<Integer,Integer> k = duplicate(node,0), c = duplicate(node,3);
    Rule1b<Integer,Integer> rule = new Rule1b<>(mol);
    int kd = k.getEnd().getDistance(), cd = c.getEnd().getDistance();
    int before = rule.compare(k,c);
    System.out.printf("before originalRoot=K activeRoot=K comparisonSite=N Ndistance=%d Kduplicate=%d Cduplicate=%d Rule1b(K,C)=%d winner=%s%n",
      node.getDistance(),kd,cd,before,before>0?"K":"C");
    graph.changeRoot(node);
    int after = rule.compare(k,c);
    System.out.printf("after changeRoot(N) originalRoot=%d currentRoot=%d Ndistance=%d Kduplicate=%d Cduplicate=%d Rule1b(K,C)=%d winner=%s%n",
      graph.getRoot().getAtom(),graph.getCurrRoot().getAtom(),node.getDistance(),
      k.getEnd().getDistance(),c.getEnd().getDistance(),after,after>0?"K":"C");
    if (kd!=1 || cd!=4 || before!=1 || after!=1 || graph.getCurrRoot()!=node ||
        k.getEnd().getDistance()!=kd || c.getEnd().getDistance()!=cd)
      throw new AssertionError("pinned reroot semantics changed");
    Node<Integer,Integer> cursor = graph.getCurrRoot();
    int fromN = 0;
    int toRingCarbon = -1;
    for (int index = path.size() - 2; index >= 0; index--) {
      Node<Integer,Integer> target = path.get(index);
      cursor = step(cursor, target.getAtom());
      if (cursor != target) throw new AssertionError("rerooted edge did not reach the original occurrence");
      fromN++;
      if (target == path.get(3)) toRingCarbon = fromN;
    }
    if (cursor != graph.getRoot() || fromN != 5 || toRingCarbon != 2)
      throw new AssertionError("unexpected path distances from the auxiliary nitrogen");
    System.out.printf("retained edges from active N to real K=%d and real C=%d; nearer from N=C%n",
      fromN, toRingCarbon);
  }
}
