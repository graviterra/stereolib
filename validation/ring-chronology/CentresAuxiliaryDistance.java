import com.simolecule.centres.*;
import com.simolecule.centres.config.*;
import com.simolecule.centres.rules.*;
import java.util.*;

/** Finite uniform metric intervention in root-0 auxiliary evaluations.
 * No arguments runs both supported sweeps; SITE MASK ANCHOR traces a witness.
 * Requires CentresProbe, CentresOxaziridineRoot and unchanged pinned core classes.
 * Synthetic handed-frame assignments are not asserted to have physical embeddings.
 */
public final class CentresAuxiliaryDistance {
  static final class Measurements {
    long comparisons, reversals;
    final boolean trace;
    final Map<Digraph<Integer,Integer>,Tree> trees = new IdentityHashMap<>();
    Measurements(boolean trace) {
      this.trace = trace;
    }
  }
  // Parent identities and original depths are fixed before any metric comparison.
  static final class Tree {
    final IdentityHashMap<Node<Integer,Integer>,Node<Integer,Integer>> parent=new IdentityHashMap<>();
    final IdentityHashMap<Node<Integer,Integer>,Integer> depth=new IdentityHashMap<>();
    Tree(Digraph<Integer,Integer> g) {
      Node<Integer,Integer> current=g.getCurrRoot();
      g.changeRoot(g.getRoot());
      g.expandAll();
      visit(g.getRoot(),null,1);
      g.changeRoot(current);
    }
    void visit(Node<Integer,Integer> n,Node<Integer,Integer> p,int d) {
      if(depth.put(n,d)!=null)throw new AssertionError("not a tree");
      parent.put(n,p);
      if(!n.isDuplicate()&&n.getDistance()!=d)throw new AssertionError("real depth mismatch");
      for(Edge<Integer,Integer> e:n.getEdges()) {
        Node<Integer,Integer> x=e.getOther(n);
        if(x!=p)visit(x,n,d+1);
      }
    }
    Node<Integer,Integer> origin(Node<Integer,Integer> duplicate) {
      Node<Integer,Integer> n=parent.get(duplicate);
      while(n!=null) {
        if(!n.isDuplicate()&&n.getAtom().equals(duplicate.getAtom())) {
          if(depth.get(n)!=duplicate.getDistance())throw new AssertionError("origin depth mismatch");
          return n;
        }
        n=parent.get(n);
      }
      throw new AssertionError("origin absent");
    }
    // Unique tree-path distance via the lowest common ancestor.
    int distance(Node<Integer,Integer> a,Node<Integer,Integer> b) {
      int result=0;
      while(depth.get(a)>depth.get(b)) {
        a=parent.get(a);
        result++;
      }
      while(depth.get(b)>depth.get(a)) {
        b=parent.get(b);
        result++;
      }
      while(a!=b) {
        a=parent.get(a);
        b=parent.get(b);
        result+=2;
      }
      return result;
    }
  }
  static class Metric extends Rule1b<Integer,Integer> {
    final Tree tree;
    final Node<Integer,Integer> active;
    final boolean alternative;
    final Measurements measured;
    Metric(CentresProbe mol,Tree tree,Node<Integer,Integer> active,boolean alternative,Measurements measured) {
      super(mol);
      this.tree=tree;
      this.active=active;
      this.alternative=alternative;
      this.measured=measured;
    }
    @Override public int compare(Edge<Integer,Integer> a,Edge<Integer,Integer> b) {
      Node<Integer,Integer> x=a.getEnd(),y=b.getEnd();
      if(!x.isSet(Node.RING_DUPLICATE)||!y.isSet(Node.RING_DUPLICATE))return super.compare(a,b);
      Node<Integer,Integer> ox=tree.origin(x),oy=tree.origin(y);
      int original=-Integer.compare(tree.depth.get(ox),tree.depth.get(oy));
      if(original!=super.compare(a,b))throw new AssertionError("native metric disagreement");
      int changed=-Integer.compare(tree.distance(active,ox),tree.distance(active,oy));
      if(alternative) {
        measured.comparisons++;
        if(original*changed<0) {
          measured.reversals++;
          if(measured.trace)System.out.println("METRIC active="+active.getAtom()+"@"+active.getDistance()+" origins="+ox.getAtom()+"@"+tree.depth.get(ox)+","+oy.getAtom()+"@"+tree.depth.get(oy)+" activeDistances="+tree.distance(active,ox)+","+tree.distance(active,oy)+" compare="+original+"->"+changed);
        }
      }
      return alternative?changed:original;
    }
  }
  static class Config extends Tetrahedral<Integer,Integer> {
    final CentresProbe mol;
    final boolean alternative;
    final Measurements measured;
    Config(CentresProbe mol,int[] f,boolean alt,Measurements measured) {
      super(f[0],CentresOxaziridineRoot.carriers(f),f[1]);
      this.mol=mol;
      alternative=alt;
      this.measured=measured;
    }
    @SuppressWarnings("unchecked")
    @Override public Descriptor label(Node<Integer,Integer> n,Digraph<Integer,Integer> g,SequenceRule<Integer,Integer> ignored) {
      if(!g.getRoot().getAtom().equals(0))return super.label(n,g,ignored);
      Tree tree=measured.trees.get(g);
      if(tree==null) {
        tree=new Tree(g);
        measured.trees.put(g,tree);
      }
      // Exactly Labeller.allRules, replacing only its Rule1b instance.
      Rules<Integer,Integer> rules = new Rules<>(
          new Rule1a<>(mol), new Metric(mol, tree, n, alternative, measured),
          new Rule2<>(mol), new Rule3<>(mol), new Rule4a<>(mol),
          new Rule4b<>(mol), new Rule4c<>(mol), new Rule5New<>(mol), new Rule6<>(mol));
      return super.label(n,g,rules);
    }
  }
  static String run(CentresProbe mol,boolean alternative,Measurements measured) {
    measured.trees.clear();
    mol.properties.clear();
    List<Configuration<Integer,Integer>> configs=new ArrayList<>();
    for(int[] f:mol.frames)configs.add(new Config(mol,f,alternative,measured));
    new Labeller<Integer,Integer>().label(mol,configs);
    Object d=mol.getAtomProp(0,BaseMol.CIP_LABEL_KEY);
    return d==null?"unassigned":d.toString();
  }
  public static void main(String[] args) {
    if(args.length==3) {
      int site=Integer.parseInt(args[0]),mask=Integer.parseInt(args[1]);
      boolean anchor=Boolean.parseBoolean(args[2]);
      CentresProbe m=CentresOxaziridineRoot.make(site,mask,anchor);
      System.out.println("native="+CentresOxaziridineRoot.run(m,0)+" originalRecomputed="+run(m,false,new Measurements(false)));
      System.out.println("alternative="+run(m,true,new Measurements(true)));
      return;
    }
    if (args.length != 0) throw new IllegalArgumentException("expected no args or SITE MASK ANCHOR");
    for (boolean anchor : new boolean[]{false, true}) {
      int cases=0,changed=0;
      Measurements measured=new Measurements(false);
      Map<String,Integer> transitions=new TreeMap<>();
      for(int site=anchor?3:2;site<=(anchor?3:5);site++) {
        int count=1<<CentresOxaziridineRoot.make(site,0,anchor).frames.size();
        for(int mask=0;mask<count;mask++) {
          CentresProbe m=CentresOxaziridineRoot.make(site,mask,anchor);
          String nativeResult = CentresOxaziridineRoot.run(m, 0);
          String control = run(m, false, new Measurements(false));
          String modified = run(m, true, measured);
          if(!nativeResult.equals(control))throw new AssertionError("control mismatch site="+site+" mask="+mask);
          cases++;
          if(!nativeResult.equals(modified)) {
            changed++;
            if(changed<=8)System.out.println("CHANGE anchor="+anchor+" site="+site+" mask="+mask+" "+nativeResult+" -> "+modified);
          }
          transitions.merge(nativeResult+" -> "+modified,1,Integer::sum);
        }
      }
      int expectedCases=anchor?512:416;
      long expectedComparisons=anchor?1024:256;
      if(cases!=expectedCases || changed!=0 || measured.comparisons!=expectedComparisons
          || measured.reversals!=expectedComparisons)
        throw new AssertionError("unexpected uniform metric experiment totals");
      System.out.println("TOTAL anchor="+anchor+" cases="+cases+" changed="+changed+" comparisons="+measured.comparisons+" strictSignReversals="+measured.reversals+" transitions="+transitions);
    }
  }
}
