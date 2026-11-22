// Molecular adapter and final-root comparison recorder for Centres 1.0.
import com.simolecule.centres.*;
import com.simolecule.centres.config.*;
import com.simolecule.centres.rules.*;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.*;

public final class Centres10 extends BaseMol<Centres10.Atom, Centres10.Bond> {
  // The release compares carriers by object identity in Configuration.parity4.
  static final class Atom {
    final int id, number, mass, charge;
    final List<Bond> bonds = new ArrayList<>();
    final Map<String,Object> properties = new HashMap<>();
    Atom(int id, int number, int mass, int charge) {
      this.id = id; this.number = number; this.mass = mass; this.charge = charge;
    }
  }

  static final class Bond {
    final int id;
    final Atom a, b;
    final Map<String,Object> properties = new HashMap<>();
    Boolean inRing;
    Bond(int id, Atom a, Atom b) { this.id = id; this.a = a; this.b = b; }
  }

  static final class Frame {
    final Atom focus;
    final Atom[] carriers;
    final int hand;
    Frame(Atom focus, Atom[] carriers, int hand) {
      this.focus = focus; this.carriers = carriers; this.hand = hand;
    }
  }

  final List<Atom> atoms = new ArrayList<>();
  final List<Bond> bonds = new ArrayList<>();
  final List<Frame> frames = new ArrayList<>();
  final Set<Atom> centers = new HashSet<>();

  public Object getBaseImpl() { return this; }
  public int getNumAtoms() { return atoms.size(); }
  public int getNumBonds() { return bonds.size(); }
  public Atom getAtom(int i) { return atoms.get(i); }
  public int getAtomIdx(Atom a) { return a.id; }
  public Bond getBond(int i) { return bonds.get(i); }
  public int getBondIdx(Bond b) { return b.id; }
  public Iterable<Bond> getBonds(Atom a) { return a.bonds; }
  public Atom getBeg(Bond b) { return b.a; }
  public Atom getEnd(Bond b) { return b.b; }
  public Atom getOther(Bond b, Atom a) {
    if (a == b.a) return b.b;
    if (a == b.b) return b.a;
    throw new IllegalArgumentException("nonincident bond");
  }
  public boolean isInRing(Bond b) {
    if (b.inRing != null) return b.inRing;
    Deque<Atom> todo = new ArrayDeque<>();
    Set<Atom> seen = new HashSet<>();
    todo.add(b.a); seen.add(b.a);
    while (!todo.isEmpty()) {
      Atom current = todo.remove();
      if (current == b.b) return b.inRing = true;
      for (Bond next : current.bonds) {
        Atom other = getOther(next, current);
        if (next != b && seen.add(other)) todo.add(other);
      }
    }
    return b.inRing = false;
  }
  public int getAtomicNum(Atom a) { return a == null ? 1 : a.number; }
  public int getNumHydrogens(Atom a) { return 0; } // Input includes all explicit H atoms.
  public int getMassNum(Atom a) { return a == null ? 0 : a.mass; }
  public int getCharge(Atom a) { return a.charge; }
  public int getBondOrder(Bond b) { return 1; }
  public void setAtomProp(Atom a, String k, Object v) { a.properties.put(k,v); }
  @SuppressWarnings("unchecked")
  public <V> V getAtomProp(Atom a, String k) { return (V)a.properties.get(k); }
  public void setBondProp(Bond b, String k, Object v) { b.properties.put(k,v); }
  @SuppressWarnings("unchecked")
  public <V> V getBondProp(Bond b, String k) { return (V)b.properties.get(k); }
  public String dumpDigraph(Digraph<Atom,Bond> g) { return "Centres 1.0 ring input"; }

  void read(BufferedReader in) throws IOException {
    if (!"centres-1.0".equals(in.readLine())) throw new IOException("incorrect request format");
    for (String line; (line = in.readLine()) != null;) {
      String[] s = line.split(" ", -1);
      if (s[0].equals("a") && s.length == 4) {
        atoms.add(new Atom(atoms.size(),Integer.parseInt(s[1]),Integer.parseInt(s[2]),Integer.parseInt(s[3])));
      } else if (s[0].equals("b") && s.length == 3) {
        Atom a = atoms.get(Integer.parseInt(s[1])), b = atoms.get(Integer.parseInt(s[2]));
        Bond bond = new Bond(bonds.size(),a,b);
        bonds.add(bond); a.bonds.add(bond); b.bonds.add(bond);
      } else if (s[0].equals("f") && s.length == 7) {
        Atom focus = atoms.get(Integer.parseInt(s[1]));
        Atom[] carriers = new Atom[4];
        for (int j = 0; j < 4; j++) carriers[j] = atoms.get(Integer.parseInt(s[j+3]));
        int hand;
        if (s[2].equals("R")) hand = Tetrahedral.RIGHT;
        else if (s[2].equals("S")) hand = Tetrahedral.LEFT;
        else throw new IOException("invalid carrier handedness");
        if (!centers.add(focus)) throw new IOException("duplicate focus");
        frames.add(new Frame(focus, carriers, hand));
      } else throw new IOException("invalid molecular record");
    }
  }

  static class PassTrace {
    final List<String> trials = new ArrayList<>(), groups = new ArrayList<>();
    String after;
    public String toString() {
      return "{\"after\":" + after + ",\"trials\":" + trials + ",\"groups\":" + groups + "}";
    }
  }

  // Observe the sort at each assignment focus. The original subrules perform
  // their recursive comparisons directly on the live digraph.
  boolean logPrefixes;
  final List<String> prefixes = new ArrayList<>();

  final class RootRules extends SequenceRule<Atom,Bond> {
    final SequenceRule<Atom,Bond> original;
    final PassTrace pass;
    RootRules(SequenceRule<Atom,Bond> original, PassTrace pass) {
      super(original.getMol()); this.original = original; this.pass = pass;
    }
    public int compare(Edge<Atom,Bond> a, Edge<Atom,Bond> b) { return original.compare(a,b); }
    public int getNumSubRules() { return original.getNumSubRules(); }

    Sort<Atom,Bond> recordingSorter(List<String> events) {
      List<SequenceRule<Atom,Bond>> rules = original.getSorter().getRules();
      List<SequenceRule<Atom,Bond>> observed = new ArrayList<>();
      List<String> attempted = new ArrayList<>();
      for (int i = 0; i < rules.size(); i++) {
        final SequenceRule<Atom,Bond> rule = rules.get(i);
        final boolean last = (i+1 == rules.size());
        observed.add(new SequenceRule<Atom,Bond>(getMol()) {
          public int compare(Edge<Atom,Bond> a, Edge<Atom,Bond> b) { return rule.compare(a,b); }
          public int getComparision(Edge<Atom,Bond> a, Edge<Atom,Bond> b, boolean deep) {
            int v = rule.getComparision(a,b,deep);
            if (logPrefixes)
              attempted.add("[\"" + rule.getClass().getSimpleName() + "\"," + v + "]");
            if (v != 0 || last) {
              String operands = "{\"left\":" + a.getEnd().getAtom().id + ",\"right\":" + b.getEnd().getAtom().id;
              events.add(operands + ",\"value\":" + v + "}");
              if (logPrefixes) {
                prefixes.add(operands + ",\"rules\":" + attempted + "}");
                attempted.clear();
              }
            }
            return v;
          }
        });
      }
      return new Sort<>(observed);
    }

    public Sort<Atom,Bond> getSorter() { return recordingSorter(pass.groups); }
    public Priority sort(Node<Atom,Bond> node, List<Edge<Atom,Bond>> edges) {
      List<Integer> start = new ArrayList<>();
      for (Edge<Atom,Bond> edge : edges) start.add(edge.getEnd().getAtom().id);
      Atom mark = node.getDigraph().getRule6Ref();
      List<String> events = new ArrayList<>();
      Priority result = recordingSorter(events).prioritise(node,edges,true);
      pass.trials.add("{\"mark\":" + (mark == null ? "null" : mark.id) +
          ",\"start\":" + start + ",\"comparisons\":" + events + "}");
      return result;
    }
  }

  // Keep object identity for occurrences of the same atom reached by different paths.
  static final class Work {
    final Node<Atom,Bond> node;
    final int index;
    Descriptor result;
    final List<Integer> path = new ArrayList<>();
    Work(Node<Atom,Bond> node, int index) {
      this.node = node; this.index = index;
      for (Node<Atom,Bond> n = node; n != null;) {
        path.add(n.getAtom().id);
        Node<Atom,Bond> parent = null;
        for (Edge<Atom,Bond> edge : n.getEdges()) {
          if (edge.isEnd(n)) {
            if (parent != null) throw new IllegalStateException("multiple path parents");
            parent = edge.getBeg();
          }
        }
        n = parent;
      }
      if (path.size() != node.getDistance()) throw new IllegalStateException("incorrect path distance");
    }
    public String toString() {
      return path.toString();
    }
  }

  final class Schedule {
    final List<Work> discovered = new ArrayList<>(), pending = new ArrayList<>();
    final List<String> updates = new ArrayList<>();
    final Map<Node<Atom,Bond>,Work> byNode = new IdentityHashMap<>();
    int depth = Integer.MAX_VALUE;

    void discover(Digraph<Atom,Bond> graph) {
      for (Frame f : frames) {
        if (f.focus == graph.getRoot().getAtom()) continue;
        for (Node<Atom,Bond> n : graph.getNodes(f.focus)) {
          if (n.isDuplicate()) continue;
          Work w = new Work(n,discovered.size());
          if (byNode.put(n,w) != null) throw new IllegalStateException("duplicated auxiliary occurrence");
          discovered.add(w);
        }
      }
    }
    void published(List<Work> items) {
      for (Work w : items)
        if (w.result == null || w.node.getAux() != w.result)
          throw new IllegalStateException("missing or incorrect published descriptor");
    }
    Work before(Node<Atom,Bond> node) {
      if (node.getDistance() != depth) {
        published(pending); pending.clear(); depth = node.getDistance();
      }
      for (Work w : pending)
        if (w.node.getAux() != null) throw new IllegalStateException("same-distance label published early");
      Work w = byNode.get(node);
      if (w == null || w.result != null || node.getAux() != null)
        throw new IllegalStateException("unexpected auxiliary assignment");
      return w;
    }
  }

  final Map<Atom,Schedule> schedules = new IdentityHashMap<>();

  static String mark(Digraph<Atom,Bond> graph) {
    Atom a = graph.getRule6Ref();
    return a == null ? "null" : Integer.toString(a.id);
  }

  final class Observed extends Tetrahedral<Atom,Bond> {
    final List<PassTrace> passes = new ArrayList<>();
    Observed(Frame f) { super(f.focus,f.carriers,f.hand); }
    public Descriptor label(SequenceRule<Atom,Bond> rules) {
      PassTrace pass = new PassTrace(); passes.add(pass);
      boolean first = (rules.getNumSubRules() == 3);
      Schedule schedule = schedules.get(getFocus());
      if (!first) schedule.published(schedule.discovered);
      Descriptor d = super.label(new RootRules(rules,pass));
      pass.after = mark(getDigraph());
      if (first && (d == null || d == Descriptor.Unknown)) schedule.discover(getDigraph());
      return d;
    }
    public Descriptor label(Node<Atom,Bond> n, Digraph<Atom,Bond> graph, SequenceRule<Atom,Bond> rules) {
      Schedule schedule = schedules.get(graph.getRoot().getAtom());
      Work w = schedule.before(n);
      PassTrace pass = new PassTrace();
      Descriptor d = super.label(n,graph,new RootRules(rules,pass));
      pass.after = mark(graph);
      w.result = d;
      schedule.pending.add(w);
      schedule.updates.add("{\"index\":" + w.index + ",\"pass\":" + pass +
          ",\"label\":\"" + (d == Descriptor.Unknown ? "-" : d) + "\"}");
      return d;
    }
  }

  List<String> labels() {
    List<String> result = new ArrayList<>();
    for (Frame frame : frames) {
      Object d = frame.focus.properties.get(CIP_LABEL_KEY);
      String code = d == null ? "-" : d.toString();
      if (!Arrays.asList("-","R","S","r","s").contains(code))
        throw new IllegalStateException("unexpected tetrahedral descriptor " + code);
      result.add(code);
    }
    return result;
  }

  String evaluate() {
    List<Configuration<Atom,Bond>> configs = new ArrayList<>();
    for (Frame frame : frames) configs.add(new Tetrahedral<>(frame.focus,frame.carriers,frame.hand));
    new Labeller<Atom,Bond>().label(this,configs);
    List<String> plain = labels();
    for (Atom atom : atoms) atom.properties.clear();
    for (Bond bond : bonds) bond.properties.clear();
    configs.clear();
    List<Observed> observed = new ArrayList<>();
    for (Frame frame : frames) {
      schedules.put(frame.focus,new Schedule());
      Observed obs = new Observed(frame); observed.add(obs); configs.add(obs);
    }
    new Labeller<Atom,Bond>().label(this,configs);
    if (!plain.equals(labels())) throw new IllegalStateException("observation changed core output");
    List<String> rows = new ArrayList<>();
    for (int i = 0; i < observed.size(); i++) {
      Schedule schedule = schedules.get(frames.get(i).focus);
      rows.add("{\"atom\":" + frames.get(i).focus.id + ",\"passes\":" + observed.get(i).passes +
          ",\"discovered\":" + schedule.discovered + ",\"updates\":" + schedule.updates +
          ",\"label\":\"" + plain.get(i) + "\"}");
    }
    return logPrefixes ? "{\"traces\":" + rows + ",\"observed\":" + prefixes + "}" : rows.toString();
  }

  public static void main(String[] args) throws IOException {
    Centres10 mol = new Centres10();
    if (args.length == 1 && args[0].equals("--rule-prefixes")) mol.logPrefixes = true;
    else if (args.length != 0) throw new IllegalArgumentException("unknown tracing mode");
    mol.read(new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8)));
    System.out.println(mol.evaluate());
  }
}
