import com.simolecule.centres.*;
import com.simolecule.centres.config.*;
import com.simolecule.centres.rules.*;
import java.nio.file.*;
import java.util.*;

/** Resolve the Rule 1b distance choice independently at each auxiliary address
 * of the requested atom. All other rules and the primary comparison are stock. */
public final class CentresSiteMetrics {
  record Outcome(String label, Set<List<Integer>> queried) {}
  static final class Run {
    final Map<List<Integer>,Boolean> choices;
    final Set<List<Integer>> queried = new LinkedHashSet<>();
    final boolean bySphere;
    final Map<Digraph<Integer,Integer>,CentresAuxiliaryDistance.Tree> trees = new IdentityHashMap<>();
    Run(Map<List<Integer>,Boolean> choices, boolean bySphere) {
      this.choices = choices;
      this.bySphere = bySphere;
    }
  }

  static final class Config extends Tetrahedral<Integer,Integer> {
    final CentresProbe mol;
    final Run run;
    Config(CentresProbe mol, int[] frame, Run run) {
      super(frame[0], CentresOxaziridineRoot.carriers(frame), frame[1]);
      this.mol = mol;
      this.run = run;
    }
    @Override public Descriptor label(Node<Integer,Integer> focus, Digraph<Integer,Integer> digraph,
                                      SequenceRule<Integer,Integer> rules) {
      if (digraph.getRoot().getAtom() != 0) return super.label(focus, digraph, rules);
      var tree = run.trees.computeIfAbsent(digraph, CentresAuxiliaryDistance.Tree::new);
      var path = new ArrayList<Integer>();
      for (var n = focus; n != null; n = tree.parent.get(n)) path.add(n.getAtom());
      Collections.reverse(path);
      var metric = new Rule1b<Integer,Integer>(mol) {
        @Override public int compare(Edge<Integer,Integer> a, Edge<Integer,Integer> b) {
          int stock = super.compare(a,b);
          var x = a.getEnd();
          var y = b.getEnd();
          if (!x.isSet(Node.RING_DUPLICATE) || !y.isSet(Node.RING_DUPLICATE)) return stock;
          var u = tree.origin(x);
          var v = tree.origin(y);
          if (stock != Integer.compare(tree.depth.get(v), tree.depth.get(u)))
            throw new AssertionError("construction distance");
          int active = Integer.compare(tree.distance(focus,v), tree.distance(focus,u));
          if (active == stock) return stock;
          List<Integer> key = run.bySphere ? List.of(path.size()-1) : path;
          run.queried.add(key);
          return run.choices.getOrDefault(key,false) ? active : stock;
        }
      };
      var mixed = new Rules<>(new Rule1a<>(mol),metric,new Rule2<>(mol),new Rule3<>(mol),
          new Rule4a<>(mol),new Rule4b<>(mol),new Rule4c<>(mol),new Rule5New<>(mol),new Rule6<>(mol));
      return super.label(focus,digraph,mixed);
    }
  }

  static Outcome evaluate(CentresProbe mol, Map<List<Integer>,Boolean> choices, boolean bySphere) {
    mol.properties.clear();
    var run = new Run(choices, bySphere);
    List<Configuration<Integer,Integer>> configs = new ArrayList<>();
    for (int[] frame : mol.frames) configs.add(new Config(mol,frame,run));
    new Labeller<Integer,Integer>().label(mol,configs);
    Object descriptor = mol.getAtomProp(0,BaseMol.CIP_LABEL_KEY);
    return new Outcome(descriptor == null ? "unassigned" : descriptor.toString(),run.queried);
  }

  static final class Search {
    final CentresProbe molecule;
    final Set<String> labels = new TreeSet<>();
    final Set<List<Integer>> addresses = new HashSet<>();
    final Map<List<Integer>,Boolean> choices = new LinkedHashMap<>();
    int leaves;
    final boolean bySphere;
    final int budget;
    Search(CentresProbe molecule, boolean bySphere, int budget) {
      this.molecule = molecule;
      this.bySphere = bySphere;
      this.budget = budget;
    }
    // Until the first unbound key is read, extending this assignment cannot
    // change control flow. Reuse the default-false run only on the false side.
    void visit(Outcome result) {
      addresses.addAll(result.queried);
      for (var address : result.queried) {
        if (choices.containsKey(address)) continue;
        choices.put(address,false);
        visit(result);
        choices.put(address,true);
        visit(evaluate(molecule,choices,bySphere));
        choices.remove(address);
        return;
      }
      if (++leaves > budget) throw new IllegalStateException("policy budget exceeded: " + molecule.name);
      labels.add(result.label);

    }
  }

  static void audit(CentresProbe molecule, boolean bySphere, int budget) {
    Outcome baseline = evaluate(molecule, Map.of(), bySphere);
    String stock = CentresOxaziridineRoot.run(molecule, 0);
    if (!stock.equals(baseline.label)) throw new AssertionError("stock control " + molecule.name);
    Search search = new Search(molecule, bySphere, budget);
    search.visit(baseline);
    String active = CentresAuxiliaryDistance.run(molecule, true, new CentresAuxiliaryDistance.Measurements(false));
    Map<List<Integer>,Boolean> all = new HashMap<>();
    for (var key : search.addresses) all.put(key, true);
    if (!evaluate(molecule, all, bySphere).label.equals(active)) throw new AssertionError("active control");
    System.out.println(String.join("\t", molecule.name, stock, active, Integer.toString(search.addresses.size()),
        Integer.toString(search.leaves), String.join(",", search.labels)));
  }

  // VS280's central pentagon has five equivalent substitution sites in the SDF.
  // Reflect the numbered 20-carbon perimeter around the requested carbon,
  // translating through the request's root-zero permutation in both directions.
  static int reflected(int id, int root) {
    if (id < 0 || id >= 20) throw new IllegalArgumentException("expected a carbon on the perimeter");
    int original = id == 0 ? root : id <= root ? id - 1 : id;
    int image = Math.floorMod(2 * root - original, 20);
    return image == root ? 0 : image < root ? image + 1 : image;
  }

  static void checkReflection(CentresProbe molecule, int root) {
    var byCenter = new HashMap<Integer,int[]>();
    for (var frame : molecule.frames) byCenter.put(frame[0], frame);
    for (int i = 0; i < 20; i++) {
      int j = reflected(i, root);
      int[] from = byCenter.get(i), to = byCenter.get(j);
      if (molecule.elements.get(i) != 6 || reflected(j, root) != i) throw new AssertionError("carbon map");
      var positions = new ArrayList<Integer>();
      int hydrogens = 0;
      for (int k = 2; k < 6; k++) {
        int id = from[k];
        if (molecule.elements.get(id) == 1) { hydrogens++; continue; }
        int mapped = reflected(id, root);
        int slot = 2;
        while (slot < 6 && to[slot] != mapped) slot++;
        if (slot == 6) throw new AssertionError("reflection breaks a bond");
        positions.add(slot);
      }
      // Two interchangeable terminal H allow either carrier permutation sign.
      if (hydrogens == 2) continue;
      if (hydrogens != 0) throw new AssertionError("unexpected VS280 valence");
      int inversions = 0;
      for (int a = 0; a < 4; a++)
        for (int b = a + 1; b < 4; b++)
          if (positions.get(a) > positions.get(b)) inversions++;
      if ((inversions % 2 == 1) != (from[1] != to[1])) throw new AssertionError("reflection reverses frame");
    }
  }

  static void vs280(CentresProbe molecule) {
    var match = java.util.regex.Pattern.compile("VS280-atom(3|7|11|15|19)\\.req").matcher(molecule.name);
    if (!match.matches()) throw new IllegalArgumentException(molecule.name);
    int root = Integer.parseInt(match.group(1)) - 1;
    checkReflection(molecule, root);
    var baseline = evaluate(molecule, Map.of(), false);
    if (!baseline.label.equals("R") || baseline.queried.size() != 32) throw new AssertionError("VS280 baseline");
    var seen = new HashSet<List<Integer>>();
    for (var path : baseline.queried) {
      if (!evaluate(molecule, Map.of(path, true), false).label.equals("unassigned"))
        throw new AssertionError("single-site control " + path);
      if (seen.contains(path)) continue;
      var partner = path.stream().map(i -> reflected(i, root)).toList();
      if (path.equals(partner) || !baseline.queried.contains(partner)) throw new AssertionError("path reflection");
      seen.add(path);
      seen.add(partner);
      if (!evaluate(molecule, Map.of(path, true, partner, true), false).label.equals("R"))
        throw new AssertionError("paired-site control " + path);
    }
    System.out.println(molecule.name + " 32 single-site refusals, 16 reflected-pair R");
  }

  static void synthetic() throws Exception {
    for (boolean mirror : new boolean[]{false, true}) {
      var molecule = CentresOriginMetricSpiro.molecule(mirror);
      var search = new Search(molecule, false, 16);
      search.visit(evaluate(molecule, Map.of(), false));
      var paths = List.of(List.of(0,1,3), List.of(0,5,7), List.of(0,2,3,4,1), List.of(0,6,7,8,5));
      if (!search.addresses.equals(Set.copyOf(paths)) || search.leaves != 16)
        throw new AssertionError("spiro path coverage");
      for (int mask = 0; mask < 16; mask++) {
        var chosen = new HashMap<List<Integer>,Boolean>();
        for (int bit = 0; bit < paths.size(); bit++) chosen.put(paths.get(bit), (mask & (1 << bit)) != 0);
        boolean reverses = (mask & 3) != 0;
        String expected = reverses == mirror ? "R" : "S";
        if (!evaluate(molecule, chosen, false).label.equals(expected))
          throw new AssertionError("spiro mask " + mask);
      }
    }
    var molecule = CentresOxaziridineRoot.make(3, 91);
    var left = List.of(0,6,7,8,5,4,3);
    var right = List.of(0,12,13,14,11,10,9);
    var search = new Search(molecule, false, 4);
    search.visit(evaluate(molecule, Map.of(), false));
    if (!search.addresses.equals(Set.of(left, right)) || search.leaves != 4)
      throw new AssertionError("oxaziridine path coverage");
    for (int mask = 0; mask < 4; mask++) {
      String expected = List.of("unassigned", "S", "R", "unassigned").get(mask);
      if (!evaluate(molecule, Map.of(left, (mask & 1) != 0, right, (mask & 2) != 0), false).label.equals(expected))
        throw new AssertionError("oxaziridine mask " + mask);
    }
    System.out.println("Spiro path truth table verified in both geometries; four oxaziridine masks verified");
  }

  public static void main(String[] args) throws Exception {
    if (args.length == 1 && args[0].equals("synthetic")) {
      synthetic();
      return;
    }
    if (args.length >= 2 && args[0].equals("vs280")) {
      for (int i = 1; i < args.length; i++) vs280(CentresPublishedMetric.read(Path.of(args[i])));
      return;
    }
    if (args.length < 3) throw new IllegalArgumentException("sphere|path POLICY_BUDGET REQUEST...");
    boolean bySphere = switch (args[0]) {
      case "sphere" -> true;
      case "path" -> false;
      default -> throw new IllegalArgumentException(args[0]);
    };
    int budget = Integer.parseInt(args[1]);
    for (int i = 2; i < args.length; i++) {
      audit(CentresPublishedMetric.read(Path.of(args[i])), bySphere, budget);
    }
  }
}
