// Adapter for the neutral, all-explicit, single-bond graphs from ExportInputs.lean.
// All ranking and auxiliary labels are computed by the unmodified Centres 1.0 core.
import com.simolecule.centres.BaseMol;
import com.simolecule.centres.Digraph;
import com.simolecule.centres.Labeller;
import com.simolecule.centres.config.Configuration;
import com.simolecule.centres.config.Tetrahedral;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;

public class CentresProbe extends BaseMol<Integer,Integer> {
  final List<Integer> elements = new ArrayList<>();
  final List<int[]> edges = new ArrayList<>();
  final List<int[]> frames = new ArrayList<>();
  final Map<Integer,Map<String,Object>> properties = new HashMap<>();
  final String name;

  CentresProbe(String name) { this.name = name; }

  public Object getBaseImpl() { return this; }
  public int getNumAtoms() { return elements.size(); }
  public int getNumBonds() { return edges.size(); }
  public Integer getAtom(int idx) { return idx; }
  public int getAtomIdx(Integer atom) { return atom; }
  public Integer getBond(int idx) { return idx; }
  public int getBondIdx(Integer bond) { return bond; }
  public Integer getBeg(Integer bond) { return edges.get(bond)[0]; }
  public Integer getEnd(Integer bond) { return edges.get(bond)[1]; }
  public Integer getOther(Integer bond, Integer atom) {
    if (atom.equals(getBeg(bond))) return getEnd(bond);
    if (atom.equals(getEnd(bond))) return getBeg(bond);
    throw new IllegalArgumentException("nonincident bond");
  }
  public Iterable<Integer> getBonds(Integer atom) {
    List<Integer> found = new ArrayList<>();
    for (int i = 0; i < edges.size(); ++i)
      if (atom.equals(getBeg(i)) || atom.equals(getEnd(i))) found.add(i);
    return found;
  }
  public boolean isInRing(Integer bond) {
    // The endpoints remain connected after removing exactly this edge.
    Set<Integer> seen = new HashSet<>();
    Deque<Integer> queue = new ArrayDeque<>();
    queue.add(getBeg(bond));
    while (!queue.isEmpty()) {
      int atom = queue.remove();
      if (!seen.add(atom)) continue;
      if (getEnd(bond).equals(atom)) return true;
      for (Integer otherBond : getBonds(atom))
        if (!otherBond.equals(bond)) queue.add(getOther(otherBond, atom));
    }
    return false;
  }
  public int getAtomicNum(Integer atom) { return elements.get(atom); }
  public int getNumHydrogens(Integer atom) { return 0; } // No implicit hydrogens.
  public int getMassNum(Integer atom) { return 0; }
  public int getCharge(Integer atom) { return 0; }
  public int getBondOrder(Integer bond) { return 1; }
  public void setAtomProp(Integer atom, String key, Object val) {
    properties.computeIfAbsent(atom, id -> new HashMap<>()).put(key, val);
  }
  @SuppressWarnings("unchecked")
  public <V> V getAtomProp(Integer atom, String key) {
    return (V) properties.getOrDefault(atom, Collections.emptyMap()).get(key);
  }
  public void setBondProp(Integer bond, String key, Object val) {
    throw new UnsupportedOperationException("tetrahedral-only input");
  }
  public <V> V getBondProp(Integer bond, String key) { return null; }
  public String dumpDigraph(Digraph<Integer,Integer> graph) { return name; }

  List<String> run(int flipped) {
    return run(flipped, (1 << frames.size()) - 1);
  }

  List<String> run(int flipped, int included) {
    properties.clear();
    List<Configuration<Integer,Integer>> configs = new ArrayList<>();
    for (int i = 0; i < frames.size(); ++i) {
      if ((included & (1 << i)) == 0) continue;
      int[] f = frames.get(i);
      Integer[] carriers = {f[2], f[3], f[4], f[5]};
      boolean right = (f[1] == Tetrahedral.RIGHT) ^ ((flipped & (1 << i)) != 0);
      configs.add(new Tetrahedral<>(f[0], carriers, right ? Tetrahedral.RIGHT : Tetrahedral.LEFT));
    }
    new Labeller<Integer,Integer>().label(this, configs);
    List<String> labels = new ArrayList<>();
    for (int[] f : frames) {
      Object label = getAtomProp(f[0], CIP_LABEL_KEY);
      labels.add(label == null ? "unassigned" : label.toString());
    }
    return labels;
  }

  static void read(List<String> lines) {
    List<CentresProbe> graphs = new ArrayList<>();
    CentresProbe mol = null;
    for (String line : lines) {
      String[] s = line.split(" ");
      switch (s[0]) {
        case "graph": mol = new CentresProbe(s[1]); graphs.add(mol); break;
        case "atom": mol.elements.add(Integer.parseInt(s[1])); break;
        case "bond": mol.edges.add(new int[]{Integer.parseInt(s[1]),Integer.parseInt(s[2])}); break;
        case "frame":
          if (s.length != 7 || !(s[2].equals("R") || s[2].equals("S")))
            throw new IllegalArgumentException(line);
          int[] frame = new int[6];
          frame[0] = Integer.parseInt(s[1]);
          frame[1] = s[2].equals("R") ? Tetrahedral.RIGHT : Tetrahedral.LEFT;
          for (int i = 2; i < 6; ++i) frame[i] = Integer.parseInt(s[i+1]);
          mol.frames.add(frame);
          break;
        default: throw new IllegalArgumentException(line);
      }
    }
    if (graphs.size() != 2 || !graphs.get(0).name.equals("spiro") || !graphs.get(1).name.equals("propellane")) throw new IllegalArgumentException("expected spiro and propellane");
    for (CentresProbe graph : graphs) {
      int expectedAtoms = graph.name.equals("spiro") ? 21 : 11;
      int expectedEdges = graph.name.equals("spiro") ? 22 : 13;
      int expectedFrames = graph.name.equals("spiro") ? 7 : 5;
      if (graph.elements.size() != expectedAtoms || graph.edges.size() != expectedEdges ||
          graph.frames.size() != expectedFrames) throw new IllegalArgumentException("fixture inventory");
      List<String> primary = graph.run(0);
      System.out.println(graph.name + " original " + primary);
      System.out.println(graph.name + " mirror " + graph.run((1 << graph.frames.size()) - 1));
      if (graph.name.equals("spiro")) {
        System.out.println("spiro annotated center only " + graph.run(0, 1));
        System.out.println("spiro annotated center only, mirror " + graph.run(1, 1));
      } else {
        Map<List<String>,Integer> counts = new LinkedHashMap<>();
        for (int mask = 0; mask < (1 << graph.frames.size()); ++mask)
          counts.merge(graph.run(mask), 1, Integer::sum);
        System.out.println("propellane all handed-frame combinations " + counts);
        // Each candidate is omitted, left, or right. Omit the empty inventory.
        int all = (1 << graph.frames.size()) - 1;
        Map<List<String>,Integer> inventoryCounts = new LinkedHashMap<>();
        for (int included = 1; included <= all; ++included) {
          int flip = included;
          while (true) {
            inventoryCounts.merge(graph.run(flip, included), 1, Integer::sum);
            if (flip == 0) break;
            flip = (flip - 1) & included;
          }
        }
        System.out.println("propellane all nonempty inventories and handed frames " + inventoryCounts);
      }
    }
  }

  public static void main(String[] args) throws Exception {
    read(Files.readAllLines(Paths.get(args[0])));
  }
}
