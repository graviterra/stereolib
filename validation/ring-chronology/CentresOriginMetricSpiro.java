import com.simolecule.centres.config.Tetrahedral;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/** Compare both uniform Rule 1b metrics on the spiro witness using the pinned
 * Centres adapter. All atom numbers and frame signs come from the V2000 input. */
public final class CentresOriginMetricSpiro {
  static Path fixture = Path.of("validation/ring-chronology/OriginMetricSpiro.mol");

  static int frame(List<double[]> positions, List<Integer> neighbors) {
    double[][] v = new double[3][3];
    for (int i = 0; i < 3; i++)
      for (int axis = 0; axis < 3; axis++)
        v[i][axis] = positions.get(neighbors.get(i))[axis] - positions.get(neighbors.get(3))[axis];
    double volume = v[0][0] * (v[1][1]*v[2][2] - v[1][2]*v[2][1])
                  - v[0][1] * (v[1][0]*v[2][2] - v[1][2]*v[2][0])
                  + v[0][2] * (v[1][0]*v[2][1] - v[1][1]*v[2][0]);
    if (volume == 0) throw new AssertionError("flat frame");
    return volume < 0 ? Tetrahedral.RIGHT : Tetrahedral.LEFT;
  }

  static CentresProbe molecule(boolean reflect) throws Exception {
    List<String> mol = Files.readAllLines(fixture);
    String[] counts = mol.get(3).trim().split("\\s+");
    int atoms = Integer.parseInt(counts[0]), bonds = Integer.parseInt(counts[1]);
    if (atoms != 13 || bonds != 16) throw new AssertionError("wrong fixture");
    CentresProbe m = new CentresProbe("spiro");
    List<double[]> positions = new ArrayList<>();
    for (int a = 0; a < atoms; a++) {
      String[] row = mol.get(4+a).trim().split("\\s+");
      m.elements.add(switch (row[3]) { case "C" -> 6; case "O" -> 8; case "H" -> 1;
        default -> throw new AssertionError("unexpected element"); });
      double x = Double.parseDouble(row[0]);
      positions.add(new double[]{reflect ? -x : x, Double.parseDouble(row[1]), Double.parseDouble(row[2])});
    }
    for (int j = 0; j < bonds; j++) {
      String[] row = mol.get(4+atoms+j).trim().split("\\s+");
      if (!row[2].equals("1")) throw new AssertionError("expected single bond");
      m.edges.add(new int[]{Integer.parseInt(row[0])-1, Integer.parseInt(row[1])-1});
    }
    for (int a = 0; a < atoms; a++) {
      if (m.elements.get(a) != 6) continue;
      List<Integer> ns = new ArrayList<>();
      for (int e : m.getBonds(a)) ns.add(m.getOther(e,a));
      if (ns.size() != 4) throw new AssertionError("expected four carbon ligands");
      m.frames.add(new int[]{a,frame(positions,ns),ns.get(0),ns.get(1),ns.get(2),ns.get(3)});
    }
    return m;
  }

  static String metric(CentresProbe m, boolean active) {
    return CentresAuxiliaryDistance.run(m, active, new CentresAuxiliaryDistance.Measurements(false));
  }

  public static void main(String[] args) throws Exception {
    if (args.length > 0) fixture = Path.of(args[0]);
    for (boolean reflect : new boolean[]{false,true}) {
      CentresProbe m = molecule(reflect);
      String original = CentresOxaziridineRoot.run(m,0);
      String control = metric(m,false), alternative = metric(m,true);
      if (!original.equals(control) || !control.equals(reflect ? "S" : "R") ||
          !alternative.equals(reflect ? "R" : "S")) throw new AssertionError(original+"/"+control+"/"+alternative);
      System.out.println("reflected="+reflect+" release="+original+" original="+control+" active="+alternative);
    }
    CentresProbe m = molecule(false);
    int differing = 0, count = 1 << m.frames.size();
    for (int mask = 0; mask < count; mask++) {
      for (int j = 0; j < m.frames.size(); j++)
        m.frames.get(j)[1] = ((mask >> j) & 1) == 0 ? Tetrahedral.RIGHT : Tetrahedral.LEFT;
      String original = CentresOxaziridineRoot.run(m,0);
      if (!original.equals(metric(m,false))) throw new AssertionError("control failed at "+mask);
      if (!original.equals(metric(m,true))) differing++;
    }
    if (count != 32 || differing != 16) throw new AssertionError("unexpected frame sweep");
    System.out.println("abstract handed-frame assignments changed="+differing+" of "+count);
  }
}
