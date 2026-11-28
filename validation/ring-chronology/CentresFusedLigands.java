import com.simolecule.centres.config.Tetrahedral;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** All framed stereoisomers of a carbinol carrying two octahydroinden-4-yl arms.
 * The three bits per arm are the SMILES parities at C4, C7a, C3a in that order.
 * The model uses explicit hydrogens and single bonds throughout. */
public final class CentresFusedLigands {
  static void bond(CentresProbe m, int a, int b) {
    m.edges.add(new int[]{a, b});
  }

  static CentresProbe molecule() {
    var m = new CentresProbe("bis(octahydroindenyl)carbinol");
    for (int i = 0; i < 20; i++) m.elements.add(i == 1 ? 8 : 6);
    bond(m, 0, 1);
    for (int b : List.of(2, 11)) {
      bond(m, 0, b);
      for (int i = b; i < b + 8; i++) bond(m, i, i + 1);
      bond(m, b, b + 8);
      bond(m, b + 4, b + 8);
    }
    int[] hydrogen = new int[20];
    for (int i = 0; i < 20; i++) {
      int degree = 0;
      for (int ignored : m.getBonds(i)) degree++;
      int valence = i == 1 ? 2 : 4;
      for (; degree < valence; degree++) {
        hydrogen[i] = m.elements.size();
        m.elements.add(1);
        bond(m, i, hydrogen[i]);
      }
    }
    // Ligands in SMILES traversal order, with ring digits at their written positions.
    m.frames.add(new int[]{0, 0, 1, 2, 11, hydrogen[0]});
    for (int b : List.of(2, 11)) {
      m.frames.add(new int[]{b, 0, 0, b + 8, b + 1, hydrogen[b]});
      m.frames.add(new int[]{b + 4, 0, b + 3, b + 8, b + 5, hydrogen[b + 4]});
      m.frames.add(new int[]{b + 8, 0, b + 7, b, b + 4, hydrogen[b + 8]});
    }
    return m;
  }

  record Arm(boolean attachment, boolean farJunction, boolean nearJunction) {
    static Arm decode(int bits) {
      return new Arm((bits & 1) != 0, (bits & 2) != 0, (bits & 4) != 0);
    }

    int relativeRank(boolean active) {
      boolean first = attachment == nearJunction;
      boolean sameFarHand = attachment == farJunction;
      boolean second = active ? sameFarHand : !sameFarHand;
      return (first ? 2 : 0) + (second ? 1 : 0);
    }
  }

  static String predicted(boolean rootRight, Arm left, Arm right, boolean active) {
    if (left.equals(right)) return "unassigned";
    int order = Integer.compare(left.relativeRank(active), right.relativeRank(active));
    boolean pseudo = order == 0;
    if (pseudo) order = Boolean.compare(left.attachment, right.attachment);
    boolean isR = rootRight == (order > 0);
    return pseudo ? (isR ? "r" : "s") : (isR ? "R" : "S");
  }

  public static void main(String[] args) {
    var m = molecule();
    if (args.length == 1 && args[0].equals("--frames")) {
      for (int z : m.elements) System.out.println("a " + z);
      for (int[] edge : m.edges) System.out.printf("b %d %d%n", edge[0], edge[1]);
      for (int[] f : m.frames) System.out.printf("f %d %d %d %d%n", f[2], f[3], f[4], f[5]);
      for (int mask = 0; mask < 128; mask++) {
        String label = predicted((mask & 1) != 0, Arm.decode(mask >> 1), Arm.decode(mask >> 4), false);
        System.out.printf("p %d %s%n", mask, label);
      }
      return;
    }
    if (args.length != 0) throw new IllegalArgumentException("expected no arguments or --frames");
    int changed = 0;
    int leaves = 0;
    for (int mask = 0; mask < 128; mask++) {
      for (int j = 0; j < m.frames.size(); j++) {
        m.frames.get(j)[1] = (mask & (1 << j)) == 0 ? Tetrahedral.LEFT : Tetrahedral.RIGHT;
      }
      boolean rootRight = (mask & 1) != 0;
      Arm left = Arm.decode(mask >> 1);
      Arm right = Arm.decode(mask >> 4);
      String stock = CentresOxaziridineRoot.run(m, 0);
      String active = CentresAuxiliaryDistance.run(m, true, new CentresAuxiliaryDistance.Measurements(false));
      if (!stock.equals(predicted(rootRight, left, right, false)) ||
          !active.equals(predicted(rootRight, left, right, true))) {
        throw new AssertionError("arm formula disagrees at mask " + mask);
      }
      if (!stock.equals(active)) changed++;
      var baseline = CentresSiteMetrics.evaluate(m, Map.of(), false);
      var search = new CentresSiteMetrics.Search(m, false, 16);
      search.visit(baseline);
      // Only comparisons tied at the first relative parity can see the switch.
      Set<String> expected;
      boolean leftNearMatches = left.attachment == left.nearJunction;
      boolean rightNearMatches = right.attachment == right.nearJunction;
      if (leftNearMatches != rightNearMatches) {
        expected = Set.of(stock);
      } else if (left.equals(right) || left.relativeRank(false) == right.relativeRank(false)) {
        expected = Set.of(stock, "R", "S");
      } else {
        expected = Set.of("R", "S");
      }
      if (!baseline.label().equals(stock) || !search.labels.equals(expected) || search.leaves != 16) {
        throw new AssertionError("occurrence policies disagree at mask " + mask);
      }
      leaves += search.leaves;
    }
    System.out.printf("128 frame inventories, %d uniform reversals, %d occurrence-policy leaves%n", changed, leaves);
  }
}
