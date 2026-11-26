import com.simolecule.centres.BaseMol;
import com.simolecule.centres.Descriptor;
import com.simolecule.centres.Digraph;
import com.simolecule.centres.Edge;
import com.simolecule.centres.Labeller;
import com.simolecule.centres.Node;
import com.simolecule.centres.config.Configuration;
import com.simolecule.centres.config.Tetrahedral;
import com.simolecule.centres.rules.SequenceRule;
import java.util.*;

/** Finite differential test, using synthetic handed frames, not embedded geometry.
 * Requires CentresProbe and the unchanged pinned Centres 1.0 core on the classpath.
 * No arguments: enumerate all frames. "sample": dump attachment K, mask 14.
 */
public final class CentresOxaziridineRoot {
  // Modes: regular=0, no-op subclass=1, both Ns=2, left N=3, right N=4.
  static boolean trace;
  static long calls, flips;
  static final Map<String, Long> occurrenceFlips = new TreeMap<>();

  static final class AuxiliaryIntervention extends Tetrahedral<Integer, Integer> {
    final CentresProbe mol;
    final int mode;

    AuxiliaryIntervention(CentresProbe mol, int[] frame, int mode) {
      super(frame[0], carriers(frame), frame[1]);
      this.mol = mol;
      this.mode = mode;
    }

    @Override public Descriptor label(Node<Integer, Integer> node,
        Digraph<Integer, Integer> graph, SequenceRule<Integer, Integer> rules) {
      Descriptor original = super.label(node, graph, rules);
      // Restrict intervention and accounting to the requested primary digraph.
      // The primary label(SequenceRule) method is inherited without modification.
      if (!graph.getRoot().getAtom().equals(0)) return original;
      calls++;
      int carbons = 0, ringDuplicateCarbons = 0;
      for (Edge<Integer, Integer> edge : node.getEdges()) {
        Node<Integer, Integer> other = edge.getOther(node);
        if (other.getAtom() != null && mol.getAtomicNum(other.getAtom()) == 6) {
          carbons++;
          if (other.isSet(Node.RING_DUPLICATE)) ringDuplicateCarbons++;
        }
      }
      boolean selectedArm = mode == 2 || (mode == 3 && node.getAtom() == 3)
          || (mode == 4 && node.getAtom() == 9);
      boolean target = mol.getAtomicNum(node.getAtom()) == 7
          && carbons == 2 && ringDuplicateCarbons == 2;
      if (!selectedArm || !target || (original != Descriptor.R && original != Descriptor.S))
        return original;
      Descriptor switched = original == Descriptor.R ? Descriptor.S : Descriptor.R;
      flips++;
      String occurrence = "N=" + node.getAtom() + ",distance=" + node.getDistance()
          + "," + original + "->" + switched;
      occurrenceFlips.merge(occurrence, 1L, Long::sum);
      if (trace) {
        StringBuilder directions = new StringBuilder();
        for (Edge<Integer, Integer> edge : node.getEdges()) {
          Node<Integer, Integer> other = edge.getOther(node);
          directions.append(" [atom=").append(other.getAtom())
              .append(" z=").append(mol.getAtomicNum(other.getAtom()))
              .append(" distance=").append(other.getDistance())
              .append(" ringDuplicate=").append(other.isSet(Node.RING_DUPLICATE)).append("]");
        }
        System.out.println("FLIP primaryRoot=0 " + occurrence + directions);
      }
      return switched;
    }
  }

  static Integer[] carriers(int[] frame) {
    return new Integer[]{frame[2], frame[3], frame[4], frame[5]};
  }

  static int atom(CentresProbe mol, int atomicNumber) {
    mol.elements.add(atomicNumber);
    return mol.elements.size() - 1;
  }

  static void bond(CentresProbe mol, int a, int b) {
    mol.edges.add(new int[]{a, b});
  }

  static CentresProbe make(int site, int mask) {
    return make(site, mask, false);
  }

  static CentresProbe make(int site, int mask, boolean anchor) {
    CentresProbe mol = new CentresProbe("site" + site + "mask" + mask);
    atom(mol, 6); atom(mol, 1); atom(mol, 9);
    bond(mol, 0, 1); bond(mol, 0, 2);
    // In each copy the local order is N,O,C,K,C4,C5. Both copies have identical
    // constitution and attachment sites; their local handed frames vary independently.
    for (int arm = 0; arm < 2; arm++) {
      int offset = mol.elements.size();
      for (int z : new int[]{7, 8, 6, 6, 6, 6}) atom(mol, z);
      for (int[] edge : new int[][]{{0,1},{1,2},{2,0},{0,3},{3,4},{4,5},{5,2}})
        bond(mol, offset + edge[0], offset + edge[1]);
      bond(mol, 0, offset + site);
    }
    int heavyCount = mol.elements.size();
    for (int a = 3; a < heavyCount; a++) {
      int z = mol.elements.get(a);
      int valence = z == 6 ? 4 : z == 7 ? 3 : 2;
      int degree = 0;
      for (Integer ignored : mol.getBonds(a)) degree++;
      if (degree > valence) throw new AssertionError("invalid valence");
      for (int k = degree; k < valence; k++) bond(mol, a, atom(mol, 1));
    }
    if (anchor) {
      if (site != 3) throw new IllegalArgumentException("anchor requires K attachment");
      // Add the same root-CH(Cl)-K spacer to each constitutionally identical arm.
      for (int k : new int[]{6, 12}) {
        int spacer = atom(mol, 6);
        boolean replaced = false;
        for (int[] edge : mol.edges) {
          if (edge[0] == 0 && edge[1] == k) {
            edge[1] = spacer;
            replaced = true;
            break;
          }
        }
        if (!replaced) throw new AssertionError("missing K attachment");
        bond(mol, spacer, k);
        bond(mol, spacer, atom(mol, 1));
        bond(mol, spacer, atom(mol, 17));
      }
    }
    int frameIndex = 0;
    for (int a = 0; a < mol.elements.size(); a++) {
      if (mol.elements.get(a) != 6 && mol.elements.get(a) != 7) continue;
      List<Integer> neighbors = new ArrayList<>();
      for (Integer b : mol.getBonds(a)) neighbors.add(mol.getOther(b, a));
      if (neighbors.size() == 3) neighbors.add(a); // N lone-pair carrier convention.
      int hydrogens = 0;
      for (int neighbor : neighbors) if (mol.elements.get(neighbor) == 1) hydrogens++;
      if (neighbors.size() != 4) throw new AssertionError("carrier inventory");
      if (hydrogens >= 2) continue; // No frames on nonstereogenic CH2 twins.
      int hand = ((mask >> frameIndex++) & 1) == 0 ? Tetrahedral.RIGHT : Tetrahedral.LEFT;
      mol.frames.add(new int[]{a, hand, neighbors.get(0), neighbors.get(1),
          neighbors.get(2), neighbors.get(3)});
    }
    return mol;
  }

  static String run(CentresProbe mol, int mode) {
    mol.properties.clear();
    List<Configuration<Integer, Integer>> configs = new ArrayList<>();
    for (int[] frame : mol.frames)
      configs.add(mode == 0 ? new Tetrahedral<>(frame[0], carriers(frame), frame[1])
          : new AuxiliaryIntervention(mol, frame, mode));
    // Exceptions intentionally propagate: a refusal is only an absent primary label.
    new Labeller<Integer, Integer>().label(mol, configs);
    Object descriptor = mol.getAtomProp(0, BaseMol.CIP_LABEL_KEY);
    return descriptor == null ? "unassigned" : descriptor.toString();
  }

  /** Exhaustive local-frame control with two common CH(Cl) spacers.
   * Equal anchor bits compare corresponding carrier orders root,K,H,Cl.
   * These are synthetic frame assignments, with no embedding assertion.
   */
  static void anchoredControl() {
    long startFlips = flips;
    int frameCount = make(3, 0, true).frames.size();
    if (frameCount != 9) throw new AssertionError("anchored frame inventory");
    int tested = 0, triggered = 0, changed = 0;
    int equalTested = 0, equalTriggered = 0, equalChanged = 0;
    long equalFlips = 0;
    Map<String, Integer> transitions = new TreeMap<>();
    Map<String, Integer> equalTransitions = new TreeMap<>();
    for (int mask = 0; mask < (1 << frameCount); mask++) {
      CentresProbe mol = make(3, mask, true);
      String baseline = run(mol, 0), control = run(mol, 1);
      if (!baseline.equals(control)) throw new AssertionError("anchored baseline disagreement");
      long before = flips;
      String modified = run(mol, 2);
      long switched = flips - before;
      // The anchors are appended after the seven original candidate frames.
      boolean equalAnchors = ((mask >> 7) & 1) == ((mask >> 8) & 1);
      tested++;
      if (switched > 0) triggered++;
      if (!baseline.equals(modified)) changed++;
      transitions.merge(baseline + " -> " + modified, 1, Integer::sum);
      if (equalAnchors) {
        equalTested++;
        if (switched > 0) equalTriggered++;
        if (!baseline.equals(modified)) equalChanged++;
        equalFlips += switched;
        equalTransitions.merge(baseline + " -> " + modified, 1, Integer::sum);
      }
    }
    long totalFlips = flips - startFlips;
    if (tested != 512 || triggered != 512 || changed != 0 || totalFlips != 1024
        || equalTested != 256 || equalTriggered != 256 || equalChanged != 0 || equalFlips != 512)
      throw new AssertionError("unexpected anchored control totals");
    System.out.println("ANCHOR both-arm tested=" + tested + " triggered=" + triggered
        + " flips=" + totalFlips + " changed=" + changed + " transitions=" + transitions);
    System.out.println("ANCHOR equal-parity tested=" + equalTested + " triggered=" + equalTriggered
        + " flips=" + equalFlips + " changed=" + equalChanged + " transitions=" + equalTransitions);
  }

  public static void main(String[] args) {
    if (args.length == 1 && args[0].equals("sample")) {
      CentresProbe mol = make(3, 14);
      System.out.println("atoms=" + mol.elements);
      for (int[] edge : mol.edges) System.out.println("bond " + Arrays.toString(edge));
      for (int[] frame : mol.frames) System.out.println("frame " + Arrays.toString(frame));
      System.out.println("regular=" + run(mol, 0) + " noop=" + run(mol, 1));
      trace = true;
      System.out.println("left-only=" + run(mol, 3));
      return;
    }
    if (args.length != 0) throw new IllegalArgumentException("expected no args or sample");
    int cases = 0, tested = 0, changed = 0, triggered = 0;
    Map<String, Integer> transitions = new TreeMap<>();
    Map<Integer, Integer> changesByMode = new TreeMap<>();
    for (int site = 2; site <= 5; site++) {
      int frameCount = make(site, 0).frames.size();
      System.out.println("SITE local=" + site + " frames=" + frameCount
          + " handedFrameCases=" + (1 << frameCount));
      for (int mask = 0; mask < (1 << frameCount); mask++) {
        CentresProbe mol = make(site, mask);
        String baseline = run(mol, 0), control = run(mol, 1);
        if (!baseline.equals(control)) throw new AssertionError("baseline disagreement");
        cases++;
        for (int mode = 2; mode <= 4; mode++) {
          long before = flips;
          String modified = run(mol, mode);
          // OxaziridineRootFrames.lean derives this mask from an admitted
          // 27-atom geometry in the carrier order used by this adapter.
          if (site == 3 && mask == 91) {
            String expected = mode == 2 ? "unassigned" : mode == 3 ? "S" : "R";
            if (!baseline.equals("unassigned") || !modified.equals(expected)
                || flips - before != (mode == 2 ? 2 : 1))
              throw new AssertionError("coordinate witness disagrees with pinned replay");
            System.out.println("COORDINATE mask=91 baseline=" + baseline + " mode=" + mode
                + " result=" + modified + " flips=" + (flips - before));
          }
          tested++;
          if (flips > before) triggered++;
          if (!baseline.equals(modified)) {
            changed++;
            changesByMode.merge(mode, 1, Integer::sum);
            if (mask < 32) System.out.println("CHANGE mode=" + mode + " site=" + site
                + " mask=" + mask + " " + baseline + " -> " + modified
                + " flips=" + (flips - before));
          }
          transitions.merge(baseline + " -> " + modified, 1, Integer::sum);
        }
      }
    }
    if (cases != 416 || tested != 1248 || changed != 64 || triggered != 384 || flips != 512
        || changesByMode.getOrDefault(2, 0) != 0
        || changesByMode.getOrDefault(3, 0) != 32
        || changesByMode.getOrDefault(4, 0) != 32)
      throw new AssertionError("unexpected pinned-core experiment totals");
    System.out.println("cases=" + cases + " tested=" + tested + " changed=" + changed
        + " triggeredCases=" + triggered + " calls=" + calls + " flips=" + flips
        + " changesByMode=" + changesByMode + " transitions=" + transitions
        + " occurrenceFlips=" + occurrenceFlips);
    anchoredControl();
  }
}
