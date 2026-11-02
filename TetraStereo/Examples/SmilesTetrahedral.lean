import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.Examples.SmilesTetrahedralKernelAromatic
import TetraStereo.Examples.SmilesTetrahedralKernelFusedMancude
import TetraStereo.Examples.SmilesTetrahedralKernelCyclic

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace SmilesTetrahedral

open OneCenter

/-!
  Stereochemical assignment from OpenSMILES strings.

  These run the whole path a chemist starts from: parse, materialise implicit hydrogens into their
  OpenSMILES neighbour positions, rank branches by the shared sphere key, and combine the
  written-order parity with the parity of the written-to-priority permutation.

  The absolute sense of the convention is anchored twice, independently:

  * `N[C@@H](C)C(=O)O` is the OpenSMILES specification's own worked example of L-alanine, which is
    (S);
  * `[C@H](F)(Cl)Br` is (S) by direct geometric reasoning — `@` puts F, Cl, Br anticlockwise viewed
    from the bracket hydrogen, so viewed with that hydrogen pointing away Br, Cl, F run
    anticlockwise.

  The amino-acid series is the strongest evidence that the ranking is real rather than
  pattern-matched: L-serine and L-cysteine differ by a single atom, and the descriptor flips from
  (S) to (R) because sulfur outranks the carboxyl carbon.  That is the textbook exception among the
  L-amino acids, and it is reproduced here from constitution alone.

  The OpenSMILES parser is total and kernel-reducible.  These regressions use definitional
  equality, ordinary decision procedures, or explicit structural computation lemmas; none trusts
  the native compiler.  They remain anonymous `example`s, so they add no API surface.
-/

/-- Assignment at one centre, for brevity below. -/
private def at? (input : String) (idx : ℕ) : Option RS :=
  smilesTetrahedralDescriptorAt? input idx

/-- Direct production branch comparison, used to pin the first chemically decisive intermediate. -/
private def branchComparison? (input : String) (center left right : ℕ) : Option Ordering :=
  match parseOpenSMILES input with
  | Except.error _ => none
  | Except.ok mol =>
      let expanded := mol.normalizeUnspecifiedBonds.withExplicitHydrogens
      expanded.compareBranches? (analysisFuel expanded) center left right

/-! ### Hydrogen materialisation -/

/-- Alanine is `C₃H₇NO₂`: six parsed heavy atoms become thirteen once hydrogens are explicit.

The seventh hydrogen is the hydroxyl one, and it is a regression twice over.  The permissive valence
table admits oxygen valences `1`, `2` and `3`, so filling to the first admissible valence left a
bare oxygen; and the bracket parser counted the element letter of `[H]` as a hydrogen-count suffix. -/
example :
    (match parseOpenSMILES "N[C@@H](C)C(=O)O" with
      | Except.ok mol =>
          (mol.normalizeUnspecifiedBonds.withExplicitHydrogens).atomCount = 13
      | Except.error _ => false) = true := by
  rfl

/-- An explicitly written `[H]` is one atom carrying no further hydrogens of its own. -/
example :
    (match parseOpenSMILES "[H]C" with
      | Except.ok mol =>
          (mol.normalizeUnspecifiedBonds.withExplicitHydrogens).atomCount = 5
      | Except.error _ => false) = true := by
  rfl

/-- Bracket atoms never receive implicit hydrogens: absent `H` and explicit `H0` both mean exactly
zero, rather than "fill to normal valence". -/
example :
    (analyzeSmilesReport "[C@](F)(Cl)Br" =
      "atom 0: refused (expected four ligands, found 3)") = true := by
  have h : analyzeSmiles "[C@](F)(Cl)Br" = .ok
      [{ unit := StereoUnit.tetrahedral 0,
         outcome := StereoOutcome.refused (StereoRefusal.wrongLigandCount 3) }] := by rfl
  rw [analyzeSmilesReport, h]
  decide

example :
    (analyzeSmilesReport "[C@H0](F)(Cl)Br" =
      "atom 0: refused (expected four ligands, found 3)") = true := by
  have h : analyzeSmiles "[C@H0](F)(Cl)Br" = .ok
      [{ unit := StereoUnit.tetrahedral 0,
         outcome := StereoOutcome.refused (StereoRefusal.wrongLigandCount 3) }] := by rfl
  rw [analyzeSmilesReport, h]
  decide

/-- The bracket hydrogen sits where OpenSMILES puts it: immediately after the atom the centre was
reached from.  Getting this wrong mirrors every affected descriptor. -/
example :
    (match parseOpenSMILES "N[C@@H](C)C(=O)O" with
      | Except.ok mol =>
          (mol.normalizeUnspecifiedBonds.withExplicitHydrogens).writtenNeighbors 1 = [0, 8, 2, 3]
      | Except.error _ => false) = true := by
  rfl

/-! ### Amino acids -/

/-- L-alanine is (S). -/
example : (at? "N[C@@H](C)C(=O)O" 1 = some RS.S) = true := by decide

/-- D-alanine is (R). -/
example : (at? "N[C@H](C)C(=O)O" 1 = some RS.R) = true := by decide

/-- L-serine is (S). -/
example : (at? "N[C@@H](CO)C(=O)O" 1 = some RS.S) = true := by decide

/-- L-cysteine is (R), not (S): sulfur outranks the carboxyl carbon, so the priorities at the alpha
carbon reorder relative to every other L-amino acid.  Serine and cysteine differ by one atom and
this is the descriptor flipping because of it. -/
example : (at? "N[C@@H](CS)C(=O)O" 1 = some RS.R) = true := by decide

/-- L-valine is (S). -/
example : (at? "N[C@@H](C(C)C)C(=O)O" 1 = some RS.S) = true := by decide

/-- L-leucine is (S). -/
example : (at? "N[C@@H](CC(C)C)C(=O)O" 1 = some RS.S) = true := by decide

/-- L-methionine is (S): the sulfur sits two bonds out, so unlike cysteine it does not outrank the
carboxyl carbon and the usual priority order is restored. -/
example : (at? "N[C@@H](CCSC)C(=O)O" 1 = some RS.S) = true := by decide

/-- L-phenylalanine is (S), with an aromatic side chain. -/
example : (at? "N[C@@H](Cc1ccccc1)C(=O)O" 1 = some RS.S) = true := by decide

/-- L-aspartic acid is (S), with a second carboxyl competing in the side chain. -/
example : (at? "N[C@@H](CC(=O)O)C(=O)O" 1 = some RS.S) = true := by decide

/-- L-proline is (S).  Its centre lies on the ring, so this is the regression for ring-closure
neighbour order: the ring bond has to occupy the slot where its digit was opened, not the slot where
it closed. -/
example : (at? "OC(=O)[C@@H]1CCCN1" 3 = some RS.S) = true := by decide

/-- The ring neighbour sits immediately after the bracket hydrogen, where the digit was written. -/
example :
    (match parseOpenSMILES "OC(=O)[C@@H]1CCCN1" with
      | Except.ok mol =>
          (mol.normalizeUnspecifiedBonds.withExplicitHydrogens).writtenNeighbors 3 = [1, 9, 7, 4]
      | Except.error _ => false) = true := by
  rfl

/-- L-threonine is (2S,3R), and both centres are assigned from one string. -/
example :
    (at? "C[C@@H](O)[C@H](N)C(=O)O" 3 = some RS.S) = true := by decide

example :
    (at? "C[C@@H](O)[C@H](N)C(=O)O" 1 = some RS.R) = true := by decide

/-! ### Molecular formulas

Hydrogen filling must respect aromaticity: an aromatic ring atom fills to the aromatic valence, and
a two-connected aromatic heteroatom is the pyridine/furan type carrying no hydrogen. -/

example :
    (match parseOpenSMILES "c1ccccc1" with
      | Except.ok mol => (mol.normalizeUnspecifiedBonds.withExplicitHydrogens).atomCount = 12
      | Except.error _ => false) = true := by
  rfl

example :
    (match parseOpenSMILES "c1ccncc1" with
      | Except.ok mol => (mol.normalizeUnspecifiedBonds.withExplicitHydrogens).atomCount = 11
      | Except.error _ => false) = true := by
  rfl

example :
    (match parseOpenSMILES "c1cc[nH]c1" with
      | Except.ok mol => (mol.normalizeUnspecifiedBonds.withExplicitHydrogens).atomCount = 10
      | Except.error _ => false) = true := by
  rfl

/-! ### Bromochlorofluoromethane

The library's flagship geometric example, now reached from a string rather than a hand-built
realization. -/

example : (at? "[C@H](F)(Cl)Br" 0 = some RS.S) = true := by decide

example : (at? "[C@@H](F)(Cl)Br" 0 = some RS.R) = true := by decide

/-- Writing fluorine first moves the bracket hydrogen one place, a single transposition, so the
descriptor flips. -/
example : (at? "F[C@@H](Cl)Br" 1 = some RS.S) = true := by decide

example : (at? "F[C@H](Cl)Br" 1 = some RS.R) = true := by decide

/-! ### Other centres -/

/-- Ethyl outranks methyl at the second sphere. -/
example : (at? "N[C@@H](C)CC" 1 = some RS.S) = true := by decide

/-- D-glyceraldehyde is (R). -/
example : (at? "OC[C@@H](O)C=O" 2 = some RS.R) = true := by decide

example : (at? "OC[C@H](O)C=O" 2 = some RS.S) = true := by decide

/-- Ring closures are cut on revisit, so a cyclic substituent terminates. -/
example : (at? "C[C@H]1CCCCO1" 1 = some RS.S) = true := by decide

/- An aromatic substituent does not prevent assignment; the two parities give opposite answers.
The exact regression is kernel checked by `SmilesTetrahedralKernelProof.aromatic_parities_opposite`. -/

/-! ### Refusals

Each of these is withheld with a reason rather than guessed. -/

/-- Two identical methyls: not stereogenic. -/
example :
    (RawMolecule.tetrahedralOutcome
      (match parseOpenSMILES "C[C@@H](C)N" with
        | Except.ok mol => mol.normalizeUnspecifiedBonds.withExplicitHydrogens
        | Except.error _ => { atoms := [], bonds := [] }) 40 1 =
      StereoOutcome.refused StereoRefusal.notStereogenic) = true := by
  decide

/-- No parity was written. -/
example : (at? "CC(N)C(=O)O" 1 = none) = true := by decide

/-- The two methyls differ only by isotope, which Rule 2 now separates. -/
example : (at? "C[C@@H]([13CH3])N" 1 = some RS.S) = true := by
  decide

/-- Revised Rule 2 uses standard atomic weight for an unlabelled atom.  Natural carbon therefore
outranks `[12C]` but is outranked by `[13C]`. -/
example : (at? "[C@H](F)(C)[12CH3]" 0 = some RS.R) = true := by decide

example : (at? "[C@H](F)(C)[13CH3]" 0 = some RS.S) = true := by decide

/-- Silicon and germanium are consumed as complete element tokens and participate in Rule 1a. -/
example :
    (at? "[SiH3][C@]([GeH3])(OC)SC" 1 = some RS.R) = true := by
  decide

/-- A bracketed silicon centre is parsed as silicon, not as sulfur with an ignored `i`. -/
example :
    (match parseOpenSMILES "[Si@H](F)(Cl)Br" with
      | Except.ok mol => (mol.atomAt? 0).map (fun atom => atom.element) = some Element.Si
      | Except.error _ => false) = true := by
  rfl

/-- Unsupported two-letter element tokens cannot be accepted through a supported one-letter
prefix. -/
example :
    (match parseOpenSMILES "[Sc@H](F)(Cl)Br" with
      | Except.error _ => true
      | Except.ok _ => false) = true := by
  rfl

/-- Monoisotopic iodine has the same Rule-2 mass whether or not `127` is written explicitly. -/
example :
    (analyzeSmilesReport "[C@H](Cl)(I)[127I]" =
      "atom 0: refused (unresolved: pending descriptor-dependent rules)") = true := by
  have h : analyzeSmiles "[C@H](Cl)(I)[127I]" = .ok
      [{ unit := StereoUnit.tetrahedral 0,
         outcome := StereoOutcome.refused StereoRefusal.notStereogenic }] := by rfl
  rw [analyzeSmilesReport, h]
  decide

/-- Equal sphere multisets can still be separated by parent/child connectivity.  The canonical
hierarchical digraph retains that connectivity and assigns the annotated centre.  The same public
pass also perceives the two unannotated constitutionally stereogenic centers. -/
example :
    (analyzeSmilesReport "[C@H](F)(C(OC)C)C(O)CC" =
      "atom 0: R\natom 2: refused (no stereochemistry written)\n" ++
        "atom 6: refused (no stereochemistry written)") = true := by
  decide

/-- A ring revisit is represented as a duplicate leaf, not merely stopped during the next
expansion step. -/
example :
    (match parseOpenSMILES "C1CC1" with
      | Except.error _ => false
      | Except.ok mol =>
          let node : RawMolecule.BranchNode :=
            { atom := 2, parent := 1, visited := [1, 0], duplicate := false, rootDistance := 1 }
          match mol.normalizeUnspecifiedBonds.branchChildrenOnPath node with
          | [child] => child.atom == 0 && child.duplicate
          | _ => false) = true := by
  rfl

/-- Exhausting the paired comparator's width budget is unresolved, never a tie. -/
example :
    (match parseOpenSMILES "C[C@@H](C)N" with
      | Except.error _ => false
      | Except.ok mol =>
          let expanded := mol.normalizeUnspecifiedBonds.withExplicitHydrogens
          let node : ℕ → RawMolecule.BranchNode := fun atom =>
            { atom := atom, parent := 1, visited := [1], duplicate := false, rootDistance := 0 }
          expanded.comparePairedLevels 3 0 9 [(node 0, node 2)] = none) = true := by
  rfl

/-! ### Canonical hierarchical-digraph regressions -/

/-- The sulfinate convention treats the trigonal-pyramidal `S=O` root edge as single; neutral and
charge-separated representations therefore agree. -/
example : (at? "C[S@@](OC)=O" 1 = some RS.R) = true := by decide

example : (at? "C[S+@@](OC)[O-]" 1 = some RS.R) = true := by decide

example :
    (branchComparison? "[O-][N+](C=1C=CC(=CC1)[S@@](OCC)=O)=O" 8 9 12 =
      some Ordering.gt) = true := by
  decide

/-- Equivalent pyridine Kekulé forms receive the same exact averaged Rule-1a label. -/
example : (at? "O[C@H](/C=N\\C)C1=NC=CC=C1" 1 = some RS.S) = true := by decide

example : (at? "O[C@H](/C=N\\C)C=1N=CC=CC1" 1 = some RS.S) = true := by decide

example :
    (branchComparison? "O[C@H](/C=N\\C)C1=NC=CC=C1" 1 2 5 = some Ordering.gt) =
      true := by
  decide

example :
    (match parseOpenSMILES "O[C@H](/C=N\\C)C1=NC=CC=C1" with
      | Except.error _ => false
      | Except.ok mol =>
          let node : RawMolecule.CanonicalBranchNode :=
            { atom := 6, parent := 5, history := [6, 5, 1],
              provenance := RawMolecule.CanonicalNodeProvenance.multipleBondDuplicate 2 }
          mol.normalizeUnspecifiedBonds.canonicalRule1aLabel node =
            { numerator := 13, denominator := 2 }) = true := by
  rfl

/-- An odd mancude ring averages over every maximum-match Kekulé form, including the one in which
the inspected atom is unmatched and contributes the electron-pair value zero. -/
example :
    (match parseOpenSMILES "[CH-]1C=CC=C1" with
      | Except.error _ => false
      | Except.ok mol =>
          mol.normalizeUnspecifiedBonds.mancudeRule1aLabel? 1 2 =
            some { numerator := 24, denominator := 5 }) = true := by
  rfl

/-- Naphthalene has three maximum-match Kekulé forms; the bounded fused-system engine enumerates all
three rather than selecting the written localization. -/
example :
    (match parseOpenSMILES "C1=CC2=CC=CC=C2C=C1" with
      | Except.error _ => false
      | Except.ok mol =>
          mol.normalizeUnspecifiedBonds.generalMancudeRule1aLabel? 0 1 =
            some { numerator := 18, denominator := 3 }) = true := by
  rfl

/-- A written double bond excluded from the localized mancude graph is an ordinary multiple bond:
an alternating path that crosses a saturated stereocentre must not turn its duplicate into a
mancude average. -/
example :
    (match parseOpenSMILES "C1=CC2=C(C13N=CCO3)C=CC=C2" with
      | Except.error _ => false
      | Except.ok mol =>
          let normalized := mol.normalizeUnspecifiedBonds
          !RawMolecule.containsUndirectedEdge normalized.localizedMancudeEdges 0 1 &&
            normalized.mancudeRule1aLabel? 0 1 ==
              some { numerator := 6, denominator := 1 }) = true := by
  rfl

/- The fused mancude assignment is kernel checked separately by
`SmilesTetrahedralKernelProof.fused_mancude_assignment`. -/

/-- A truncated Rule-1a tie may not fall through to a visible Rule-1b difference. -/
example :
    let atom : RawMolecule.CIPAtomicLabel := { numerator := 6, denominator := 1 }
    let left : RawMolecule.CanonicalBranchKey :=
      { rule1a := [[([], atom)]], rule1b := [[([], 2)]], rule2 := [[([], 12)]],
        realAtoms := [[]], sourceNodes := [[]],
        complete := false }
    let right : RawMolecule.CanonicalBranchKey :=
      { rule1a := [[([], atom)]], rule1b := [[([], 4)]], rule2 := [[([], 13)]],
        realAtoms := [[]], sourceNodes := [[]],
        complete := false }
    RawMolecule.compareCanonicalBranchKeys? left right = none := by
  rfl

/-- Revised Rule 1b assigns every node a root distance.  A real ligand root is in sphere one, while
a multiple-bond duplicate uses the sphere of the atom to which it is attached. -/
example :
    let root := RawMolecule.canonicalRoot 99 0
    root.rule1bRootDistance = 1 := by
  rfl

example :
    (match parseOpenSMILES "C=O" with
      | Except.error _ => false
      | Except.ok mol =>
          let root := RawMolecule.canonicalRoot 99 0
          (mol.normalizeUnspecifiedBonds.canonicalChildren root).any fun node =>
            node.provenance =
              RawMolecule.CanonicalNodeProvenance.multipleBondDuplicate 1) = true := by
  rfl

/- A checked constitutional automorphism suppresses uppercase assignments for identical or
enantiomorphic cyclic ligands; the exact refusal is kernel checked by
`SmilesTetrahedralKernelProof.cyclic_automorphism_refusal`. -/

/-- P-92.3 gives `³H > ²H > ¹H (or H)`: explicit protium ties the implicit hydrogen, so this end is
not stereogenic. -/
example : (analyzeSmilesReport "[1H]/C=C/Br" = "no stereogenic units found") = true := by
  decide

example : (analyzeSmilesReport "[2H]/C=C/Br" = "bond 1=2: E") = true := by
  decide

/-- A syntactically writable but physically absent nuclide cannot fall back to its integer mass
number and influence an emitted descriptor. -/
example :
    (match analyzeSmiles "[999C@](F)(Cl)(Br)I" with
      | Except.error message =>
          message == "unsupported element or isotope: no frozen IUPAC Rule-2 mass datum"
      | Except.ok _ => false) = true := by
  decide

/-- Parent-ranked spheres ignore iodine in a lower branch once chlorine versus fluorine has decided
the corresponding higher branch (Hanson–Mayfield VS115). -/
example :
    (at? "FC[C@H]([C@@H]([C@H]([C@@H]([C@H](CCl)F)CCBr)O)CCI)F" 4 = some RS.R) =
      true := by
  decide

example :
    (branchComparison? "FC[C@H]([C@@H]([C@H]([C@@H]([C@H](CCl)F)CCBr)O)CCI)F"
      4 3 5 = some Ordering.lt) = true := by
  decide

/-- Ring and multiple-bond duplicate provenance resolves both centres of VS172. -/
example : (at? "C1[C@H]2CC=C[C@@H]12" 1 = some RS.R) = true := by decide

example : (at? "C1[C@H]2CC=C[C@@H]12" 5 = some RS.S) = true := by decide

/-- Parent ranking and Rule-1b root distance resolve both centres of VS174. -/
example : (at? "C1CCC=C[C@H]2[C@H]1CCC2" 5 = some RS.R) = true := by decide

example : (at? "C1CCC=C[C@H]2[C@H]1CCC2" 6 = some RS.R) = true := by decide

example :
    (branchComparison? "C1CCC=C[C@H]2[C@H]1CCC2" 5 4 6 = some Ordering.gt &&
      branchComparison? "C1CCC=C[C@H]2[C@H]1CCC2" 6 7 0 = some Ordering.gt) = true := by
  decide

/-! ### Shallow circular occurrence ambiguity -/

/-- Target atom 6 occurs through the two equal ring arms from ligand 1, while target atom 4 is a
farther unique occurrence on the acyclic arm. -/
private def ambiguousNearestProbeMolecule : RawMolecule :=
  match parseOpenSMILES "CC1(CCC)CCC1" with
  | .ok mol => mol
  | .error _ => { atoms := [], bonds := [] }

example :
    nearestShallowRealOccurrenceSearch? ambiguousNearestProbeMolecule 6
      (ambiguousNearestProbeMolecule.atomCount + 1) 5000
      [RawMolecule.canonicalRoot 0 1] ==
        some (ShallowRealOccurrenceSearch.ambiguous 3) := by
  rfl

/-- A nearer ambiguous carrier must cause refusal instead of disappearing while the farther unique
target is selected. -/
example :
    (nearestShallowCircularOccurrence? ambiguousNearestProbeMolecule [0, 6, 4]
      (ambiguousNearestProbeMolecule.atomCount + 1) 0 1).isNone := by
  rfl

/-! ### Molecule-level analysis -/

/-- One call reports every stereogenic unit of a molecule carrying both kinds. -/
example :
    (analyzeSmilesReport "C/C=C/[C@@H](N)C(=O)O" = "atom 3: R\nbond 1=2: E") = true := by
  decide

/-- Non-stereogenic double bonds are not reported at all: a carbonyl oxygen bears no substituents,
so listing it as a refusal would bury the real results. -/
example :
    (analyzeSmilesReport "N[C@@H](C)C(=O)O" = "atom 1: S") = true := by
  decide

end SmilesTetrahedral
end Examples
end TetraStereo
