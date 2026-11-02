import TetraStereo.OneCenter.AuthoritativeCIPGraph
import TetraStereo.OneCenter.AuthoritativeLocalizedCIPAnalysis
import TetraStereo.OneCenter.BranchSphereKey
import TetraStereo.OneCenter.ProductionCIPExactExpansion
import TetraStereo.OneCenter.LocalizedRawGraphReadiness
import TetraStereo.OneCenter.IUPACP92SemanticGraphRepresentationBridge
import TetraStereo.KernelOnly
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace TetraStereo.OneCenter

/-!
# P/S oxido root edge: canonical normalization versus raw localized expansion

This module is a source-level diagnostic for one concrete, chemically valid compact
phosphane-oxide constitution:

* phosphorus `0` is double-bonded to oxygen `1`;
* phosphorus `0` is single-bonded to three explicit hydrogens (`2`, `3`, `4`).

The molecule enters the proof pipeline through the actual parser-side intake
`RawMolecule.toSemanticMolecule?`, the actual raw localized readiness gate
`RawLocalizedGraphSourceReady`, and the actual admission theorem
`localizedCIPGraphReady_of_raw`.  No synthetic key fields or hand-made graph inputs are used.

The point of the diagnostic is a representation correspondence issue, not a claim that either
side has incorrect chemistry:

* `RawMolecule.canonicalBondOrder` (and `RawMolecule.canonicalHierarchyBond`) rewrites the
  distinguished P/S--O root edge from written order `2` to coordination-sphere order `1`.
  Consequently `RawMolecule.canonicalChildCopies` removes the sole parent copy and the oxygen
  root has no child.
* `CertifiedLocalizedCIPInput.moleculeGraph` is the direct raw localized graph
  `SemanticMolecule.toLocalizedMoleculeGraph`, which retains the written order `2`.
  Consequently the executable official expansion generates an extra copy `(P, 1)` at the oxygen
  root, with provenance `OfficialCIPNodeProvenance.multipleBondDuplicate 1`.

The frozen P-9 provisions supporting the canonical side are in the local primary-source snapshot:

* `tmp/chemical-fidelity-20261018/primary-sources/P9.txt`, lines 1916-1919
  (P-93.2.3): the oxygen is treated as the fourth atom and "the nature of the bonding to this
  oxygen atom is not relevant";
* lines 1937-1940 (P-93.2.4): the conventionally written `P=O` bond "is considered as a single
  bond, as there are already four atoms or groups in the tetrahedral configuration";
* lines 1962-1965 (P-93.2.5): sulfates/sulfonates and related compounds are treated like
  phosphates; sulfoxides are handled under P-93.3.3.2;
* lines 2152-2167 (P-93.3.3.2): trigonal-pyramidal centers, including sulfoxides, are treated
  as tetrahedral with a lone pair (phantom atom).

Accordingly, the localized adapter is not wrong as a *constitutional* graph; it is simply not in
the coordination-sphere normal form that the CIP expansion assumes.  The executable bridge rule
stated below is `normalizedOxidoRootBond`, which replaces the raw localized root order by
`semanticP92CanonicalRootBond` before occurrence-sensitive expansion.  The alternative is to
restrict the raw localized adapter so that an eligible P/S oxido root edge cannot occur; the
witness below shows that such a restriction would reject this chemically valid input.
-/

namespace OxidoRootExpansionDiagnostic

open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.LocalizedRawGraphReadiness

/-! ## 1. The compact source constitution and its actual intake -/

/-- Periodic-table atom data used by the semantic source. -/
def phosphorusElement : PeriodicElement := ⟨15, by decide, by decide⟩

def oxygenElement : PeriodicElement := ⟨8, by decide, by decide⟩

def hydrogenElement : PeriodicElement := ⟨1, by decide, by decide⟩

def phosphorusAtom : SemanticAtom := { element := phosphorusElement }

def oxygenAtom : SemanticAtom := { element := oxygenElement }

def hydrogenAtom : SemanticAtom := { element := hydrogenElement }

/-- The compact phosphane-oxide source: `P(=O)(H)(H)(H)`, atom `0` = P, atom `1` = O. -/
def phosphaneOxide : RawMolecule where
  atoms :=
    [ { element := .P }, { element := .O },
      { element := .H }, { element := .H }, { element := .H } ]
  bonds :=
    [ { source := 0, target := 1, kind := .double },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single },
      { source := 0, target := 4, kind := .single } ]

/-- The exact semantic molecule obtained from `phosphaneOxide` by checked parser intake. -/
def phosphaneOxideSemantic : SemanticMolecule where
  atoms := [phosphorusAtom, oxygenAtom, hydrogenAtom, hydrogenAtom, hydrogenAtom]
  interactions :=
    [ { participants := [0, 1], kind := .covalent 2 },
      { participants := [0, 2], kind := .covalent 1 },
      { participants := [0, 3], kind := .covalent 1 },
      { participants := [0, 4], kind := .covalent 1 } ]

/-- Actual successful source intake: the parser conversion, not a synthetic key assignment. -/
theorem phosphaneOxide_toSemanticMolecule :
    phosphaneOxide.toSemanticMolecule? = some phosphaneOxideSemantic := by
  decide +kernel

/-- Raw endpoint well-formedness of the compact source. -/
theorem phosphaneOxide_wellFormed : phosphaneOxide.WellFormed :=
  (RawMolecule.wellFormed_iff_all_bondEndpointsOK phosphaneOxide).mpr (by decide +kernel)

/-- Raw unordered-edge uniqueness of the compact source. -/
theorem phosphaneOxide_bondRecordsUnique : phosphaneOxide.BondRecordsUnique :=
  (RawMolecule.bondRecordsUnique?_eq_true_iff phosphaneOxide).mp (by decide +kernel)

/-- The raw source is admissible under the parser contract. -/
theorem phosphaneOxide_admissible : phosphaneOxide.Admissible :=
  (RawMolecule.admissible?_eq_true_iff phosphaneOxide).mp (by decide +kernel)

/-- Structural well-formedness of the checked semantic molecule, transported from the raw source. -/
theorem phosphaneOxideSemantic_structurallyWellFormed :
    phosphaneOxideSemantic.StructurallyWellFormed :=
  (phosphaneOxide.toSemanticMolecule?_structurallyWellFormed_iff
    phosphaneOxideSemantic phosphaneOxide_toSemanticMolecule).mpr phosphaneOxide_wellFormed

/-- The actual raw localized readiness gate accepts the compact source. -/
theorem phosphaneOxide_rawLocalizedGraphSourceReady :
    RawLocalizedGraphSourceReady phosphaneOxide :=
  (rawLocalizedGraphSourceReady?_eq_true_iff phosphaneOxide).mp (by decide +kernel)

/-- Actual semantic localized-CIP admission, derived from the raw gate and checked intake. -/
theorem phosphaneOxideSemantic_graphReady :
    phosphaneOxideSemantic.LocalizedCIPGraphReady :=
  localizedCIPGraphReady_of_raw phosphaneOxide phosphaneOxideSemantic
    phosphaneOxide_toSemanticMolecule phosphaneOxide_rawLocalizedGraphSourceReady

/-- The format-neutral authoritative input wrapping the checked semantic molecule. -/
def phosphaneOxideAuthoritative : AuthoritativeChemicalInput where
  molecule := phosphaneOxideSemantic

/-- Structural admission of the authoritative input. -/
theorem phosphaneOxideAuthoritative_structurallyWellFormed :
    phosphaneOxideAuthoritative.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    phosphaneOxideAuthoritative).mp (by decide +kernel)

def phosphaneOxideCertified : CertifiedAuthoritativeChemicalInput where
  input := phosphaneOxideAuthoritative
  structurallyWellFormed := phosphaneOxideAuthoritative_structurallyWellFormed

/-- The actual localized CIP pipeline input used by the executable official expansion. -/
def phosphaneOxideLocalizedInput : CertifiedLocalizedCIPInput where
  certified := phosphaneOxideCertified
  graphReady := by
    change phosphaneOxideSemantic.LocalizedCIPGraphReady
    exact phosphaneOxideSemantic_graphReady

/-! ## 2. Canonical (root-normalized) side -/

def rawCenter : Fin phosphaneOxide.atomCount := ⟨0, by decide⟩

def rawLigand : Fin phosphaneOxide.atomCount := ⟨1, by decide⟩

def sourceCenter : Fin phosphaneOxideAuthoritative.molecule.atomCount := ⟨0, by decide⟩

def sourceLigand : Fin phosphaneOxideAuthoritative.molecule.atomCount := ⟨1, by decide⟩

def semanticCenter : Fin phosphaneOxideSemantic.atomCount := ⟨0, by decide⟩

def semanticLigand : Fin phosphaneOxideSemantic.atomCount := ⟨1, by decide⟩

def localizedCenter : phosphaneOxideLocalizedInput.Atom := ⟨0, by decide⟩

def localizedLigand : phosphaneOxideLocalizedInput.Atom := ⟨1, by decide⟩

def localizedHydrogenA : phosphaneOxideLocalizedInput.Atom := ⟨2, by decide⟩

def localizedHydrogenB : phosphaneOxideLocalizedInput.Atom := ⟨3, by decide⟩

def localizedHydrogenC : phosphaneOxideLocalizedInput.Atom := ⟨4, by decide⟩

/-- The production detector recognizes the distinguished P/S oxido root edge. -/
theorem oxidoRootEdge_detected :
    phosphaneOxide.isTrigonalPyramidalOxidoRootEdge 0 1 = true := by
  decide +kernel

/-- The raw written order of the root edge is two. -/
theorem rawRootBondOrder_two :
    phosphaneOxide.bondOrder 0 1 = 2 := by
  decide +kernel

/-- On the canonical node history `[O, P]`, `canonicalBondOrder` collapses the root edge to one. -/
theorem canonicalRootBondOrder_one :
    phosphaneOxide.canonicalBondOrder (RawMolecule.canonicalRoot 0 1) 0 = 1 := by
  decide +kernel

/-- The canonical oxygen root has no child copies: the real parent copy was the only copy. -/
theorem canonicalRootChildCopies_nil :
    phosphaneOxide.canonicalChildCopies (RawMolecule.canonicalRoot 0 1) = [] := by
  decide +kernel

/-- Consequently the canonical oxygen root has no canonical children. -/
theorem canonicalRootChildren_nil :
    phosphaneOxide.canonicalChildren (RawMolecule.canonicalRoot 0 1) = [] := by
  decide +kernel

/-- The canonical hierarchy bond function also records the coordination-sphere order one. -/
theorem canonicalHierarchyBond_collapsed :
    phosphaneOxide.canonicalHierarchyBond 0 1 0 1 = 1 := by
  decide +kernel

/-- The canonical hierarchy graph's root edge has order one. -/
theorem canonicalHierarchyGraph_bond_collapsed :
    (phosphaneOxide.canonicalHierarchyMoleculeGraph rawCenter rawLigand).bond
        rawCenter rawLigand = 1 := by
  rw [RawMolecule.canonicalHierarchyMoleculeGraph_bond]
  change phosphaneOxide.canonicalHierarchyBond 0 1 0 1 = 1
  exact canonicalHierarchyBond_collapsed

/-! ## 3. Raw localized executable side -/

/-- The raw localized graph retains the written double bond on the root edge. -/
theorem localizedGraph_rootBond_two :
    phosphaneOxideLocalizedInput.moleculeGraph.bond localizedLigand localizedCenter = 2 := by
  decide +kernel

/-! ### Kernel computation of the sorted neighbor lists

`Finset.sort` is `Multiset.sort`, whose body is the well-founded `List.mergeSort` that the kernel
does not unfold.  The executable expansion therefore cannot be evaluated by `decide` while a
`Finset.sort` remains in the term.  The next two declarations replace that sort by an explicit
list once for every atom of the witness, using the sort-free theorem `List.toFinset_sort`; after
that the executable child and neighbor lists are ordinary structural computations. -/

/-- If `l` is a nodup, sorted enumeration of the neighbors of `a`, then `Finset.sort` is `l`. -/
theorem sort_of_toFinset_eq (a : phosphaneOxideLocalizedInput.Atom)
    (l : List phosphaneOxideLocalizedInput.Atom)
    (hset : l.toFinset = phosphaneOxideLocalizedInput.moleculeGraph.neighborFinset a)
    (hnd : l.Nodup) (hpw : l.Pairwise (· ≤ ·)) :
    (phosphaneOxideLocalizedInput.moleculeGraph.neighborFinset a).sort (· ≤ ·) = l := by
  rw [← hset]
  exact (List.toFinset_sort (r := (· ≤ ·)) (l := l) hnd).mpr hpw

/-- The sorted neighbor list of every atom of the witness.  The right-hand side is a `match` on
the atom value, so it rewrites uniformly at every atom occurrence in an executable term. -/
theorem neighborSort_eq (a : phosphaneOxideLocalizedInput.Atom) :
    (phosphaneOxideLocalizedInput.moleculeGraph.neighborFinset a).sort (· ≤ ·) =
      match a.val with
      | 0 => [localizedLigand, localizedHydrogenA, localizedHydrogenB, localizedHydrogenC]
      | 1 => [localizedCenter]
      | 2 => [localizedCenter]
      | 3 => [localizedCenter]
      | 4 => [localizedCenter]
      | _ => [] := by
  fin_cases a
  · exact sort_of_toFinset_eq ⟨0, by decide⟩
      [localizedLigand, localizedHydrogenA, localizedHydrogenB, localizedHydrogenC]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨1, by decide⟩ [localizedCenter]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨2, by decide⟩ [localizedCenter]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨3, by decide⟩ [localizedCenter]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq ⟨4, by decide⟩ [localizedCenter]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)

/-- The oxygen root used for occurrence expansion, with the phosphorus center as parent. -/
def localizedOxidoRoot : OfficialCIPNode phosphaneOxideLocalizedInput.Atom :=
  OfficialCIPNode.rootFromEdge localizedCenter localizedLigand

/-- The executable neighbor copies of oxygen are the two written copies of the P=O edge. -/
theorem localizedNeighborCopies_ligand :
    phosphaneOxideLocalizedInput.executableOfficialNeighborCopies localizedLigand =
      [(localizedCenter, 0), (localizedCenter, 1)] := by
  simp only [executableOfficialNeighborCopies, neighborSort_eq, localizedLigand, localizedCenter]
  decide

/-- Removing the real parent copy `(P, 0)` leaves the extra copy `(P, 1)`. -/
theorem localizedChildCopies_root :
    phosphaneOxideLocalizedInput.executableOfficialChildCopies localizedOxidoRoot =
      [(localizedCenter, 1)] := by
  simp only [executableOfficialChildCopies, executableOfficialNeighborCopies,
    neighborSort_eq, localizedOxidoRoot, OfficialCIPNode.rootFromEdge,
    OfficialCIPNode.parent?, localizedLigand, localizedCenter]
  decide

/-- The executable official child list contains exactly one extra duplicate child. -/
theorem localizedChildren_root :
    phosphaneOxideLocalizedInput.executableOfficialCIPChildren localizedOxidoRoot =
      [localizedOxidoRoot.extend localizedCenter 1] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies,
    executableOfficialNeighborCopies, neighborSort_eq, localizedOxidoRoot,
    OfficialCIPNode.rootFromEdge, OfficialCIPNode.parent?,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    localizedLigand, localizedCenter]
  decide

/-- The extra child is provenance-annotated as a multiple-bond duplicate at root distance one. -/
theorem localizedChildren_provenance :
    (phosphaneOxideLocalizedInput.executableOfficialCIPChildren localizedOxidoRoot).map
        (fun child => child.provenance) =
      [OfficialCIPNodeProvenance.multipleBondDuplicate 1] := by
  rw [localizedChildren_root]
  decide +kernel

/-- The single executable child itself is provenance-annotated as the extra multiple-bond copy. -/
theorem localizedDuplicateChild_provenance :
    (localizedOxidoRoot.extend localizedCenter 1).provenance =
      OfficialCIPNodeProvenance.multipleBondDuplicate 1 := by
  decide +kernel

/-- The extra duplicate child carries the branch history `[P, O, P]`. -/
theorem localizedDuplicateChild_history :
    (localizedOxidoRoot.extend localizedCenter 1).history =
      [localizedCenter, localizedLigand, localizedCenter] := by
  decide +kernel

/-! ## 4. Exact discrepancy statement -/

/-- The precise raw/localized versus canonical duplicate-copy discrepancy.

* Canonical: the oxygen root has no child copies at all.
* Localized: the same root has one child copy, `(P, 1)`, and the executable child is a
  multiple-bond duplicate at root distance one.
-/
theorem oxidoRootExpansionDiscrepancy :
    phosphaneOxide.canonicalChildCopies (RawMolecule.canonicalRoot 0 1) = [] ∧
      phosphaneOxideLocalizedInput.executableOfficialChildCopies localizedOxidoRoot =
        [(localizedCenter, 1)] ∧
      phosphaneOxideLocalizedInput.executableOfficialCIPChildren localizedOxidoRoot =
        [localizedOxidoRoot.extend localizedCenter 1] ∧
      (localizedOxidoRoot.extend localizedCenter 1).provenance =
        OfficialCIPNodeProvenance.multipleBondDuplicate 1 :=
  ⟨canonicalRootChildCopies_nil, localizedChildCopies_root, localizedChildren_root,
    localizedDuplicateChild_provenance⟩

/-- The root bond-order disagreement in one statement. -/
theorem oxidoRootBondOrderDiscrepancy :
    phosphaneOxide.bondOrder 0 1 = 2 ∧
      phosphaneOxide.canonicalBondOrder (RawMolecule.canonicalRoot 0 1) 0 = 1 ∧
      phosphaneOxideLocalizedInput.moleculeGraph.bond localizedLigand localizedCenter = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-! ## 5. The proposed normalized bridge rule -/

/-- Executable proposed bridge rule: normalize the distinguished P/S oxido root edge on the
localized semantic graph before occurrence-sensitive expansion.  This is exactly the independent
P-92 root normalization applied to the localized graph. -/
def normalizedOxidoRootBond (source : AuthoritativeChemicalInput)
    (center ligand : Fin source.molecule.atomCount) : ℕ :=
  IUPACNormativeProvision.semanticP92CanonicalRootBond
    source.molecule.toLocalizedMoleculeGraph center ligand center ligand

/-- The normalized root order for the witness is one. -/
theorem normalizedOxidoRootBond_witness :
    normalizedOxidoRootBond phosphaneOxideAuthoritative sourceCenter sourceLigand = 1 := by
  decide +kernel

/-- The graph-native normalized localized graph has root order one, matching the canonical side. -/
theorem normalizedLocalizedGraph_bond_collapsed :
    (IUPACNormativeProvision.p92CanonicalLocalizedMoleculeGraph
      phosphaneOxideAuthoritative sourceCenter sourceLigand).bond
        sourceCenter sourceLigand = 1 := by
  change normalizedOxidoRootBond phosphaneOxideAuthoritative sourceCenter sourceLigand = 1
  exact normalizedOxidoRootBond_witness

/-- Under the normalized root order, the only generated copy index is zero (the real edge). -/
theorem normalizedRootCopyIndices :
    List.range
        (normalizedOxidoRootBond phosphaneOxideAuthoritative sourceCenter sourceLigand) = [0] := by
  decide +kernel

/-- The canonical hierarchy bond and the normalized localized root bond agree on the witness. -/
theorem canonical_eq_normalizedOxidoRootBond :
    phosphaneOxide.canonicalHierarchyBond 0 1 0 1 =
      normalizedOxidoRootBond phosphaneOxideAuthoritative sourceCenter sourceLigand := by
  calc
    phosphaneOxide.canonicalHierarchyBond 0 1 0 1 = 1 :=
      canonicalHierarchyBond_collapsed
    _ = normalizedOxidoRootBond phosphaneOxideAuthoritative sourceCenter sourceLigand :=
      normalizedOxidoRootBond_witness.symm

/-- The raw localized bond disagrees with the canonical root bond. -/
theorem rawLocalized_disagrees_canonical :
    phosphaneOxideLocalizedInput.moleculeGraph.bond localizedLigand localizedCenter ≠
      phosphaneOxide.canonicalHierarchyBond 0 1 0 1 := by
  rw [localizedGraph_rootBond_two, canonicalHierarchyBond_collapsed]
  decide

/-- The witness has an eligible P/S oxido root edge under the independent P-92 predicate, so the
restrict-the-adapter alternative would have to reject this valid chemical input. -/
theorem witness_hasEligibleOxidoRootEdge :
    IUPACNormativeProvision.P92OxidoRootEligible
      phosphaneOxideSemantic.toLocalizedMoleculeGraph semanticCenter semanticLigand := by
  unfold IUPACNormativeProvision.P92OxidoRootEligible
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-! ### Executable occurrence expansion under the normalized root bond

The proposed rule is only a bridge if the normalized graph actually removes the extra copy in the
same executable builder that produced it on the raw graph.  The following generic runtime
definitions mirror `CertifiedLocalizedCIPInput.executableOfficialNeighborCopies` and
`CertifiedLocalizedCIPInput.executableOfficialCIPChildren` for an arbitrary finite graph, so the
comparison is made by the same algorithm rather than by a separate accounting convention. -/

/-- Executable neighbor copies of `atom` in an arbitrary finite molecular graph. -/
def executableGraphNeighborCopies {n : ℕ} (graph : MoleculeGraph (Fin n)) (atom : Fin n) :
    List (Fin n × ℕ) :=
  (graph.neighborFinset atom).sort (· ≤ ·) |>.flatMap fun neighbor =>
    (List.range (graph.bond atom neighbor)).map fun copyIndex => (neighbor, copyIndex)

/-- Executable child copies with the zero-index parent occurrence removed. -/
def executableGraphChildCopies {n : ℕ} (graph : MoleculeGraph (Fin n))
    (parent current : Fin n) : List (Fin n × ℕ) :=
  (executableGraphNeighborCopies graph current).filter fun copy =>
    !(copy.1 == parent && copy.2 == 0)

/-- Executable child copies of an official digraph node. -/
def executableGraphChildCopiesOfNode {n : ℕ} (graph : MoleculeGraph (Fin n))
    (node : OfficialCIPNode (Fin n)) : List (Fin n × ℕ) :=
  match node.current? with
  | none => []
  | some current =>
      match node.parent? with
      | none => executableGraphNeighborCopies graph current
      | some parent => executableGraphChildCopies graph parent current

/-- Executable official children in an arbitrary finite molecular graph. -/
def executableGraphCIPChildren {n : ℕ} (graph : MoleculeGraph (Fin n))
    (node : OfficialCIPNode (Fin n)) : List (OfficialCIPNode (Fin n)) :=
  if node.isDuplicateLeaf then []
  else
    (executableGraphChildCopiesOfNode graph node).map fun copy =>
      node.extend copy.1 copy.2

/-- If `l` is a nodup, sorted enumeration of the neighbors of `atom`, then `Finset.sort` is `l`. -/
theorem sort_neighborFinset_eq {n : ℕ} (graph : MoleculeGraph (Fin n)) (atom : Fin n)
    (l : List (Fin n)) (hset : l.toFinset = graph.neighborFinset atom)
    (hnd : l.Nodup) (hpw : l.Pairwise (· ≤ ·)) :
    (graph.neighborFinset atom).sort (· ≤ ·) = l := by
  rw [← hset]
  exact (List.toFinset_sort (r := (· ≤ ·)) (l := l) hnd).mpr hpw

/-- The normalized localized graph used by the proposed bridge rule. -/
def normalizedLocalizedGraph :
    MoleculeGraph (Fin phosphaneOxideAuthoritative.molecule.atomCount) :=
  IUPACNormativeProvision.p92CanonicalLocalizedMoleculeGraph
    phosphaneOxideAuthoritative sourceCenter sourceLigand

/-- The oxygen root node of the normalized executable expansion. -/
def normalizedOxidoRoot :
    OfficialCIPNode (Fin phosphaneOxideAuthoritative.molecule.atomCount) :=
  OfficialCIPNode.rootFromEdge sourceCenter sourceLigand

/-- The normalized graph keeps the oxygen--phosphorus root edge positive. -/
theorem normalizedGraph_bond_ligand_center :
    normalizedLocalizedGraph.bond sourceLigand sourceCenter = 1 := by
  decide +kernel

/-- The only normalized neighbor of the oxygen is the phosphorus center. -/
theorem normalizedLigand_neighbor_iff
    (atom : Fin phosphaneOxideAuthoritative.molecule.atomCount) :
    atom ∈ normalizedLocalizedGraph.neighborFinset sourceLigand ↔ atom = sourceCenter := by
  fin_cases atom <;> decide +kernel

/-- Under normalization the sorted neighbor list of oxygen is the single phosphorus atom. -/
theorem normalizedNeighborSort_ligand :
    (normalizedLocalizedGraph.neighborFinset sourceLigand).sort (· ≤ ·) = [sourceCenter] := by
  apply sort_neighborFinset_eq
  · ext atom
    simp only [List.mem_toFinset, List.mem_singleton]
    exact (normalizedLigand_neighbor_iff atom).symm
  · simp
  · simp

/-- The normalized neighbor copies contain only the real edge copy `(P, 0)`. -/
theorem normalizedNeighborCopies_ligand :
    executableGraphNeighborCopies normalizedLocalizedGraph sourceLigand =
      [(sourceCenter, 0)] := by
  simp [executableGraphNeighborCopies, normalizedNeighborSort_ligand,
    normalizedGraph_bond_ligand_center]

/-- Removing the real parent copy leaves no normalized child copies at the oxygen root. -/
theorem normalizedChildCopies_root :
    executableGraphChildCopies normalizedLocalizedGraph sourceCenter sourceLigand = [] := by
  rw [executableGraphChildCopies, normalizedNeighborCopies_ligand]
  decide

/-- The normalized executable expansion gives the oxygen root no children at all. -/
theorem normalizedChildren_root :
    executableGraphCIPChildren normalizedLocalizedGraph normalizedOxidoRoot = [] := by
  simp only [executableGraphCIPChildren, executableGraphChildCopiesOfNode,
    normalizedOxidoRoot, OfficialCIPNode.rootFromEdge, OfficialCIPNode.parent?,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    normalizedChildCopies_root, List.map_nil, Bool.false_eq_true, ↓reduceIte]

/-- **Bridge-rule suppression.**  The proposed normalization reproduces exactly the canonical
root outcome (no oxygen child), while the raw localized generic builder retains the extra
multiple-bond duplicate `(P, 1)`. -/
theorem normalizedSuppression_matches_canonical :
    phosphaneOxide.canonicalChildren (RawMolecule.canonicalRoot 0 1) = [] ∧
      executableGraphCIPChildren normalizedLocalizedGraph normalizedOxidoRoot = [] ∧
      phosphaneOxideLocalizedInput.executableOfficialCIPChildren localizedOxidoRoot =
        [localizedOxidoRoot.extend localizedCenter 1] :=
  ⟨canonicalRootChildren_nil, normalizedChildren_root, localizedChildren_root⟩

/-! ## 6. Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.phosphaneOxide_toSemanticMolecule
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.phosphaneOxide_wellFormed
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.phosphaneOxide_bondRecordsUnique
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.phosphaneOxide_admissible
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.phosphaneOxideSemantic_structurallyWellFormed
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.phosphaneOxide_rawLocalizedGraphSourceReady
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.phosphaneOxideSemantic_graphReady
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.phosphaneOxideAuthoritative_structurallyWellFormed
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.oxidoRootEdge_detected
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.rawRootBondOrder_two
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.canonicalRootBondOrder_one
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.canonicalRootChildCopies_nil
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.canonicalRootChildren_nil
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.canonicalHierarchyBond_collapsed
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.canonicalHierarchyGraph_bond_collapsed
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.localizedGraph_rootBond_two
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.sort_of_toFinset_eq
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.neighborSort_eq
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.localizedNeighborCopies_ligand
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.localizedChildCopies_root
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.localizedChildren_root
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.localizedChildren_provenance
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.localizedDuplicateChild_provenance
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.localizedDuplicateChild_history
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.oxidoRootExpansionDiscrepancy
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.oxidoRootBondOrderDiscrepancy
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.normalizedOxidoRootBond_witness
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.normalizedLocalizedGraph_bond_collapsed
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.normalizedRootCopyIndices
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.canonical_eq_normalizedOxidoRootBond
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.rawLocalized_disagrees_canonical
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.witness_hasEligibleOxidoRootEdge
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.sort_neighborFinset_eq
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.normalizedGraph_bond_ligand_center
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.normalizedLigand_neighbor_iff
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.normalizedNeighborSort_ligand
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.normalizedNeighborCopies_ligand
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.normalizedChildCopies_root
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.normalizedChildren_root
assert_kernel_only TetraStereo.OneCenter.OxidoRootExpansionDiagnostic.normalizedSuppression_matches_canonical

end OxidoRootExpansionDiagnostic

end TetraStereo.OneCenter
