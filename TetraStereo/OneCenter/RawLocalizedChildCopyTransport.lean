import TetraStereo.OneCenter.BranchSphereKey
import TetraStereo.OneCenter.AuthoritativeLocalizedCIPAnalysis
import TetraStereo.OneCenter.LocalizedRawGraphReadiness
import TetraStereo.OneCenter.LocalizedCanonicalRuntimeKeyCorrespondence
import TetraStereo.OneCenter.ProductionCIPRule1aGraphRealization
import TetraStereo.OneCenter.CIPP93TrigonalPyramidalIntegration
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open scoped List

local infixl:50 " ~ " => List.Perm

/-!
# Raw/localized child-copy transport

The raw canonical branch expansion enumerates child copies by walking `RawMolecule.bonds` in
parser order.  The localized executable expansion enumerates the same copies by sorting the
neighbours of the current atom in the localized molecular graph.  This module proves that the two
lists are permutations, preserving the exact copy index, under the source-intake agreement and the
explicit no-oxido-root-edge domain in which `canonicalBondOrder` is the raw bond order.

The proof first transports the seed enumeration (the incident neighbour list and the per-neighbour
`List.range` blocks), then transports the removal of the real parent copy `(parent, 0)`.  No
equality of the two enumerated lists as lists is asserted: their orders genuinely differ.
-/

namespace RawMolecule

/-! ## Endpoint extraction from the raw bond list -/

/-- The opposite endpoint of a bond with respect to `atom`, in source-first orientation. -/
private def otherEndpoint? (atom first second : ℕ) : Option ℕ :=
  if first == atom then some second
  else if second == atom then some first
  else none

/-- The extracted endpoint really is connected to `atom`. -/
private theorem connects_of_otherEndpoint?_eq_some
    (atom first second next : ℕ)
    (h : otherEndpoint? atom first second = some next) :
    ((first == atom && second == next) ||
      (first == next && second == atom)) = true := by
  unfold otherEndpoint? at h
  cases hfirst : (first == atom) with
  | true =>
      have hnext : second = next := by
        simpa [hfirst] using h
      subst hnext
      simp
  | false =>
      cases hsecond : (second == atom) with
      | true =>
          have hnext : first = next := by
            simpa [hfirst, hsecond] using h
          subst hnext
          simp
      | false =>
          simp [hfirst, hsecond] at h

/-- A connected endpoint is exactly the endpoint extracted from the bond. -/
private theorem otherEndpoint?_eq_some_of_connects
    (atom first second next : ℕ)
    (hconnects : ((first == atom && second == next) ||
      (first == next && second == atom)) = true) :
    otherEndpoint? atom first second = some next := by
  unfold otherEndpoint?
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hconnects
  cases hfirst : (first == atom) with
  | true =>
      have hfirstEq : first = atom := by simpa using hfirst
      have htarget : second = next := by
        rcases hconnects with ⟨_, htarget⟩ | ⟨hfirstNext, hsecondAtom⟩
        · exact htarget
        · exact hsecondAtom.trans (hfirstEq.symm.trans hfirstNext)
      subst hfirstEq
      subst htarget
      simp
  | false =>
      have hfirstNe : first ≠ atom := by
        intro equality
        subst equality
        simp at hfirst
      have hsecond : second = atom := by
        rcases hconnects with ⟨hfirstEq, _⟩ | ⟨_, hsecond⟩
        · exact absurd hfirstEq hfirstNe
        · exact hsecond
      have htarget : first = next := by
        rcases hconnects with ⟨hfirstEq, _⟩ | ⟨htarget, _⟩
        · exact absurd hfirstEq hfirstNe
        · exact htarget
      subst hsecond
      subst htarget
      simp

/-- Two unordered pairs with the same `min` and `max` are equal up to orientation. -/
theorem unordered_pair_eq_of_min_max_eq
    (a b c d : ℕ) (hmin : Nat.min a b = Nat.min c d)
    (hmax : Nat.max a b = Nat.max c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases le_total a b with hab | hba
  · have hminA : a = Nat.min c d := by
      simpa [Nat.min_eq_left hab] using hmin
    have hmaxB : b = Nat.max c d := by
      simpa [Nat.max_eq_right hab] using hmax
    rcases le_total c d with hcd | hdc
    · exact Or.inl ⟨hminA.trans (Nat.min_eq_left hcd),
        hmaxB.trans (Nat.max_eq_right hcd)⟩
    · exact Or.inr ⟨hminA.trans (Nat.min_eq_right hdc),
        hmaxB.trans (Nat.max_eq_left hdc)⟩
  · have hminB : b = Nat.min c d := by
      simpa [Nat.min_eq_right hba] using hmin
    have hmaxA : a = Nat.max c d := by
      simpa [Nat.max_eq_left hba] using hmax
    rcases le_total c d with hcd | hdc
    · exact Or.inr ⟨hmaxA.trans (Nat.max_eq_right hcd),
        hminB.trans (Nat.min_eq_left hcd)⟩
    · exact Or.inl ⟨hmaxA.trans (Nat.max_eq_left hdc),
        hminB.trans (Nat.min_eq_right hdc)⟩

/-- The semantic unordered key of a connected pair is the semantic key of the bond endpoints. -/
theorem semanticEdgeKey_eq_of_connects
    (bond : RawBond) {left right : ℕ}
    (hconnects : bond.connects left right = true) :
    semanticEdgeKey left right = semanticEdgeKey bond.source bond.target := by
  simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hconnects
  rcases hconnects with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · rw [← hsource, ← htarget]
  · rw [← htarget, ← hsource]
    simp [semanticEdgeKey, min_comm, max_comm]

/-- A bond whose unordered key is the key of `left,right` connects those two atoms. -/
theorem connects_of_edgeKey_eq
    (bond : RawBond) {left right : ℕ}
    (hkey : bond.edgeKey = semanticEdgeKey left right) :
    bond.connects left right = true := by
  have hmin : Nat.min bond.source bond.target = Nat.min left right := by
    simpa [RawBond.edgeKey, semanticEdgeKey] using congrArg Prod.fst hkey
  have hmax : Nat.max bond.source bond.target = Nat.max left right := by
    simpa [RawBond.edgeKey, semanticEdgeKey] using congrArg Prod.snd hkey
  rcases unordered_pair_eq_of_min_max_eq bond.source bond.target left right hmin hmax with
    ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · simp [RawBond.connects, hsource, htarget]
  · simp [RawBond.connects, hsource, htarget]

/-! ## Raw seed enumeration -/

/-- Incident neighbour atoms, enumerated in the input bond-list order. -/
def canonicalIncidentNeighbors (mol : RawMolecule) (atom : ℕ) : List ℕ :=
  mol.bonds.filterMap fun bond => otherEndpoint? atom bond.source bond.target

/-- Child-copy seeds before removing the real parent copy, in input bond-list order. -/
def canonicalSeedCopies (mol : RawMolecule) (node : CanonicalBranchNode) : List (ℕ × ℕ) :=
  (mol.canonicalIncidentNeighbors node.atom).flatMap fun next =>
    (List.range (mol.canonicalBondOrder node next)).map fun copyIndex => (next, copyIndex)

/-- Membership in the raw incident-neighbour enumeration is exactly positive raw bond order. -/
theorem mem_canonicalIncidentNeighbors_iff
    (mol : RawMolecule) (atom : ℕ) (wellFormed : mol.WellFormed) (other : ℕ) :
    other ∈ mol.canonicalIncidentNeighbors atom ↔ 0 < mol.bondOrder atom other := by
  constructor
  · intro member
    rw [canonicalIncidentNeighbors, List.mem_filterMap] at member
    obtain ⟨bond, hbond, hother⟩ := member
    have connects := connects_of_otherEndpoint?_eq_some atom bond.source bond.target other hother
    have hne : atom ≠ other := by
      intro equality
      subst other
      have connectsSelf := connects
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connectsSelf
      rcases connectsSelf with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
      · exact (wellFormed bond hbond).2.2 (hsource.trans htarget.symm)
      · exact (wellFormed bond hbond).2.2 (hsource.trans htarget.symm)
    exact (RawMolecule.bondOrder_pos_iff_exists_bond mol hne).mpr
      ⟨bond, hbond, connects⟩
  · intro positive
    have hne : atom ≠ other := by
      intro equality
      subst other
      rw [RawMolecule.bondOrder_self] at positive
      exact Nat.lt_irrefl 0 positive
    obtain ⟨bond, hbond, connects⟩ :=
      (RawMolecule.bondOrder_pos_iff_exists_bond mol hne).mp positive
    have hother := otherEndpoint?_eq_some_of_connects atom bond.source bond.target other connects
    rw [canonicalIncidentNeighbors, List.mem_filterMap]
    exact ⟨bond, hbond, hother⟩

/-- Both endpoints of a positive raw bond-order pair are parsed atom indices. -/
theorem bondOrder_pos_endpoint_lt
    (mol : RawMolecule) (wellFormed : mol.WellFormed)
    {left right : ℕ} (positive : 0 < mol.bondOrder left right) :
    left < mol.atomCount ∧ right < mol.atomCount := by
  have hne : left ≠ right := by
    intro equality
    subst right
    rw [RawMolecule.bondOrder_self] at positive
    exact Nat.lt_irrefl 0 positive
  obtain ⟨bond, hbond, connects⟩ :=
    (RawMolecule.bondOrder_pos_iff_exists_bond mol hne).mp positive
  have endpoints := wellFormed bond hbond
  simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connects
  rcases connects with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · constructor
    · rw [← hleft]
      exact endpoints.1
    · rw [← hright]
      exact endpoints.2.1
  · constructor
    · rw [← hright]
      exact endpoints.2.1
    · rw [← hleft]
      exact endpoints.1

/-- The raw incident-neighbour list has no duplicate atom. -/
private theorem canonicalIncidentNeighbors_nodup_of_nodup
    (mol : RawMolecule) (atom : ℕ) (unique : mol.BondRecordsUnique) :
    ∀ bonds : List RawBond, bonds.Nodup →
      (∀ bond ∈ bonds, bond ∈ mol.bonds) →
      (bonds.filterMap fun bond => otherEndpoint? atom bond.source bond.target).Nodup := by
  intro bonds
  induction bonds with
  | nil =>
      intro _ _
      simp
  | cons bond rest inductionHypothesis =>
      intro hnodup hsubset
      have hbond : bond ∈ mol.bonds := hsubset bond (by simp)
      have hfresh : bond ∉ rest := (List.nodup_cons.mp hnodup).1
      have hrestNodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have hrestSubset : ∀ item ∈ rest, item ∈ mol.bonds := by
        intro item hitem
        exact hsubset item (by simp [hitem])
      cases hstep : otherEndpoint? atom bond.source bond.target with
      | none =>
          rw [List.filterMap_cons_none (f := fun item =>
            otherEndpoint? atom item.source item.target) (a := bond) (l := rest) hstep]
          exact inductionHypothesis hrestNodup hrestSubset
      | some next =>
          rw [List.filterMap_cons_some (f := fun item =>
            otherEndpoint? atom item.source item.target) (a := bond) (l := rest) (b := next) hstep]
          rw [List.nodup_cons]
          constructor
          · intro hmem
            rw [List.mem_filterMap] at hmem
            obtain ⟨otherBond, hotherBond, hotherEndpoint⟩ := hmem
            have hbondConnects := connects_of_otherEndpoint?_eq_some atom bond.source
              bond.target next hstep
            have hotherConnects := connects_of_otherEndpoint?_eq_some atom otherBond.source
              otherBond.target next hotherEndpoint
            have hbondsEq : bond = otherBond :=
              RawMolecule.bond_eq_of_mem_of_connects mol unique hbond
                (hrestSubset otherBond hotherBond) hbondConnects hotherConnects
            subst otherBond
            exact hfresh hotherBond
          · exact inductionHypothesis hrestNodup hrestSubset

theorem canonicalIncidentNeighbors_nodup
    (mol : RawMolecule) (atom : ℕ) (unique : mol.BondRecordsUnique) :
    (mol.canonicalIncidentNeighbors atom).Nodup := by
  unfold canonicalIncidentNeighbors
  exact canonicalIncidentNeighbors_nodup_of_nodup mol atom unique mol.bonds
    (List.Nodup.of_map RawBond.edgeKey unique) (fun _ hbond => hbond)

/-- The seed enumeration has no duplicate `(atom, copy index)` pair. -/
theorem canonicalSeedCopies_nodup
    (mol : RawMolecule) (node : CanonicalBranchNode)
    (unique : mol.BondRecordsUnique) :
    (mol.canonicalSeedCopies node).Nodup := by
  unfold canonicalSeedCopies
  rw [List.nodup_flatMap]
  constructor
  · intro next _
    exact List.Nodup.map (by
      intro left right equality
      exact Prod.mk.inj equality |>.2) List.nodup_range
  · have neighborsNodup := canonicalIncidentNeighbors_nodup mol node.atom unique
    rw [List.nodup_iff_pairwise_ne] at neighborsNodup
    apply neighborsNodup.imp
    intro left right different
    rw [Function.onFun, List.disjoint_left]
    intro copy leftPresent rightPresent
    rw [List.mem_map] at leftPresent rightPresent
    rcases leftPresent with ⟨leftIndex, _leftIndexPresent, leftIdentity⟩
    rcases rightPresent with ⟨rightIndex, _rightIndexPresent, rightIdentity⟩
    subst copy
    exact different (Prod.mk.inj rightIdentity |>.1.symm)

/-- Exact membership characterization of the raw seed enumeration. -/
theorem mem_canonicalSeedCopies_iff
    (mol : RawMolecule) (node : CanonicalBranchNode)
    (wellFormed : mol.WellFormed) (next copyIndex : ℕ) :
    (next, copyIndex) ∈ mol.canonicalSeedCopies node ↔
      0 < mol.bondOrder node.atom next ∧
        copyIndex < mol.canonicalBondOrder node next := by
  rw [canonicalSeedCopies, List.mem_flatMap]
  constructor
  · rintro ⟨other, hother, hmember⟩
    rw [List.mem_map] at hmember
    obtain ⟨index, hindex, hpair⟩ := hmember
    have hotherEq : other = next := (Prod.mk.inj hpair).1
    have hindexEq : index = copyIndex := (Prod.mk.inj hpair).2
    subst other
    subst index
    exact ⟨(mem_canonicalIncidentNeighbors_iff mol node.atom wellFormed next).mp hother,
      by simpa using hindex⟩
  · rintro ⟨positive, bound⟩
    refine ⟨next,
      (mem_canonicalIncidentNeighbors_iff mol node.atom wellFormed next).mpr positive, ?_⟩
    rw [List.mem_map]
    exact ⟨copyIndex, by simpa using bound, rfl⟩

/-! ## Relating the raw child enumeration to the seed enumeration -/

/-- Pulling a `match` on an option through a `filterMap` and `flatMap`. -/
private theorem flatMap_match_option_eq_filterMap_flatMap
    (bonds : List RawBond) (other : RawBond → Option ℕ)
    (block : ℕ → List (ℕ × ℕ)) :
    bonds.flatMap (fun bond =>
        match other bond with
        | none => []
        | some next => block next) =
      (bonds.filterMap other).flatMap block := by
  induction bonds with
  | nil => rfl
  | cons bond rest inductionHypothesis =>
      cases h : other bond with
      | none => simp [h, inductionHypothesis]
      | some next => simp [h, inductionHypothesis]

theorem canonicalChildCopies_eq_erase_seed
    (mol : RawMolecule) (node : CanonicalBranchNode) :
    mol.canonicalChildCopies node =
      eraseCanonicalParentCopy node.parent (mol.canonicalSeedCopies node) := by
  unfold canonicalChildCopies canonicalSeedCopies canonicalIncidentNeighbors
  exact congrArg (eraseCanonicalParentCopy node.parent)
    (flatMap_match_option_eq_filterMap_flatMap mol.bonds
      (fun bond => otherEndpoint? node.atom bond.source bond.target)
      (fun next => (List.range (mol.canonicalBondOrder node next)).map
        fun copyIndex => (next, copyIndex)))

theorem eraseCanonicalParentCopy_eq_filter_of_nodup
    (parent : ℕ) (copies : List (ℕ × ℕ)) (nodup : copies.Nodup) :
    eraseCanonicalParentCopy parent copies =
      copies.filter (fun copy => !(copy.1 == parent && copy.2 == 0)) := by
  rw [RawMolecule.eraseCanonicalParentCopy_eq_erase parent copies,
    nodup.erase_eq_filter (parent, 0)]
  apply List.filter_congr
  rintro ⟨first, second⟩ _
  rfl

/-- The raw child enumeration is the seed enumeration with the real parent copy removed. -/
theorem canonicalChildCopies_eq_filter_seed
    (mol : RawMolecule) (node : CanonicalBranchNode)
    (unique : mol.BondRecordsUnique) :
    mol.canonicalChildCopies node =
      (mol.canonicalSeedCopies node).filter
        (fun copy => !(copy.1 == node.parent && copy.2 == 0)) := by
  rw [canonicalChildCopies_eq_erase_seed]
  exact eraseCanonicalParentCopy_eq_filter_of_nodup node.parent
    (mol.canonicalSeedCopies node) (canonicalSeedCopies_nodup mol node unique)

end RawMolecule

namespace CertifiedLocalizedCIPInput

/-- Neighbour atoms of a localized graph atom, in sorted executable order. -/
def sortedNeighborAtoms (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    List input.Atom :=
  (input.moleculeGraph.neighborFinset atom).sort (· ≤ ·)

/-- Seed child copies in sorted localized order, before removing the real parent copy. -/
def executableSeedCopies (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    List (input.Atom × ℕ) :=
  (input.sortedNeighborAtoms atom).flatMap fun neighbor =>
    (List.range (input.moleculeGraph.bond atom neighbor)).map fun copyIndex =>
      (neighbor, copyIndex)

theorem executableOfficialNeighborCopies_eq_seed
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    input.executableOfficialNeighborCopies atom = input.executableSeedCopies atom := rfl

theorem executableOfficialChildCopies_eq_filter_seed
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    (current parent : input.Atom)
    (currentObserved : node.current? = some current)
    (parentObserved : node.parent? = some parent) :
    input.executableOfficialChildCopies node =
      (input.executableSeedCopies current).filter
        (fun copy => !(copy.1 == parent && copy.2 == 0)) := by
  simp only [executableOfficialChildCopies, executableSeedCopies, sortedNeighborAtoms,
    executableOfficialNeighborCopies, currentObserved, parentObserved]

theorem sortedNeighborAtoms_nodup
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    (input.sortedNeighborAtoms atom).Nodup := by
  unfold sortedNeighborAtoms
  exact Finset.sort_nodup (input.moleculeGraph.neighborFinset atom) (· ≤ ·)

theorem mem_sortedNeighborAtoms_iff
    (input : CertifiedLocalizedCIPInput) (atom neighbor : input.Atom) :
    neighbor ∈ input.sortedNeighborAtoms atom ↔
      0 < input.moleculeGraph.bond atom neighbor := by
  simp [sortedNeighborAtoms, MoleculeGraph.Adj]

end CertifiedLocalizedCIPInput

/-! ## The explicit no-oxido-root-edge domain -/

/-- The canonical oxido exception does not fire anywhere along this node's recorded history. -/
def NoOxidoRootEdgeHistory (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode) : Prop :=
  ∀ current center : ℕ,
    node.history = [current, center] →
      ¬ BlueBookP93.TrigonalPyramidal.OxidoRootEdge mol center current

/-- Outside the explicit oxido root edge, the canonical child bond order is the raw bond order. -/
theorem canonicalBondOrder_eq_bondOrder_of_noOxidoRootEdge
    (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (noOxido : NoOxidoRootEdgeHistory mol node) (next : ℕ) :
    mol.canonicalBondOrder node next = mol.bondOrder node.atom next := by
  cases observed : node.history with
  | nil =>
      simp [RawMolecule.canonicalBondOrder, observed]
  | cons current rest =>
      cases rest with
      | nil =>
          simp [RawMolecule.canonicalBondOrder, observed]
      | cons center tail =>
          cases tail with
          | nil =>
              have noEdge :
                  ¬ BlueBookP93.TrigonalPyramidal.OxidoRootEdge mol center current :=
                noOxido current center observed
              have detector :
                  mol.isTrigonalPyramidalOxidoRootEdge center current = false := by
                cases detected : mol.isTrigonalPyramidalOxidoRootEdge center current with
                | false => rfl
                | true =>
                    exact False.elim (noEdge
                      ((BlueBookP93.TrigonalPyramidal.isTrigonalPyramidalOxidoRootEdge_eq_true_iff
                        mol center current).mp detected))
              simp [RawMolecule.canonicalBondOrder, observed, detector]
          | cons extra tail₂ =>
              simp [RawMolecule.canonicalBondOrder, observed]

/-! ## Transport of localized bond orders -/

/-- The localized order of a supported raw spelling is the raw graph order of that spelling. -/
theorem localizedBondOrder?_eq_some_order_of_isLocalizedCovalent
    (bond : RawBond) (supported : bond.kind.IsLocalizedCovalent) :
    bond.kind.localizedBondOrder? = some bond.kind.order := by
  rcases supported with ⟨order, horder⟩
  cases kindObserved : bond.kind with
  | unspecified =>
      rw [kindObserved] at horder
      cases horder
  | single =>
      simp [ParsedBondKind.localizedBondOrder?, ParsedBondKind.order]
  | double =>
      simp [ParsedBondKind.localizedBondOrder?, ParsedBondKind.order]
  | triple =>
      simp [ParsedBondKind.localizedBondOrder?, ParsedBondKind.order]
  | aromatic =>
      rw [kindObserved] at horder
      cases horder
  | up =>
      simp [ParsedBondKind.localizedBondOrder?, ParsedBondKind.order]
  | down =>
      simp [ParsedBondKind.localizedBondOrder?, ParsedBondKind.order]

/-- A supported raw bond contributes its explicit semantic localized record. -/
theorem localizedCovalentRecord_mem_of_rawBond
    (mol : RawMolecule) (semantic : SemanticMolecule)
    (converted : mol.toSemanticMolecule? = some semantic)
    {bond : RawBond} (hbond : bond ∈ mol.bonds)
    (supported : bond.kind.IsLocalizedCovalent) :
    (semanticEdgeKey bond.source bond.target, bond.kind.order) ∈
      semantic.localizedCovalentRecords := by
  unfold SemanticMolecule.localizedCovalentRecords
  rw [RawMolecule.toSemanticMolecule?_interactions mol semantic converted]
  rw [List.mem_filterMap]
  refine ⟨bond.toSemanticInteraction, ?_, ?_⟩
  · rw [List.mem_map]
    exact ⟨bond, hbond, rfl⟩
  · rw [SemanticInteraction.localizedCovalentRecord?_toSemanticInteraction,
      localizedBondOrder?_eq_some_order_of_isLocalizedCovalent bond supported]
    simp [RawBond.edgeKey, semanticEdgeKey]

/-- Under intake agreement, the localized bond order at a distinct pair is the raw bond order. -/
theorem localizedBondOrder_eq_rawBondOrder_of_agreement
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    {left right : ℕ} (hne : left ≠ right) :
    input.certified.input.molecule.localizedBondOrder left right =
      mol.bondOrder left right := by
  by_cases positive : 0 < mol.bondOrder left right
  · obtain ⟨bond, hbond, connects⟩ :=
      (RawMolecule.bondOrder_pos_iff_exists_bond mol hne).mp positive
    have orderEq : mol.bondOrder left right = bond.kind.order :=
      RawMolecule.bondOrder_eq_kind_of_mem_connects mol wellFormed unique hbond connects
    have recordPresent :
        (semanticEdgeKey bond.source bond.target, bond.kind.order) ∈
          input.certified.input.molecule.localizedCovalentRecords :=
      localizedCovalentRecord_mem_of_rawBond mol input.certified.input.molecule
        agreement.1 hbond (supported bond hbond)
    have edgeEq : semanticEdgeKey left right =
        semanticEdgeKey bond.source bond.target :=
      RawMolecule.semanticEdgeKey_eq_of_connects bond connects
    have present' :
        (semanticEdgeKey left right, bond.kind.order) ∈
          input.certified.input.molecule.localizedCovalentRecords := by
      rw [edgeEq]
      exact recordPresent
    rw [orderEq]
    exact SemanticMolecule.localizedBondOrder_eq_of_record
      input.certified.input.molecule left right bond.kind.order input.graphReady hne present'
  · have zero : mol.bondOrder left right = 0 := Nat.eq_zero_of_not_pos positive
    have absent : semanticEdgeKey left right ∉
        input.certified.input.molecule.localizedCovalentKeys := by
      intro member
      have keysEq := LocalizedRawGraphReadiness.localizedCovalentKeys_eq_raw mol
        input.certified.input.molecule agreement.1 supported
      rw [keysEq] at member
      rw [List.mem_map] at member
      obtain ⟨bond, hbond, hkey⟩ := member
      have connects := RawMolecule.connects_of_edgeKey_eq bond hkey
      have rawPositive : 0 < mol.bondOrder left right :=
        (RawMolecule.bondOrder_pos_iff_exists_bond mol hne).mpr
          ⟨bond, hbond, connects⟩
      rw [zero] at rawPositive
      exact Nat.lt_irrefl 0 rawPositive
    rw [zero]
    exact SemanticMolecule.localizedBondOrder_eq_zero_of_no_record
      input.certified.input.molecule left right absent

/-- The localized molecular graph bond is the raw bond order at the corresponding indices. -/
theorem moleculeGraph_bond_eq_rawBondOrder
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (left right : input.Atom) :
    input.moleculeGraph.bond left right = mol.bondOrder left.val right.val := by
  by_cases same : left = right
  · subst right
    exact (input.moleculeGraph.bond_self left).trans
      (RawMolecule.bondOrder_self mol left.val).symm
  · have hne : left.val ≠ right.val := fun equality => same (Fin.ext equality)
    unfold CertifiedLocalizedCIPInput.moleculeGraph
    rw [SemanticMolecule.toLocalizedMoleculeGraph_bond]
    exact localizedBondOrder_eq_rawBondOrder_of_agreement mol input agreement wellFormed
      unique supported hne

/-! ## Neighbour-list transport -/

/-- The raw incident-neighbour list permutes the sorted localized neighbour list. -/
theorem canonicalIncidentNeighbors_perm_sortedNeighborAtoms
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (atom : Fin mol.atomCount) :
    mol.canonicalIncidentNeighbors atom.val ~
      (input.sortedNeighborAtoms (localizedIndexOf mol input agreement atom)).map
        (fun neighbor => neighbor.val) := by
  let current : input.Atom := localizedIndexOf mol input agreement atom
  refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
  · exact RawMolecule.canonicalIncidentNeighbors_nodup mol atom.val unique
  · exact List.Nodup.map (fun left right equality => Fin.val_inj.mp equality)
      (CertifiedLocalizedCIPInput.sortedNeighborAtoms_nodup input current)
  · intro other
    constructor
    · intro member
      have positive :=
        (RawMolecule.mem_canonicalIncidentNeighbors_iff mol atom.val wellFormed other).mp
          member
      have bounds := RawMolecule.bondOrder_pos_endpoint_lt mol wellFormed positive
      let target : input.Atom :=
        ⟨other, by
          have countExact := RawMolecule.toSemanticMolecule?_atomCount mol
            input.certified.input.molecule agreement.1
          rw [countExact]
          exact bounds.2⟩
      have bondEq : input.moleculeGraph.bond current target =
          mol.bondOrder atom.val other := by
        simpa [current, target, localizedIndexOf] using
          moleculeGraph_bond_eq_rawBondOrder mol input agreement wellFormed unique supported
            current target
      have targetPositive : 0 < input.moleculeGraph.bond current target := by
        rw [bondEq]
        exact positive
      have targetMember : target ∈ input.sortedNeighborAtoms current :=
        (CertifiedLocalizedCIPInput.mem_sortedNeighborAtoms_iff input current target).mpr
          targetPositive
      rw [List.mem_map]
      exact ⟨target, targetMember, rfl⟩
    · rw [List.mem_map]
      rintro ⟨target, targetMember, valueEq⟩
      have targetPositive :=
        (CertifiedLocalizedCIPInput.mem_sortedNeighborAtoms_iff input current target).mp
          targetMember
      have bondEq : input.moleculeGraph.bond current target =
          mol.bondOrder atom.val target.val := by
        simpa [current, localizedIndexOf] using
          moleculeGraph_bond_eq_rawBondOrder mol input agreement wellFormed unique supported
            current target
      have rawPositive : 0 < mol.bondOrder atom.val target.val := by
        rw [← bondEq]
        exact targetPositive
      rw [← valueEq]
      exact (RawMolecule.mem_canonicalIncidentNeighbors_iff mol atom.val wellFormed
        target.val).mpr rawPositive

/-! ## Seed-copy transport -/

/-- The raw seed enumeration permutes the localized sorted seed enumeration. -/
theorem canonicalSeedCopies_perm_executableSeedCopies
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (node : RawMolecule.CanonicalBranchNode) (atomBound : node.atom < mol.atomCount)
    (noOxido : NoOxidoRootEdgeHistory mol node) :
    mol.canonicalSeedCopies node ~
      (input.executableSeedCopies
        (localizedIndexOf mol input agreement ⟨node.atom, atomBound⟩)).map
        (fun copy => (copy.1.val, copy.2)) := by
  let atom : Fin mol.atomCount := ⟨node.atom, atomBound⟩
  let current : input.Atom := localizedIndexOf mol input agreement atom
  let g : input.Atom × ℕ → ℕ × ℕ := fun copy => (copy.1.val, copy.2)
  let rawBlock : ℕ → List (ℕ × ℕ) := fun next =>
    (List.range (mol.canonicalBondOrder node next)).map fun copyIndex => (next, copyIndex)
  let locBlock : input.Atom → List (input.Atom × ℕ) := fun neighbor =>
    (List.range (input.moleculeGraph.bond current neighbor)).map fun copyIndex =>
      (neighbor, copyIndex)
  have hneighbors : mol.canonicalIncidentNeighbors node.atom ~
      (input.sortedNeighborAtoms current).map (fun neighbor => neighbor.val) :=
    canonicalIncidentNeighbors_perm_sortedNeighborAtoms mol input agreement wellFormed
      unique supported atom
  have hblock : ∀ neighbor ∈ input.sortedNeighborAtoms current,
      (locBlock neighbor).map g = rawBlock neighbor.val := by
    intro neighbor _
    have bondEq : input.moleculeGraph.bond current neighbor =
        mol.bondOrder node.atom neighbor.val := by
      simpa [current, atom, localizedIndexOf] using
        moleculeGraph_bond_eq_rawBondOrder mol input agreement wellFormed unique supported
          current neighbor
    have canonicalEq : mol.canonicalBondOrder node neighbor.val =
        mol.bondOrder node.atom neighbor.val :=
      canonicalBondOrder_eq_bondOrder_of_noOxidoRootEdge mol node noOxido neighbor.val
    calc
      (locBlock neighbor).map g
          = (List.range (mol.bondOrder node.atom neighbor.val)).map
              (fun copyIndex => (neighbor.val, copyIndex)) := by
            simp only [locBlock, g, List.map_map, Function.comp_def, bondEq]
      _ = (List.range (mol.canonicalBondOrder node neighbor.val)).map
              (fun copyIndex => (neighbor.val, copyIndex)) := by
            rw [canonicalEq]
      _ = rawBlock neighbor.val := rfl
  have hmain : (mol.canonicalIncidentNeighbors node.atom).flatMap rawBlock ~
      (input.sortedNeighborAtoms current).flatMap
        (fun neighbor => (locBlock neighbor).map g) := by
    have hperm : (mol.canonicalIncidentNeighbors node.atom).flatMap rawBlock ~
        ((input.sortedNeighborAtoms current).map
          (fun neighbor => neighbor.val)).flatMap rawBlock :=
      List.Perm.flatMap_right rawBlock hneighbors
    have heq : (input.sortedNeighborAtoms current).flatMap
          (fun neighbor => (locBlock neighbor).map g) =
        ((input.sortedNeighborAtoms current).map
          (fun neighbor => neighbor.val)).flatMap rawBlock := by
      rw [List.flatMap_map]
      exact List.flatMap_congr hblock
    rw [heq]
    exact hperm
  unfold RawMolecule.canonicalSeedCopies CertifiedLocalizedCIPInput.executableSeedCopies
  rw [List.map_flatMap]
  exact hmain

/-- Exact seed-copy multiplicity transport, before any parent-copy removal. -/
theorem canonicalSeedCopies_countP_eq_executableSeedCopies
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (node : RawMolecule.CanonicalBranchNode) (atomBound : node.atom < mol.atomCount)
    (noOxido : NoOxidoRootEdgeHistory mol node)
    (predicate : ℕ × ℕ → Bool) :
    (input.executableSeedCopies
        (localizedIndexOf mol input agreement ⟨node.atom, atomBound⟩)).countP
        (fun copy => predicate (copy.1.val, copy.2)) =
      (mol.canonicalSeedCopies node).countP predicate := by
  let g : input.Atom × ℕ → ℕ × ℕ := fun copy => (copy.1.val, copy.2)
  have hperm : mol.canonicalSeedCopies node ~
      (input.executableSeedCopies
        (localizedIndexOf mol input agreement ⟨node.atom, atomBound⟩)).map g := by
    simpa [g] using
      canonicalSeedCopies_perm_executableSeedCopies mol input agreement wellFormed
        unique supported node atomBound noOxido
  have hcount := hperm.symm.countP_eq predicate
  rw [List.countP_map] at hcount
  simpa [Function.comp_def, g] using hcount

/-! ## Child-copy transport with real-parent removal -/

/-- The actual raw child-copy list permutes the localized executable child-copy list, preserving
every `(atom, copyIndex)` pair exactly. -/
theorem canonicalChildCopies_perm_executableOfficialChildCopies
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (node : RawMolecule.CanonicalBranchNode) (onode : OfficialCIPNode input.Atom)
    (atomBound : node.atom < mol.atomCount)
    (parentBound : node.parent < mol.atomCount)
    (currentObserved : onode.current? =
      some (localizedIndexOf mol input agreement ⟨node.atom, atomBound⟩))
    (parentObserved : onode.parent? =
      some (localizedIndexOf mol input agreement ⟨node.parent, parentBound⟩))
    (noOxido : NoOxidoRootEdgeHistory mol node) :
    (input.executableOfficialChildCopies onode).map
        (fun copy => (copy.1.val, copy.2)) ~
      mol.canonicalChildCopies node := by
  let atom : Fin mol.atomCount := ⟨node.atom, atomBound⟩
  let parentAtom : Fin mol.atomCount := ⟨node.parent, parentBound⟩
  let current : input.Atom := localizedIndexOf mol input agreement atom
  let localizedParent : input.Atom := localizedIndexOf mol input agreement parentAtom
  let g : input.Atom × ℕ → ℕ × ℕ := fun copy => (copy.1.val, copy.2)
  let pRaw : ℕ × ℕ → Bool := fun copy => !(copy.1 == node.parent && copy.2 == 0)
  let pLoc : input.Atom × ℕ → Bool :=
    fun copy => !(copy.1 == localizedParent && copy.2 == 0)
  have hloc : input.executableOfficialChildCopies onode =
      (input.executableSeedCopies current).filter pLoc := by
    simpa [pLoc] using
      CertifiedLocalizedCIPInput.executableOfficialChildCopies_eq_filter_seed
        input onode current localizedParent currentObserved parentObserved
  have hraw : mol.canonicalChildCopies node =
      (mol.canonicalSeedCopies node).filter pRaw := by
    simpa [pRaw] using
      RawMolecule.canonicalChildCopies_eq_filter_seed mol node unique
  have hseed : mol.canonicalSeedCopies node ~
      (input.executableSeedCopies current).map g := by
    simpa [current, g] using
      canonicalSeedCopies_perm_executableSeedCopies mol input agreement wellFormed unique
        supported node atomBound noOxido
  have hbeq : ∀ neighbor : input.Atom,
      (neighbor == localizedParent) = (neighbor.val == node.parent) := by
    intro neighbor
    have hval : localizedParent.val = node.parent := by
      simp [localizedParent, parentAtom, localizedIndexOf]
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    constructor
    · intro equality
      rw [equality]
      exact hval
    · intro valueEquality
      exact Fin.ext (valueEquality.trans hval.symm)
  have hpred : ∀ copy : input.Atom × ℕ, pRaw (g copy) = pLoc copy := by
    rintro ⟨neighbor, index⟩
    dsimp only [pRaw, pLoc, g]
    rw [hbeq neighbor]
  have hmapped :
      ((input.executableSeedCopies current).map g).filter pRaw =
        ((input.executableSeedCopies current).filter pLoc).map g := by
    rw [List.filter_map]
    apply congrArg (List.map g)
    exact List.filter_congr (fun copy _ => by
      simpa [Function.comp_def] using hpred copy)
  rw [hloc, hraw]
  have hfiltered := List.Perm.filter pRaw hseed
  rw [hmapped] at hfiltered
  exact hfiltered.symm

/-- Exact child-copy multiplicity transport after removing the real parent copy. -/
theorem canonicalChildCopies_countP_eq_executableOfficialChildCopies
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (node : RawMolecule.CanonicalBranchNode) (onode : OfficialCIPNode input.Atom)
    (atomBound : node.atom < mol.atomCount)
    (parentBound : node.parent < mol.atomCount)
    (currentObserved : onode.current? =
      some (localizedIndexOf mol input agreement ⟨node.atom, atomBound⟩))
    (parentObserved : onode.parent? =
      some (localizedIndexOf mol input agreement ⟨node.parent, parentBound⟩))
    (noOxido : NoOxidoRootEdgeHistory mol node)
    (predicate : ℕ × ℕ → Bool) :
    (input.executableOfficialChildCopies onode).countP
        (fun copy => predicate (copy.1.val, copy.2)) =
      (mol.canonicalChildCopies node).countP predicate := by
  let g : input.Atom × ℕ → ℕ × ℕ := fun copy => (copy.1.val, copy.2)
  have hperm : (input.executableOfficialChildCopies onode).map g ~
      mol.canonicalChildCopies node := by
    simpa [g] using
      canonicalChildCopies_perm_executableOfficialChildCopies mol input agreement
        wellFormed unique supported node onode atomBound parentBound currentObserved
        parentObserved noOxido
  have hcount := hperm.countP_eq predicate
  rw [List.countP_map] at hcount
  simpa [Function.comp_def, g] using hcount

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.RawMolecule.unordered_pair_eq_of_min_max_eq
assert_kernel_only TetraStereo.OneCenter.RawMolecule.semanticEdgeKey_eq_of_connects
assert_kernel_only TetraStereo.OneCenter.RawMolecule.connects_of_edgeKey_eq
assert_kernel_only TetraStereo.OneCenter.RawMolecule.mem_canonicalIncidentNeighbors_iff
assert_kernel_only TetraStereo.OneCenter.RawMolecule.bondOrder_pos_endpoint_lt
assert_kernel_only TetraStereo.OneCenter.RawMolecule.canonicalIncidentNeighbors_nodup
assert_kernel_only TetraStereo.OneCenter.RawMolecule.canonicalSeedCopies_nodup
assert_kernel_only TetraStereo.OneCenter.RawMolecule.mem_canonicalSeedCopies_iff
assert_kernel_only TetraStereo.OneCenter.RawMolecule.canonicalChildCopies_eq_erase_seed
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.eraseCanonicalParentCopy_eq_filter_of_nodup
assert_kernel_only TetraStereo.OneCenter.RawMolecule.canonicalChildCopies_eq_filter_seed
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableOfficialNeighborCopies_eq_seed
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableOfficialChildCopies_eq_filter_seed
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sortedNeighborAtoms_nodup
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_sortedNeighborAtoms_iff
assert_kernel_only
  TetraStereo.OneCenter.canonicalBondOrder_eq_bondOrder_of_noOxidoRootEdge
assert_kernel_only
  TetraStereo.OneCenter.localizedBondOrder?_eq_some_order_of_isLocalizedCovalent
assert_kernel_only
  TetraStereo.OneCenter.localizedCovalentRecord_mem_of_rawBond
assert_kernel_only
  TetraStereo.OneCenter.localizedBondOrder_eq_rawBondOrder_of_agreement
assert_kernel_only TetraStereo.OneCenter.moleculeGraph_bond_eq_rawBondOrder
assert_kernel_only
  TetraStereo.OneCenter.canonicalIncidentNeighbors_perm_sortedNeighborAtoms
assert_kernel_only
  TetraStereo.OneCenter.canonicalSeedCopies_perm_executableSeedCopies
assert_kernel_only
  TetraStereo.OneCenter.canonicalSeedCopies_countP_eq_executableSeedCopies
assert_kernel_only
  TetraStereo.OneCenter.canonicalChildCopies_perm_executableOfficialChildCopies
assert_kernel_only
  TetraStereo.OneCenter.canonicalChildCopies_countP_eq_executableOfficialChildCopies

end OneCenter
end TetraStereo
