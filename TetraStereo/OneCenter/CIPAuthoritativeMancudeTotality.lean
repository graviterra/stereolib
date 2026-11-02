import TetraStereo.OneCenter.CIPAuthoritativeRule1aSoundness
import TetraStereo.OneCenter.CIPAuthoritativeCursorSupport

set_option autoImplicit false

namespace TetraStereo.OneCenter.AuthoritativeCIPMancudeTotality

open RawMolecule
open AuthoritativeCIPCursorSupport

/-!
# Chemical totality of the uncapped Rule-1a mancude label

The authoritative implementation exhaustively enumerates every matching, so fuel and component
size cannot make it fail.  Its remaining chemical guard says that the written noncumulative
double bonds already form a maximum matching of the localized mancude component.  The proposition
below states exactly that graph-theoretic Kekulé condition, independently of an `Option` result.
-/

/-- In every localized component, its written noncumulative double-bond occurrences constitute a
maximum-cardinality matching of the complete finite localized edge graph. -/
def LocalizedMancudeKekuleAdmissible (mol : RawMolecule) : Prop :=
  ∀ attached : Fin mol.atomCount,
    let edges := mol.localizedMancudeComponentEdges attached.val
    let written := edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2
    IsMaximumMancudeEdgeMatching written edges

/-- A maximum written matching determines both successful support guards of the exhaustive
matching summary: its size is the written double count and its witness count is positive. -/
theorem exhaustiveMancudeMatchingStats_supported
    (mol : RawMolecule) (admissible : LocalizedMancudeKekuleAdmissible mol)
    (attached : Fin mol.atomCount) :
    let edges := mol.localizedMancudeComponentEdges attached.val
    let written := edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2
    let stats := mol.exhaustiveMancudeMatchingStats attached.val edges
    stats.size = written.length ∧ 0 < stats.count := by
  let edges := mol.localizedMancudeComponentEdges attached.val
  let written := edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2
  let family := exhaustiveMancudeEdgeMatchings edges
  let maximum := maximumMancudeEdgeMatchings family
  have writtenMaximum : IsMaximumMancudeEdgeMatching written edges := admissible attached
  have writtenMember : written ∈ maximum := by
    exact (mem_maximum_exhaustiveMancudeEdgeMatchings_iff edges written).2 writtenMaximum
  have writtenLength : written.length = mancudeFamilyMaximumSize family := by
    unfold maximum at writtenMember
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp writtenMember).2
  have maximumNonempty : maximum ≠ [] := List.ne_nil_of_mem writtenMember
  have maximumLengthPositive : 0 < maximum.length := by
    exact Nat.pos_of_ne_zero (by
      intro lengthZero
      apply maximumNonempty
      simpa using lengthZero)
  change (mol.exhaustiveMancudeMatchingStats attached.val edges).size = written.length ∧
    0 < (mol.exhaustiveMancudeMatchingStats attached.val edges).count
  rw [mol.exhaustiveMancudeMatchingStats_eq_edgeMatchingFamilyStats attached.val edges]
  change mancudeFamilyMaximumSize family = written.length ∧ 0 < maximum.length
  exact ⟨writtenLength.symm, maximumLengthPositive⟩

/-- A raw localized-edge observation in a well-formed molecule has two in-range endpoints. -/
theorem localizedMancudeEndpoints_lt
    (mol : RawMolecule) (wellFormed : mol.WellFormed) (attached duplicated : Nat)
    (localized : containsUndirectedEdge mol.localizedMancudeEdges attached duplicated = true) :
    attached < mol.atomCount ∧ duplicated < mol.atomCount := by
  unfold containsUndirectedEdge at localized
  simp only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at localized
  rcases localized with ⟨edge, edgeMember, forward | reverse⟩
  · have bounds := mol.endpoints_lt_of_mem_localizedMancudeEdges wellFormed edgeMember
    simpa [forward.1, forward.2] using bounds
  · have bounds := mol.endpoints_lt_of_mem_localizedMancudeEdges wellFormed edgeMember
    exact ⟨by simpa [reverse.1, reverse.2] using bounds.2,
      by simpa [reverse.1, reverse.2] using bounds.1⟩

/-- The endpoint of a localized edge is present in the exact finite component traversal. -/
theorem localizedMancudeEndpoint_mem_component
    (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (attached duplicated : Fin mol.atomCount)
    (localized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true) :
    duplicated.val ∈ mol.localizedMancudeComponentVertices attached.val := by
  have semantic := (mol.containsUndirectedEdge_localizedMancudeEdges_iff
    wellFormed unique attached duplicated).1 localized
  exact (mol.mem_edgeComponent_localizedMancudeEdges_iff
    wellFormed unique attached duplicated).2 (Relation.ReflTransGen.single semantic)

/-- A localized edge makes its component-filtered edge list nonempty. -/
theorem localizedMancudeComponentEdges_ne_nil
    (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (attached duplicated : Fin mol.atomCount)
    (localized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true) :
    mol.localizedMancudeComponentEdges attached.val ≠ [] := by
  have semantic := (mol.containsUndirectedEdge_localizedMancudeEdges_iff
    wellFormed unique attached duplicated).1 localized
  have realization := mol.localizedMancudeComponentEdges_realization
    wellFormed unique attached
  have matched : NatEdgeMatchedBy (mol.localizedMancudeComponentEdges attached.val)
      attached duplicated :=
    (realization.localizedComponent_iff attached duplicated).2
      ⟨semantic, Relation.ReflTransGen.refl⟩
  rcases matched with ⟨edge, edgeMember, _incident⟩
  exact List.ne_nil_of_mem edgeMember

/-- Exact localized Kekulé admissibility makes the uncapped general-mancude branch total. -/
theorem generalMancudeRule1aLabelAuthoritative?_exists
    (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique)
    (admissible : LocalizedMancudeKekuleAdmissible mol)
    (attached duplicated : Fin mol.atomCount)
    (localized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true) :
    ∃ label, mol.generalMancudeRule1aLabelAuthoritative?
      attached.val duplicated.val = some label := by
  let vertices := mol.localizedMancudeComponentVertices attached.val
  let edges := mol.localizedMancudeComponentEdges attached.val
  let written := edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2
  let stats := mol.exhaustiveMancudeMatchingStats attached.val edges
  have duplicatedMember := localizedMancudeEndpoint_mem_component mol wellFormed unique
    attached duplicated localized
  have duplicatedContained : vertices.contains duplicated.val = true := by
    exact List.contains_iff_mem.mpr duplicatedMember
  have edgesNonempty : edges ≠ [] :=
    localizedMancudeComponentEdges_ne_nil mol wellFormed unique attached duplicated localized
  have edgesIsEmpty : edges.isEmpty = false := by
    cases edgesEq : edges with
    | nil => exact False.elim (edgesNonempty edgesEq)
    | cons edge rest => rfl
  have statsSupported := exhaustiveMancudeMatchingStats_supported mol admissible attached
  change stats.size = written.length ∧ 0 < stats.count at statsSupported
  have statsCall := mol.mancudeMatchingStats_length_succ attached.val edges
  change mol.mancudeMatchingStats attached.val (edges.length + 1) edges = some stats at statsCall
  refine ⟨({ numerator := stats.partnerZSum, denominator := stats.count } : CIPAtomicLabel), ?_⟩
  unfold RawMolecule.generalMancudeRule1aLabelAuthoritative?
  change (if !vertices.contains duplicated.val || edges.isEmpty then none
    else do
      let observed ← mol.mancudeMatchingStats attached.val (edges.length + 1) edges
      if observed.size != written.length || observed.count == 0 then none
      else some ({ numerator := observed.partnerZSum, denominator := observed.count } :
        CIPAtomicLabel)) =
        some ({ numerator := stats.partnerZSum, denominator := stats.count } : CIPAtomicLabel)
  rw [duplicatedContained, edgesIsEmpty, statsCall]
  simp [statsSupported.1, Nat.ne_of_gt statsSupported.2]

/-- Well-formedness, unique bond records, and the independent maximum-written-matching condition
make every uncapped authoritative mancude dispatch total.  The proposition consumed by the
Rules-1a--6 hierarchy is therefore derived rather than assumed. -/
theorem mancudeRule1aSupported_of_localizedKekuleAdmissible
    (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique)
    (admissible : LocalizedMancudeKekuleAdmissible mol) :
    MancudeRule1aSupported mol := by
  intro attached duplicated
  by_cases localized : containsUndirectedEdge mol.localizedMancudeEdges
      attached duplicated = true
  · rcases localizedMancudeEndpoints_lt mol wellFormed attached duplicated localized with
      ⟨attachedBound, duplicatedBound⟩
    let attachedFin : Fin mol.atomCount := ⟨attached, attachedBound⟩
    let duplicatedFin : Fin mol.atomCount := ⟨duplicated, duplicatedBound⟩
    cases cycleEq : mol.simpleMancudeCycle? attached duplicated with
    | none =>
        rcases generalMancudeRule1aLabelAuthoritative?_exists mol wellFormed unique admissible
          attachedFin duplicatedFin localized with ⟨label, general⟩
        exact ⟨label, by
          unfold RawMolecule.mancudeRule1aLabelAuthoritative?
          simpa [localized, cycleEq, attachedFin, duplicatedFin] using general⟩
    | some cycleData =>
        rcases cycleData with ⟨cycle, alternate⟩
        exact ⟨mol.simpleMancudeCycleLabel duplicated alternate cycle, by
          unfold RawMolecule.mancudeRule1aLabelAuthoritative?
          simp [localized, cycleEq]⟩
  · have localizedFalse : containsUndirectedEdge mol.localizedMancudeEdges
        attached duplicated = false := Bool.eq_false_of_not_eq_true localized
    exact ⟨{ numerator := mol.atomZAt duplicated, denominator := 1 }, by
      unfold RawMolecule.mancudeRule1aLabelAuthoritative?
      simp [localizedFalse]⟩

end TetraStereo.OneCenter.AuthoritativeCIPMancudeTotality
