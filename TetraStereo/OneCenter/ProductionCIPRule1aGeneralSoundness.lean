import TetraStereo.OneCenter.ProductionCIPRule1aAssembly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace RawMolecule

/-!
# Soundness of the general production Rule-1a branch

This module is deliberately downstream of `ProductionCIPRule1aAssembly`.  Importing the assembly
back into `ProductionCIPRule1aSoundness` would create a cycle through the matching-realization
layer.  The conclusions below are exactly the pointwise conclusion used by
`MancudeRule1aSound`, but only for the general maximum-matching branch.  No correctness property
of `simpleMancudeCycle?` is assumed or asserted here.
-/

/-- The general maximum-matching labeler is sound at a semantically localized attached--duplicate
edge.  The localization premise is essential: as a standalone function the general labeler only
checks that `duplicated` lies in the component of `attached`, whereas the independent
multiple-bond observation uses the average only when the two atoms themselves form a localized
edge. -/
theorem generalMancudeRule1aLabel?_sound_of_localized
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached duplicated : Fin mol.atomCount)
    (hlocalized : mol.toMoleculeGraph.LocalizedMancudeEdge attached duplicated)
    (label : CIPAtomicLabel)
    (hlabel : mol.generalMancudeRule1aLabel? attached.val duplicated.val = some label) :
    label.toExactAtomicNumber.value =
      (mol.toMoleculeGraph.exactRule1aMultipleBond attached duplicated).value := by
  rw [mol.toMoleculeGraph.exactRule1aMultipleBond_of_localized hlocalized]
  exact mol.generalMancudeRule1aLabel_exactAverage hwellFormed hunique
    attached duplicated label hlabel

/-- Raw production localization is sufficient for general-branch soundness.  This form discharges
the representation boundary with the exact raw-list/declarative-graph realization theorem and is
therefore directly usable while reasoning about the production dispatcher. -/
theorem generalMancudeRule1aLabel?_sound_of_raw_localized
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached duplicated : Fin mol.atomCount)
    (hraw : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true)
    (label : CIPAtomicLabel)
    (hlabel : mol.generalMancudeRule1aLabel? attached.val duplicated.val = some label) :
    label.toExactAtomicNumber.value =
      (mol.toMoleculeGraph.exactRule1aMultipleBond attached duplicated).value := by
  apply mol.generalMancudeRule1aLabel?_sound_of_localized hwellFormed hunique
  · exact (mol.containsUndirectedEdge_localizedMancudeEdges_iff
      hwellFormed hunique attached duplicated).1 hraw
  · exact hlabel

/-- The actual production dispatcher is sound whenever it reaches the general branch.  Together
with `mancudeRule1aLabel?_sound_of_not_localized`, this proves both non-shortcut branches of the
pointwise obligation defining `MancudeRule1aSound`.  It intentionally leaves the
`simpleMancudeCycle? = some _` branch outside the theorem. -/
theorem mancudeRule1aLabel?_sound_of_general_branch
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached duplicated : Fin mol.atomCount)
    (hraw : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true)
    (hshortcut : mol.simpleMancudeCycle? attached.val duplicated.val = none)
    (label : CIPAtomicLabel)
    (hlabel : mol.mancudeRule1aLabel? attached.val duplicated.val = some label) :
    label.toExactAtomicNumber.value =
      (mol.toMoleculeGraph.exactRule1aMultipleBond attached duplicated).value := by
  apply mol.generalMancudeRule1aLabel?_sound_of_raw_localized hwellFormed hunique
    attached duplicated hraw label
  unfold mancudeRule1aLabel? at hlabel
  simpa [hraw, hshortcut] using hlabel

/-- The general branch satisfies precisely the same pointwise postcondition as
`MancudeRule1aSound`, uniformly over all localized atom pairs for which the shortcut declines. -/
def MancudeRule1aGeneralBranchSound (mol : RawMolecule) : Prop :=
  ∀ (attached duplicated : Fin mol.atomCount) (label : CIPAtomicLabel),
    containsUndirectedEdge mol.localizedMancudeEdges attached.val duplicated.val = true →
    mol.simpleMancudeCycle? attached.val duplicated.val = none →
    mol.mancudeRule1aLabel? attached.val duplicated.val = some label →
      label.toExactAtomicNumber.value =
        (mol.toMoleculeGraph.exactRule1aMultipleBond attached duplicated).value

/-- Well-formed molecules with unique bond records satisfy the complete general-branch fragment
of the global production Rule-1a soundness obligation. -/
theorem mancudeRule1aGeneralBranchSound
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) :
    mol.MancudeRule1aGeneralBranchSound := by
  intro attached duplicated label hraw hshortcut hlabel
  exact mol.mancudeRule1aLabel?_sound_of_general_branch hwellFormed hunique
    attached duplicated hraw hshortcut label hlabel

/-!
## Conditional production totality of the general branch

Soundness above is partial correctness: a returned label is exact, but a component may be refused
with `none`.  The remaining gap is the converse direction: which graph-theoretic precondition
guarantees that the production maximum-matching search actually *returns* a label?  The
authoritative (uncapped) executable has this via

`TetraStereo.OneCenter.AuthoritativeCIPMancudeTotality.generalMancudeRule1aLabelAuthoritative?_exists`,

but the production labeler `generalMancudeRule1aLabel?` used by the ordinary dispatcher had no such
result.  The two functions share the same guard

`stats.size != writtenDoubleCount || stats.count == 0`,

so the precondition to pin is exactly: the written noncumulative double bonds already form a
maximum-cardinality matching of the localized component.  Under that condition both support guards
hold and the recursion cannot refuse.

This is stated against `IsMaximumMancudeEdgeMatching`, the importable graph-theoretic predicate of
`ProductionCIPRule1aMatchingRealization`, rather than a duplicated ad-hoc definition.  No claim is
made that an arbitrary molecule satisfies the precondition; it is retained as an explicit,
independently auditable hypothesis.
-/

/-- Under a written maximum matching, both support guards of the exhaustive production matching
summary hold: the maximum size is the written double-bond count and the witness count is positive.
This is the production-side counterpart of
`TetraStereo.OneCenter.AuthoritativeCIPMancudeTotality.exhaustiveMancudeMatchingStats_supported`,
proved directly from the importable family realization and therefore without importing the
authoritative stack (which would cycle back through this module). -/
theorem exhaustiveMancudeMatchingStats_supported_of_maximum
    (mol : RawMolecule) (attached : ℕ) (edges written : List (ℕ × ℕ))
    (hmaximum : IsMaximumMancudeEdgeMatching written edges) :
    (mol.exhaustiveMancudeMatchingStats attached edges).size = written.length ∧
      0 < (mol.exhaustiveMancudeMatchingStats attached edges).count := by
  have hwrittenMem :
      written ∈ maximumMancudeEdgeMatchings (exhaustiveMancudeEdgeMatchings edges) :=
    (mem_maximum_exhaustiveMancudeEdgeMatchings_iff edges written).2 hmaximum
  have hlength :
      written.length = mancudeFamilyMaximumSize (exhaustiveMancudeEdgeMatchings edges) := by
    have hfilter := (List.mem_filter.mp hwrittenMem).2
    simpa only [decide_eq_true_eq] using hfilter
  have hnonempty :
      maximumMancudeEdgeMatchings (exhaustiveMancudeEdgeMatchings edges) ≠ [] :=
    List.ne_nil_of_mem hwrittenMem
  rw [mol.exhaustiveMancudeMatchingStats_eq_edgeMatchingFamilyStats attached edges]
  change mancudeFamilyMaximumSize (exhaustiveMancudeEdgeMatchings edges) = written.length ∧
    0 < (maximumMancudeEdgeMatchings (exhaustiveMancudeEdgeMatchings edges)).length
  exact ⟨hlength.symm, List.length_pos_of_ne_nil hnonempty⟩

/-- The production general branch is total — it returns a label — at every localized attached
duplicate whose written double bonds form a maximum matching of its localized component.  This is
a sufficient support condition, separate from the partial correctness result
`generalMancudeRule1aLabel?_sound_of_localized`. -/
theorem generalMancudeRule1aLabel?_exists_of_localized_maximum
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached duplicated : Fin mol.atomCount)
    (hlocalized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true)
    (hmaximum : IsMaximumMancudeEdgeMatching
      ((mol.localizedMancudeComponentEdges attached.val).filter
        fun edge => mol.bondOrder edge.1 edge.2 == 2)
      (mol.localizedMancudeComponentEdges attached.val)) :
    ∃ label, mol.generalMancudeRule1aLabel? attached.val duplicated.val = some label := by
  let vertices := mol.localizedMancudeComponentVertices attached.val
  let edges := mol.localizedMancudeComponentEdges attached.val
  let written := edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2
  let stats := mol.exhaustiveMancudeMatchingStats attached.val edges
  have hsemantic : mol.toMoleculeGraph.LocalizedMancudeEdge attached duplicated :=
    (mol.containsUndirectedEdge_localizedMancudeEdges_iff hwellFormed hunique
      attached duplicated).1 hlocalized
  have hduplicatedMember : duplicated.val ∈ vertices :=
    (mol.mem_edgeComponent_localizedMancudeEdges_iff hwellFormed hunique
      attached duplicated).2 (Relation.ReflTransGen.single hsemantic)
  have hduplicatedContained : vertices.contains duplicated.val = true :=
    List.contains_iff_mem.mpr hduplicatedMember
  have hedgesNonempty : edges ≠ [] := by
    have hrealizes := mol.localizedMancudeComponentEdges_realization hwellFormed hunique attached
    have hmatched : NatEdgeMatchedBy edges attached duplicated :=
      (hrealizes.localizedComponent_iff attached duplicated).2
        ⟨hsemantic, Relation.ReflTransGen.refl⟩
    rcases hmatched with ⟨edge, hedge, _incident⟩
    exact List.ne_nil_of_mem hedge
  have hedgesIsEmpty : edges.isEmpty = false := by
    cases edgesEq : edges with
    | nil => exact absurd edgesEq hedgesNonempty
    | cons edge rest => rfl
  have hsupported : stats.size = written.length ∧ 0 < stats.count :=
    mol.exhaustiveMancudeMatchingStats_supported_of_maximum attached.val edges written hmaximum
  have hstatsCall : mol.mancudeMatchingStats attached.val (edges.length + 1) edges = some stats :=
    mol.mancudeMatchingStats_length_succ attached.val edges
  refine ⟨({ numerator := stats.partnerZSum, denominator := stats.count } : CIPAtomicLabel), ?_⟩
  unfold generalMancudeRule1aLabel?
  change (if !vertices.contains duplicated.val || edges.isEmpty then none
    else do
      let observed ← mol.mancudeMatchingStats attached.val (edges.length + 1) edges
      if observed.size != written.length || observed.count == 0 then none
      else some ({ numerator := observed.partnerZSum, denominator := observed.count } :
        CIPAtomicLabel)) =
        some ({ numerator := stats.partnerZSum, denominator := stats.count } : CIPAtomicLabel)
  rw [hduplicatedContained, hedgesIsEmpty, hstatsCall]
  simp [hsupported.1, Nat.ne_of_gt hsupported.2]

/-- The actual production dispatcher is total at a localized attached duplicate whose component
satisfies the written-maximum condition, whether it resolves through the closed simple-cycle
formula or the general search.  This pins the single graph-theoretic precondition under which the
shortcut priority in `mancudeRule1aLabel?` cannot silently refuse. -/
theorem mancudeRule1aLabel?_exists_of_localized_maximum
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached duplicated : Fin mol.atomCount)
    (hlocalized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true)
    (hmaximum : IsMaximumMancudeEdgeMatching
      ((mol.localizedMancudeComponentEdges attached.val).filter
        fun edge => mol.bondOrder edge.1 edge.2 == 2)
      (mol.localizedMancudeComponentEdges attached.val)) :
    ∃ label, mol.mancudeRule1aLabel? attached.val duplicated.val = some label := by
  cases hcycle : mol.simpleMancudeCycle? attached.val duplicated.val with
  | none =>
      rcases mol.generalMancudeRule1aLabel?_exists_of_localized_maximum hwellFormed hunique
        attached duplicated hlocalized hmaximum with ⟨label, hgeneral⟩
      exact ⟨label, by
        unfold mancudeRule1aLabel?
        simpa [hlocalized, hcycle] using hgeneral⟩
  | some cycleData =>
      rcases cycleData with ⟨cycle, alternate⟩
      exact ⟨mol.simpleMancudeCycleLabel duplicated.val alternate cycle, by
        unfold mancudeRule1aLabel?
        simp [hlocalized, hcycle]⟩

end RawMolecule

end
end OneCenter
end TetraStereo
