import TetraStereo.OneCenter.ExplicitHydrogenDoubleBondEndpointCount
import TetraStereo.OneCenter.CIPAuthoritativeMancudeTotality

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open AuthoritativeCIPMancudeTotality

namespace RawMolecule

/-!
# Localized Mancude/Kekulé preservation under hydrogen materialization

Hydrogen materialization appends only ordinary hydrogen atoms and single bonds. This module proves
that it therefore leaves the complete localized Mancude ring graph and its written maximum
matching condition unchanged on the original atoms, while every fresh hydrogen has an empty
localized component.
-/

private theorem filter_eq_nil_of_forall_false {α : Type*}
    (predicate : α → Bool) (values : List α)
    (invisible : ∀ value ∈ values, predicate value = false) :
    values.filter predicate = [] := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headFalse : predicate head = false := invisible head (by simp)
      have tailInvisible : ∀ value ∈ tail, predicate value = false := by
        intro value member
        exact invisible value (by simp [member])
      simp [headFalse, inductionHypothesis tailInvisible]

private theorem filterMap_eq_nil_of_forall_none {α β : Type*}
    (transform : α → Option β) (values : List α)
    (invisible : ∀ value ∈ values, transform value = none) :
    values.filterMap transform = [] := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headNone : transform head = none := invisible head (by simp)
      have tailInvisible : ∀ value ∈ tail, transform value = none := by
        intro value member
        exact invisible value (by simp [member])
      simp [headNone, inductionHypothesis tailInvisible]

/-- Inserting a block invisible to a filter leaves the filtered old sequence exactly unchanged. -/
private theorem insertAfterFirst_eq_some_filter
    (insertPredicate filterPredicate : RawBond → Bool)
    (extra bonds out : List RawBond)
    (invisible : ∀ bond ∈ extra, filterPredicate bond = false)
    (observed : insertAfterFirst insertPredicate extra bonds = some out) :
    out.filter filterPredicate = bonds.filter filterPredicate := by
  have extraFiltered : extra.filter filterPredicate = [] :=
    filter_eq_nil_of_forall_false filterPredicate extra invisible
  induction bonds generalizing out with
  | nil => simp [insertAfterFirst] at observed
  | cons bond rest inductionHypothesis =>
      simp only [insertAfterFirst] at observed
      split at observed
      · cases observed
        simp only [List.filter_cons, List.filter_append, extraFiltered, List.nil_append]
      · cases mapped : insertAfterFirst insertPredicate extra rest with
        | none => simp [mapped] at observed
        | some tail =>
            simp [mapped] at observed
            cases observed
            simp only [List.filter_cons, inductionHypothesis tail mapped]

private theorem insertBeforeFirst_eq_some_filter
    (insertPredicate filterPredicate : RawBond → Bool)
    (extra bonds out : List RawBond)
    (invisible : ∀ bond ∈ extra, filterPredicate bond = false)
    (observed : insertBeforeFirst insertPredicate extra bonds = some out) :
    out.filter filterPredicate = bonds.filter filterPredicate := by
  have extraFiltered : extra.filter filterPredicate = [] :=
    filter_eq_nil_of_forall_false filterPredicate extra invisible
  induction bonds generalizing out with
  | nil => simp [insertBeforeFirst] at observed
  | cons bond rest inductionHypothesis =>
      simp only [insertBeforeFirst] at observed
      split at observed
      · cases observed
        simp only [List.filter_append, List.filter_cons, extraFiltered, List.nil_append]
      · cases mapped : insertBeforeFirst insertPredicate extra rest with
        | none => simp [mapped] at observed
        | some tail =>
            simp [mapped] at observed
            cases observed
            simp only [List.filter_cons, inductionHypothesis tail mapped]

private theorem spliceHydrogenBonds_filter_legacy
    (bonds : List RawBond) (index : ℕ) (extra : List RawBond)
    (filterPredicate : RawBond → Bool)
    (invisible : ∀ bond ∈ extra, filterPredicate bond = false) :
    (spliceHydrogenBonds bonds index extra).filter filterPredicate =
      bonds.filter filterPredicate := by
  have extraFiltered : extra.filter filterPredicate = [] :=
    filter_eq_nil_of_forall_false filterPredicate extra invisible
  unfold spliceHydrogenBonds
  split
  · rename_i empty
    have extraNil : extra = [] := List.isEmpty_iff.mp empty
    subst extra
    rfl
  · cases after : insertAfterFirst (fun bond => bond.target == index) extra bonds with
    | some out =>
        exact insertAfterFirst_eq_some_filter _ _ _ _ _ invisible after
    | none =>
        cases before : insertBeforeFirst (fun bond => bond.source == index) extra bonds with
        | some out =>
            exact insertBeforeFirst_eq_some_filter _ _ _ _ _ invisible before
        | none => simp [extraFiltered]

/-- The corresponding exact-sequence statement for an invisible `filterMap` block. -/
private theorem insertAfterFirst_eq_some_filterMap {β : Type*}
    (insertPredicate : RawBond → Bool) (transform : RawBond → Option β)
    (extra bonds out : List RawBond)
    (invisible : ∀ bond ∈ extra, transform bond = none)
    (observed : insertAfterFirst insertPredicate extra bonds = some out) :
    out.filterMap transform = bonds.filterMap transform := by
  have extraFiltered : extra.filterMap transform = [] :=
    filterMap_eq_nil_of_forall_none transform extra invisible
  induction bonds generalizing out with
  | nil => simp [insertAfterFirst] at observed
  | cons bond rest inductionHypothesis =>
      simp only [insertAfterFirst] at observed
      split at observed
      · cases observed
        simp only [List.filterMap_cons, List.filterMap_append, extraFiltered, List.nil_append]
      · cases mapped : insertAfterFirst insertPredicate extra rest with
        | none => simp [mapped] at observed
        | some tail =>
            simp [mapped] at observed
            cases observed
            simp only [List.filterMap_cons, inductionHypothesis tail mapped]

private theorem insertBeforeFirst_eq_some_filterMap {β : Type*}
    (insertPredicate : RawBond → Bool) (transform : RawBond → Option β)
    (extra bonds out : List RawBond)
    (invisible : ∀ bond ∈ extra, transform bond = none)
    (observed : insertBeforeFirst insertPredicate extra bonds = some out) :
    out.filterMap transform = bonds.filterMap transform := by
  have extraFiltered : extra.filterMap transform = [] :=
    filterMap_eq_nil_of_forall_none transform extra invisible
  induction bonds generalizing out with
  | nil => simp [insertBeforeFirst] at observed
  | cons bond rest inductionHypothesis =>
      simp only [insertBeforeFirst] at observed
      split at observed
      · cases observed
        simp only [List.filterMap_append, List.filterMap_cons, extraFiltered, List.nil_append]
      · cases mapped : insertBeforeFirst insertPredicate extra rest with
        | none => simp [mapped] at observed
        | some tail =>
            simp [mapped] at observed
            cases observed
            simp only [List.filterMap_cons, inductionHypothesis tail mapped]

private theorem spliceHydrogenBonds_filterMap_legacy {β : Type*}
    (bonds : List RawBond) (index : ℕ) (extra : List RawBond)
    (transform : RawBond → Option β)
    (invisible : ∀ bond ∈ extra, transform bond = none) :
    (spliceHydrogenBonds bonds index extra).filterMap transform =
      bonds.filterMap transform := by
  have extraFiltered : extra.filterMap transform = [] :=
    filterMap_eq_nil_of_forall_none transform extra invisible
  unfold spliceHydrogenBonds
  split
  · rename_i empty
    have extraNil : extra = [] := List.isEmpty_iff.mp empty
    subst extra
    rfl
  · cases after : insertAfterFirst (fun bond => bond.target == index) extra bonds with
    | some out =>
        exact insertAfterFirst_eq_some_filterMap _ _ _ _ _ invisible after
    | none =>
        cases before : insertBeforeFirst (fun bond => bond.source == index) extra bonds with
        | some out =>
            exact insertBeforeFirst_eq_some_filterMap _ _ _ _ _ invisible before
        | none => simp [extraFiltered]

private theorem spliceHydrogenBonds_filter
    (predecessor : Option (Option ℕ))
    (bonds : List RawBond) (index : ℕ) (extra : List RawBond)
    (filterPredicate : RawBond → Bool)
    (invisible : ∀ bond ∈ extra, filterPredicate bond = false) :
    (spliceHydrogenBondsWithPredecessor predecessor bonds index extra).filter filterPredicate =
      bonds.filter filterPredicate := by
  have extraFiltered : extra.filter filterPredicate = [] :=
    filter_eq_nil_of_forall_false filterPredicate extra invisible
  unfold spliceHydrogenBondsWithPredecessor
  split
  · rfl
  · cases predecessor with
    | none => exact spliceHydrogenBonds_filter_legacy _ _ _ _ invisible
    | some parent =>
        cases parent with
        | none =>
            cases inserted : insertBeforeFirst
                (fun bond => bond.source == index || bond.target == index) extra bonds with
            | none => simp [extraFiltered]
            | some out => exact insertBeforeFirst_eq_some_filter _ _ _ _ _ invisible inserted
        | some parent =>
            change ((insertAfterFirst
              (fun bond => bond.source == parent && bond.target == index) extra bonds).getD
                (bonds ++ extra)).filter filterPredicate = bonds.filter filterPredicate
            cases inserted : insertAfterFirst
                (fun bond => bond.source == parent && bond.target == index) extra bonds with
            | none => simp [extraFiltered]
            | some out => exact insertAfterFirst_eq_some_filter _ _ _ _ _ invisible inserted

private theorem spliceHydrogenBonds_filterMap {β : Type*}
    (predecessor : Option (Option ℕ))
    (bonds : List RawBond) (index : ℕ) (extra : List RawBond)
    (transform : RawBond → Option β)
    (invisible : ∀ bond ∈ extra, transform bond = none) :
    (spliceHydrogenBondsWithPredecessor predecessor bonds index extra).filterMap transform =
      bonds.filterMap transform := by
  have extraFiltered : extra.filterMap transform = [] :=
    filterMap_eq_nil_of_forall_none transform extra invisible
  unfold spliceHydrogenBondsWithPredecessor
  split
  · rfl
  · cases predecessor with
    | none => exact spliceHydrogenBonds_filterMap_legacy _ _ _ _ invisible
    | some parent =>
        cases parent with
        | none =>
            cases inserted : insertBeforeFirst
                (fun bond => bond.source == index || bond.target == index) extra bonds with
            | none => simp [extraFiltered]
            | some out => exact insertBeforeFirst_eq_some_filterMap _ _ _ _ _ invisible inserted
        | some parent =>
            change ((insertAfterFirst
              (fun bond => bond.source == parent && bond.target == index) extra bonds).getD
                (bonds ++ extra)).filterMap transform = bonds.filterMap transform
            cases inserted : insertAfterFirst
                (fun bond => bond.source == parent && bond.target == index) extra bonds with
            | none => simp [extraFiltered]
            | some out => exact insertAfterFirst_eq_some_filterMap _ _ _ _ _ invisible inserted

/-- A materialization step adds only single bonds, so it preserves every atom's exact written
double-bond incidence count. -/
theorem withExplicitHydrogensStep_incidentDoubleBondCount
    (molecule : RawMolecule) (state : HydrogenExpansionState)
    (index atom : ℕ) :
    (withExplicitHydrogensStep molecule state index).toRawMolecule.incidentDoubleBondCount atom =
      state.toRawMolecule.incidentDoubleBondCount atom := by
  by_cases zero : molecule.hydrogenCountAt index == 0
  · simp [withExplicitHydrogensStep, zero]
  · let count := molecule.hydrogenCountAt index
    let base := state.1.length
    let hydrogenIds := (List.range count).map fun offset => base + offset
    let newBonds := hydrogenIds.map fun hydrogen =>
      { source := index, target := hydrogen, kind := ParsedBondKind.single : RawBond }
    let predicate : RawBond → Bool := fun bond =>
      bond.kind.order == 2 && (bond.source == atom || bond.target == atom)
    have invisible : ∀ bond ∈ newBonds, predicate bond = false := by
      intro bond member
      rcases List.mem_map.mp member with ⟨hydrogen, _hydrogenMember, rfl⟩
      simp [predicate, ParsedBondKind.order]
    have filtered :=
      spliceHydrogenBonds_filter (molecule.introductionPredecessors[index]?) state.2.1 index newBonds predicate invisible
    have lengths := congrArg List.length filtered
    simpa [withExplicitHydrogensStep, zero, HydrogenExpansionState.toRawMolecule,
      incidentDoubleBondCount, count, base, hydrogenIds, newBonds, predicate] using lengths

theorem fold_withExplicitHydrogensStep_incidentDoubleBondCount
    (molecule : RawMolecule) (indices : List ℕ)
    (state : HydrogenExpansionState) (atom : ℕ) :
    ((indices.foldl (withExplicitHydrogensStep molecule) state).toRawMolecule.incidentDoubleBondCount
        atom) =
      state.toRawMolecule.incidentDoubleBondCount atom := by
  induction indices generalizing state with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      exact withExplicitHydrogensStep_incidentDoubleBondCount molecule state index atom

/-- Hydrogen materialization preserves the exact double-bond incidence count at every natural
index, including indices beyond the original atom list. -/
@[simp] theorem withExplicitHydrogens_incidentDoubleBondCount
    (molecule : RawMolecule) (atom : ℕ) :
    molecule.withExplicitHydrogens.incidentDoubleBondCount atom =
      molecule.incidentDoubleBondCount atom := by
  have folded := fold_withExplicitHydrogensStep_incidentDoubleBondCount molecule
    (List.range molecule.atomCount) (initialHydrogenExpansionState molecule) atom
  simpa [withExplicitHydrogens, initialHydrogenExpansionState,
    HydrogenExpansionState.toRawMolecule] using folded

/-- A well-formed raw bond list has no double-bond incidence outside its atom list. -/
theorem incidentDoubleBondCount_eq_zero_of_not_lt
    (molecule : RawMolecule) (well : molecule.WellFormed)
    (atom : ℕ) (outside : ¬ atom < molecule.atomCount) :
    molecule.incidentDoubleBondCount atom = 0 := by
  unfold incidentDoubleBondCount
  have filtered :
      molecule.bonds.filter (fun bond =>
        bond.kind.order == 2 && (bond.source == atom || bond.target == atom)) = [] := by
    apply filter_eq_nil_of_forall_false
    intro bond member
    have endpoints := well bond member
    have atomLower : molecule.atomCount ≤ atom := Nat.le_of_not_gt outside
    have sourceNe : bond.source ≠ atom :=
      Nat.ne_of_lt (lt_of_lt_of_le endpoints.1 atomLower)
    have targetNe : bond.target ≠ atom :=
      Nat.ne_of_lt (lt_of_lt_of_le endpoints.2.1 atomLower)
    simp [sourceNe, targetNe]
  rw [filtered]
  rfl

/-- Consequently, the original localized graph has no vertex outside the original atom list. -/
theorem localizedMancudeVertex_eq_false_of_not_lt
    (molecule : RawMolecule) (well : molecule.WellFormed)
    (atom : ℕ) (outside : ¬ atom < molecule.atomCount) :
    molecule.localizedMancudeVertex atom = false := by
  have doubleCount := molecule.incidentDoubleBondCount_eq_zero_of_not_lt well atom outside
  cases lookup : molecule.atomAt? atom with
  | none => simp [localizedMancudeVertex, doubleCount, lookup]
  | some spec =>
      have atomBound : atom < molecule.atomCount := by
        apply listGet?_eq_some_implies_lt molecule.atoms atom spec
        simpa [atomAt?] using lookup
      exact (outside atomBound).elim

/-- Atom charge and written-double incidence—the two facts used by localized vertex perception—are
unchanged by materialization at every natural index. -/
@[simp] theorem withExplicitHydrogens_localizedMancudeVertex
    (molecule : RawMolecule) (well : molecule.WellFormed) (atom : ℕ) :
    molecule.withExplicitHydrogens.localizedMancudeVertex atom =
      molecule.localizedMancudeVertex atom := by
  let result : HydrogenExpansionState :=
    (List.range molecule.atomCount).foldl (withExplicitHydrogensStep molecule)
      (initialHydrogenExpansionState molecule)
  have initialWell :
      (initialHydrogenExpansionState molecule).toRawMolecule.WellFormed := by
    intro bond member
    simpa [BondEndpointsOK] using well bond member
  have invariant : result.MaterializedValenceInvariant molecule := by
    exact fold_withExplicitHydrogensStep_preserves_materializedValenceInvariant molecule
      (List.range molecule.atomCount) (initialHydrogenExpansionState molecule)
      (by intro index member; exact List.mem_range.mp member)
      (initialHydrogenExpansionState_shapeInvariant molecule) initialWell
      (initialHydrogenExpansionState_materializedValenceInvariant molecule)
  by_cases originalBound : atom < molecule.atomCount
  · obtain ⟨source, sourceLookup⟩ :=
      listGet?_exists_of_lt molecule.atoms atom originalBound
    have sourceLookupAt : molecule.atomAt? atom = some source := by
      simpa [atomAt?] using sourceLookup
    have resultLookup := invariant.originalAtom atom source sourceLookupAt
    have expandedLookup :
        molecule.withExplicitHydrogens.atomAt? atom = some (materializedAtomSpec source) := by
      simpa [withExplicitHydrogens, result, withExactWrittenNeighbors, atomAt?] using resultLookup
    simp [localizedMancudeVertex, sourceLookupAt, expandedLookup]
  · have originalFalse :=
      molecule.localizedMancudeVertex_eq_false_of_not_lt well atom originalBound
    rw [originalFalse]
    have originalDoubleZero :=
      molecule.incidentDoubleBondCount_eq_zero_of_not_lt well atom originalBound
    have expandedDoubleZero :
        molecule.withExplicitHydrogens.incidentDoubleBondCount atom = 0 := by
      simpa using originalDoubleZero
    cases expandedLookup : molecule.withExplicitHydrogens.atomAt? atom with
    | none => simp [localizedMancudeVertex, expandedDoubleZero, expandedLookup]
    | some expandedAtom =>
        have resultLookup : result.toRawMolecule.atomAt? atom = some expandedAtom := by
          simpa [withExplicitHydrogens, result, withExactWrittenNeighbors, atomAt?] using
            expandedLookup
        obtain ⟨atomIdentity, _incident⟩ :=
          invariant.freshAtom atom expandedAtom (Nat.le_of_not_gt originalBound) resultLookup
        subst expandedAtom
        simp [localizedMancudeVertex, expandedDoubleZero, expandedLookup, AtomSpec.aliphatic]

/-- Candidate-edge projection stated against the original molecule's vertex predicate. -/
private def mancudeCandidateRecordFor
    (molecule : RawMolecule) (bond : RawBond) : Option (ℕ × ℕ) :=
  if (bond.kind.order == 1 || bond.kind.order == 2) &&
      molecule.localizedMancudeVertex bond.source &&
      molecule.localizedMancudeVertex bond.target then
    some (bond.source, bond.target)
  else
    none

/-- A single expansion step leaves the original localized-candidate projection exactly unchanged,
including list order. Every inserted single bond ends at an index outside the original atom list,
where the original localized-vertex predicate is false. -/
private theorem withExplicitHydrogensStep_mancudeCandidateProjection
    (molecule : RawMolecule) (well : molecule.WellFormed)
    (state : HydrogenExpansionState) (shape : state.ShapeInvariant molecule)
    (index : ℕ) :
    (withExplicitHydrogensStep molecule state index).2.1.filterMap
        (mancudeCandidateRecordFor molecule) =
      state.2.1.filterMap (mancudeCandidateRecordFor molecule) := by
  by_cases zero : molecule.hydrogenCountAt index == 0
  · simp [withExplicitHydrogensStep, zero]
  · let count := molecule.hydrogenCountAt index
    let base := state.1.length
    let hydrogenIds := (List.range count).map fun offset => base + offset
    let newBonds := hydrogenIds.map fun hydrogen =>
      { source := index, target := hydrogen, kind := ParsedBondKind.single : RawBond }
    have invisible :
        ∀ bond ∈ newBonds, mancudeCandidateRecordFor molecule bond = none := by
      intro bond member
      rcases List.mem_map.mp member with ⟨hydrogen, hydrogenMember, rfl⟩
      have hydrogenBounds := freshHydrogenId_bounds base count hydrogen (by
        simpa [hydrogenIds] using hydrogenMember)
      have outside : ¬ hydrogen < molecule.atomCount := by
        have originalAtoms : molecule.atomCount ≤ base := by
          simpa [base] using shape.originalAtoms
        omega
      have targetFalse :=
        molecule.localizedMancudeVertex_eq_false_of_not_lt well hydrogen outside
      simp [mancudeCandidateRecordFor, ParsedBondKind.order, targetFalse]
    have projected := spliceHydrogenBonds_filterMap (molecule.introductionPredecessors[index]?) state.2.1 index newBonds
      (mancudeCandidateRecordFor molecule) invisible
    simpa [withExplicitHydrogensStep, zero, count, base, hydrogenIds, newBonds] using projected

private theorem fold_withExplicitHydrogensStep_mancudeCandidateProjection
    (molecule : RawMolecule) (well : molecule.WellFormed)
    (indices : List ℕ) (state : HydrogenExpansionState)
    (shape : state.ShapeInvariant molecule) :
    (indices.foldl (withExplicitHydrogensStep molecule) state).2.1.filterMap
        (mancudeCandidateRecordFor molecule) =
      state.2.1.filterMap (mancudeCandidateRecordFor molecule) := by
  induction indices generalizing state with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      have nextShape :=
        withExplicitHydrogensStep_preserves_shapeInvariant molecule state index shape
      rw [List.foldl_cons,
        inductionHypothesis (withExplicitHydrogensStep molecule state index) nextShape]
      exact withExplicitHydrogensStep_mancudeCandidateProjection
        molecule well state shape index

private theorem withExplicitHydrogens_mancudeCandidateProjection
    (molecule : RawMolecule) (well : molecule.WellFormed) :
    molecule.withExplicitHydrogens.bonds.filterMap (mancudeCandidateRecordFor molecule) =
      molecule.bonds.filterMap (mancudeCandidateRecordFor molecule) := by
  have folded := fold_withExplicitHydrogensStep_mancudeCandidateProjection molecule well
    (List.range molecule.atomCount) (initialHydrogenExpansionState molecule)
    (initialHydrogenExpansionState_shapeInvariant molecule)
  simpa [withExplicitHydrogens, initialHydrogenExpansionState,
    HydrogenExpansionState.toRawMolecule] using folded

/-- The complete ordered candidate edge list is invariant under hydrogen materialization. -/
@[simp] theorem withExplicitHydrogens_localizedMancudeCandidateEdges
    (molecule : RawMolecule) (well : molecule.WellFormed) :
    molecule.withExplicitHydrogens.localizedMancudeCandidateEdges =
      molecule.localizedMancudeCandidateEdges := by
  unfold localizedMancudeCandidateEdges
  calc
    molecule.withExplicitHydrogens.bonds.filterMap
          (fun bond =>
            if (bond.kind.order == 1 || bond.kind.order == 2) &&
                molecule.withExplicitHydrogens.localizedMancudeVertex bond.source &&
                molecule.withExplicitHydrogens.localizedMancudeVertex bond.target then
              some (bond.source, bond.target)
            else none) =
        molecule.withExplicitHydrogens.bonds.filterMap
          (mancudeCandidateRecordFor molecule) := by
            apply List.filterMap_congr
            intro bond _member
            simp only [mancudeCandidateRecordFor]
            rw [molecule.withExplicitHydrogens_localizedMancudeVertex well bond.source,
              molecule.withExplicitHydrogens_localizedMancudeVertex well bond.target]
    _ = molecule.bonds.filterMap (mancudeCandidateRecordFor molecule) :=
      withExplicitHydrogens_mancudeCandidateProjection molecule well
    _ = molecule.bonds.filterMap
          (fun bond =>
            if (bond.kind.order == 1 || bond.kind.order == 2) &&
                molecule.localizedMancudeVertex bond.source &&
                molecule.localizedMancudeVertex bond.target then
              some (bond.source, bond.target)
            else none) := rfl

/-- Since bridge removal is a pure function of the ordered candidate list, the final localized
Mancude ring-edge list is exactly the original list. -/
@[simp] theorem withExplicitHydrogens_localizedMancudeEdges
    (molecule : RawMolecule) (well : molecule.WellFormed) :
    molecule.withExplicitHydrogens.localizedMancudeEdges =
      molecule.localizedMancudeEdges := by
  simp [localizedMancudeEdges,
    molecule.withExplicitHydrogens_localizedMancudeCandidateEdges well]

/-- Every pre-existing raw bond record remains present after one materialization step. -/
private theorem withExplicitHydrogensStep_oldBond_mem
    (molecule : RawMolecule) (state : HydrogenExpansionState) (index : ℕ)
    (bond : RawBond) (member : bond ∈ state.2.1) :
    bond ∈ (withExplicitHydrogensStep molecule state index).2.1 := by
  by_cases zero : molecule.hydrogenCountAt index == 0
  · simpa [withExplicitHydrogensStep, zero] using member
  · let count := molecule.hydrogenCountAt index
    let base := state.1.length
    let hydrogenIds := (List.range count).map fun offset => base + offset
    let newBonds := hydrogenIds.map fun hydrogen =>
      { source := index, target := hydrogen, kind := ParsedBondKind.single : RawBond }
    have permuted :
        (spliceHydrogenBondsWithPredecessor (molecule.introductionPredecessors[index]?) state.2.1 index newBonds).Perm (state.2.1 ++ newBonds) :=
      spliceHydrogenBondsWithPredecessor_perm _ _ _ _
    have appended : bond ∈ state.2.1 ++ newBonds := List.mem_append_left _ member
    have spliced := permuted.mem_iff.mpr appended
    simpa [withExplicitHydrogensStep, zero, count, base, hydrogenIds, newBonds] using spliced

private theorem fold_withExplicitHydrogensStep_oldBond_mem
    (molecule : RawMolecule) (indices : List ℕ) (state : HydrogenExpansionState)
    (bond : RawBond) (member : bond ∈ state.2.1) :
    bond ∈ (indices.foldl (withExplicitHydrogensStep molecule) state).2.1 := by
  induction indices generalizing state with
  | nil => exact member
  | cons index rest inductionHypothesis =>
      exact inductionHypothesis (withExplicitHydrogensStep molecule state index)
        (withExplicitHydrogensStep_oldBond_mem molecule state index bond member)

theorem withExplicitHydrogens_oldBond_mem
    (molecule : RawMolecule) (bond : RawBond) (member : bond ∈ molecule.bonds) :
    bond ∈ molecule.withExplicitHydrogens.bonds := by
  have folded := fold_withExplicitHydrogensStep_oldBond_mem molecule
    (List.range molecule.atomCount) (initialHydrogenExpansionState molecule) bond (by
      simpa [initialHydrogenExpansionState] using member)
  simpa [withExplicitHydrogens, HydrogenExpansionState.toRawMolecule] using folded

/-- On every localized Mancude edge, the exact numeric bond order is unchanged. The witness record
is an original candidate record, remains in the materialized list, and uniqueness identifies the
same order on both sides. -/
theorem withExplicitHydrogens_bondOrder_eq_of_mem_localizedMancudeEdges
    (molecule : RawMolecule) (admitted : molecule.StereochemicalAdmissible)
    {edge : ℕ × ℕ} (member : edge ∈ molecule.localizedMancudeEdges) :
    molecule.withExplicitHydrogens.bondOrder edge.1 edge.2 =
      molecule.bondOrder edge.1 edge.2 := by
  have candidateMember : edge ∈ molecule.localizedMancudeCandidateEdges :=
    (List.mem_filter.mp member).1
  unfold localizedMancudeCandidateEdges at candidateMember
  rw [List.mem_filterMap] at candidateMember
  obtain ⟨bond, bondMember, output⟩ := candidateMember
  by_cases condition :
      ((bond.kind.order == 1 || bond.kind.order == 2) &&
        molecule.localizedMancudeVertex bond.source &&
        molecule.localizedMancudeVertex bond.target) = true
  · have edgeIdentity : (bond.source, bond.target) = edge := by
      have someIdentity : some (bond.source, bond.target) = some edge := by
        simpa [condition] using output
      exact Option.some.inj someIdentity
    subst edge
    have connects : bond.connects bond.source bond.target = true := by
      simp [RawBond.connects]
    have expandedMember := molecule.withExplicitHydrogens_oldBond_mem bond bondMember
    have expandedAdmitted :=
      molecule.withExplicitHydrogens_preserves_stereochemicalAdmissible admitted
    rw [molecule.withExplicitHydrogens.bondOrder_eq_kind_of_mem_connects
        expandedAdmitted.1.1 expandedAdmitted.1.2 expandedMember connects,
      molecule.bondOrder_eq_kind_of_mem_connects
        admitted.1.1 admitted.1.2 bondMember connects]
  · simp [condition] at output

/-- An atom absent from every edge remains an isolated singleton under the finite component walk. -/
private theorem edgeComponent_singleton_of_no_incident
    (edges : List (ℕ × ℕ)) (atom fuel : ℕ)
    (noIncident : ∀ edge ∈ edges, edge.1 ≠ atom ∧ edge.2 ≠ atom) :
    edgeComponent edges fuel [atom] [atom] = [atom] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      have noNeighbors :
          edges.filterMap (fun edge =>
            if edge.1 = atom then some edge.2
            else if edge.2 = atom then some edge.1
            else none) = [] := by
        apply filterMap_eq_nil_of_forall_none
        intro edge member
        have separated := noIncident edge member
        simp [separated.1, separated.2]
      simp [edgeComponent, noNeighbors]
      cases fuel <;> rfl

/-- Every freshly appended hydrogen index has an empty localized component. -/
theorem withExplicitHydrogens_localizedMancudeComponentEdges_eq_nil_of_not_lt
    (molecule : RawMolecule) (well : molecule.WellFormed)
    (atom : ℕ) (outside : ¬ atom < molecule.atomCount) :
    molecule.withExplicitHydrogens.localizedMancudeComponentEdges atom = [] := by
  have edgesIdentity := molecule.withExplicitHydrogens_localizedMancudeEdges well
  have noIncident :
      ∀ edge ∈ molecule.localizedMancudeEdges,
        edge.1 ≠ atom ∧ edge.2 ≠ atom := by
    intro edge member
    have bounds := molecule.endpoints_lt_of_mem_localizedMancudeEdges well member
    have atomLower : molecule.atomCount ≤ atom := Nat.le_of_not_gt outside
    exact ⟨Nat.ne_of_lt (lt_of_lt_of_le bounds.1 atomLower),
      Nat.ne_of_lt (lt_of_lt_of_le bounds.2 atomLower)⟩
  have verticesIdentity :
      molecule.withExplicitHydrogens.localizedMancudeComponentVertices atom = [atom] := by
    unfold localizedMancudeComponentVertices
    rw [edgesIdentity]
    exact edgeComponent_singleton_of_no_incident molecule.localizedMancudeEdges atom
      (molecule.localizedMancudeEdges.length + 1) noIncident
  unfold localizedMancudeComponentEdges
  rw [verticesIdentity, edgesIdentity]
  apply filter_eq_nil_of_forall_false
  intro edge member
  have separated := noIncident edge member
  simp [separated.1, separated.2]

/-- Materializing inline and implied ordinary hydrogens preserves the independent localized
Mancude/Kekulé admissibility condition on every stereochemically admitted finite raw molecule. -/
theorem withExplicitHydrogens_preserves_localizedMancudeKekuleAdmissible
    (molecule : RawMolecule) (admitted : molecule.StereochemicalAdmissible)
    (kekule : LocalizedMancudeKekuleAdmissible molecule) :
    LocalizedMancudeKekuleAdmissible molecule.withExplicitHydrogens := by
  intro attached
  by_cases originalBound : attached.val < molecule.atomCount
  · let originalAttached : Fin molecule.atomCount := ⟨attached.val, originalBound⟩
    have edgesIdentity := molecule.withExplicitHydrogens_localizedMancudeEdges admitted.1.1
    have componentIdentity :
        molecule.withExplicitHydrogens.localizedMancudeComponentEdges attached.val =
          molecule.localizedMancudeComponentEdges originalAttached.val := by
      simp [localizedMancudeComponentEdges, localizedMancudeComponentVertices, edgesIdentity,
        originalAttached]
    have writtenIdentity :
        (molecule.withExplicitHydrogens.localizedMancudeComponentEdges attached.val).filter
            (fun edge => molecule.withExplicitHydrogens.bondOrder edge.1 edge.2 == 2) =
          (molecule.localizedMancudeComponentEdges originalAttached.val).filter
            (fun edge => molecule.bondOrder edge.1 edge.2 == 2) := by
      rw [componentIdentity]
      apply List.filter_congr
      intro edge edgeMember
      have localizedMember : edge ∈ molecule.localizedMancudeEdges := by
        unfold localizedMancudeComponentEdges at edgeMember
        exact (List.mem_filter.mp edgeMember).1
      rw [molecule.withExplicitHydrogens_bondOrder_eq_of_mem_localizedMancudeEdges
        admitted localizedMember]
    change IsMaximumMancudeEdgeMatching
      ((molecule.withExplicitHydrogens.localizedMancudeComponentEdges attached.val).filter
        (fun edge => molecule.withExplicitHydrogens.bondOrder edge.1 edge.2 == 2))
      (molecule.withExplicitHydrogens.localizedMancudeComponentEdges attached.val)
    rw [writtenIdentity, componentIdentity]
    exact kekule originalAttached
  · have componentEmpty :=
      molecule.withExplicitHydrogens_localizedMancudeComponentEdges_eq_nil_of_not_lt
        admitted.1.1 attached.val originalBound
    change IsMaximumMancudeEdgeMatching
      ((molecule.withExplicitHydrogens.localizedMancudeComponentEdges attached.val).filter
        (fun edge => molecule.withExplicitHydrogens.bondOrder edge.1 edge.2 == 2))
      (molecule.withExplicitHydrogens.localizedMancudeComponentEdges attached.val)
    rw [componentEmpty]
    simp [IsMaximumMancudeEdgeMatching, IsMancudeEdgeMatching]

end RawMolecule

end

end TetraStereo.OneCenter
