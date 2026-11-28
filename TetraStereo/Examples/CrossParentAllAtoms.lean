import TetraStereo.Examples.CrossParentPublicReport

/-! Complete requested-ID reports for the 41-atom cross-parent graph. -/
set_option autoImplicit false
namespace TetraStereo.Examples.CrossParentAllAtoms
open Engine OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingGroupedReport (origin)
open RingNestedActivePair (Labels)
open CrossParentDonorStore (molecule ligandRow cell)
open CrossParentClasses (hand measured nonflat)
open CrossParentRootOrder (rCount)
open CrossParentPublicRanking (rootFrame neighbors0)
open CrossParentPublicReport (outcome)
open RingWrittenPHReadings (geometry)
open private types pyramids incident from TetraStereo.Examples.CrossParentDonorStore
open private bound toAtom from TetraStereo.Engine.RingAtomicNeighborOrder
open private raw_nonflat from TetraStereo.Examples.CrossParentPublicReport
open private row? from TetraStereo.Engine.RingChemicalReport

private theorem size_bound {i : Input} (raw : i.molecule = molecule) (v : i.certified.Atom) :
    v.val < 41 := by have b := bound i v; rwa [raw] at b

private theorem inactive {i : Input} (raw : i.molecule = molecule) (v : i.certified.Atom)
    (nz : v.val ≠ 0) (off : ¬ (7 ≤ v.val ∧ v.val < 15)) :
    RingChemicalGraphProof.root i v = some none := by
  have size := size_bound raw v
  have gate : RingPyramidalPublication.phosphorus i v = false := by
    change (RingAtomicNeighborOrder.neutralPyramidal i.molecule v.val && _) = false
    rw [raw,pyramids ⟨v.val,size⟩]; rfl
  have skipped : ¬ RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) (origin i v) := by
    rintro ⟨_,b,current,on⟩
    obtain rfl : v = b := Option.some.inj current
    have four : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 4 := by
      simpa [RingPyramidalPublication.eligible,gate] using on
    rw [RingAtomicNeighborOrder.degree_eq,raw] at four
    have len := (RingStereoSiblingPass.legal_order (RingAtomicNeighborOrder.atomicNumber molecule)
      (incident v.val)).perm.length_eq
    exact (types ⟨v.val,size⟩ (len.symm.trans four)).elim nz off
  exact (RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i) v).trans
    ((RingChemicalGraphProof.state_eq i _).trans (RingChemicalGraphProof.skips i _ _ skipped))

def expectedRow? (x : SpatialConfiguration) (n : Nat) : Option (Nat × Option Labels) :=
  if n = 0 then (readback? (geometry x) rootFrame).map fun c =>
    (n,outcome (rCount (hand x) true false) (rCount (hand x) false false) c)
  else if hd : 7 ≤ n ∧ n < 15 then
    let h := hand x ⟨n-7,by omega⟩
    some (n,some (.chiral h,.chiral h.swap))
  else if n < 41 then some (n,none) else none

def expected? (x : SpatialConfiguration) (ids : List Nat) := ids.mapM (expectedRow? x)

private theorem closed : RingHydrogenCompletion.plan molecule = [] := by decide +kernel

theorem raw_agreement (i : Input) (raw : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (ids : List Nat) :
    RingHydrogenReport.fromRaw? molecule i.spatial ids = expected? i.spatial ids := by
  by_cases good : ids.all (· < 41) = true
  · let vs := ids.attach.map fun n => toAtom i n.val (by rw [raw]; exact of_decide_eq_true (List.all_eq_true.mp good _ n.property))
    have resolved : vs.map Fin.val = ids := by simp [vs,List.map_map,Function.comp_def,toAtom]
    have native := RingWrittenPHReadings.fromRaw_closed_report i (raw ▸ closed) geom vs
    rw [raw,resolved] at native
    rw [native,expected?,←resolved,List.mapM_map]
    apply RingFrameTransport.mapM_congr_mem
    intro v _
    by_cases zero : v.val = 0
    · obtain ⟨c,seen⟩ := Option.isSome_iff_exists.mp (raw_nonflat raw geom v rootFrame rfl (zero ▸ neighbors0))
      have signs (j : Fin 8) : measured i.spatial j = some (hand i.spatial j) := by
        obtain ⟨z,hz⟩ := Option.isSome_iff_exists.mp (nonflat raw geom j)
        simp [hand,hz]
      have root := CrossParentPublicReport.root raw geom v zero _ signs c seen
      simp [row?,expectedRow?,zero,root,seen]
    · by_cases tip : 7 ≤ v.val ∧ v.val < 15
      · let j : Fin 8 := ⟨v.val-7,by omega⟩
        have state := CrossParentClasses.public_leaf raw geom (origin i v) v j (by dsimp [j]; omega) rfl rfl
        have root : RingChemicalGraphProof.root i v = cell (hand i.spatial j) := (RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i) v).trans state
        simp [row?,expectedRow?,zero,tip,root,cell,j]
      · simp [row?,expectedRow?,zero,tip,size_bound raw v,inactive raw v zero tip]
  · have failed : RingMolecularReport.resolve i ids = none := by
      cases h : RingMolecularReport.resolve i ids with
      | none => rfl
      | some vs =>
        exfalso
        apply good
        rw [← (RingMolecularReport.resolve_iff ..).mp h]
        apply List.all_eq_true.mpr
        intro n hn
        obtain ⟨v,_,rfl⟩ := List.mem_map.mp hn
        exact decide_eq_true (size_bound raw v)
    have none : expected? i.spatial ids = none := by
      cases out : expected? i.spatial ids with
      | none => rfl
      | some rows =>
        exfalso
        apply good
        apply List.all_eq_true.mpr
        intro n hn
        obtain ⟨row,_,someRow⟩ := RingRetainedReferenceGroup.forInput out hn
        apply decide_eq_true
        by_contra! bad
        simp [expectedRow?,show n ≠ 0 by omega,show ¬ (7 ≤ n ∧ n < 15) by omega,show ¬ n < 41 by omega] at someRow
    have accepted := RingSpatialTransport.readmit i
    rw [raw] at accepted
    simp [RingHydrogenReport.fromRaw_closed_eq closed,RingChemicalReport.fromRaw?,accepted,failed,none]

end TetraStereo.Examples.CrossParentAllAtoms
assert_kernel_only TetraStereo.Examples.CrossParentAllAtoms.raw_agreement
