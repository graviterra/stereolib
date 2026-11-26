import TetraStereo.Engine.RingTerminalLigandOrder

/-! Reader-independent pyramidal decisions from physical two-shell prefixes
and the proved terminal duplicate-origin tie-break. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingTerminalPyramid
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Reader Labels)
open RingPyramidalSource (Directions slots atomId)
open RingPyramidalTwoShell (direction)
open RingRetainedChemicalPreorder (keyFor read_key orderWord)
open RingTerminalLigandOrder (rank rank_lt)
attribute [local instance] lexOrd
open private nodup_injective from TetraStereo.Engine.RingPyramidalSource
open private arm_eq from TetraStereo.Engine.RingPyramidalTwoShell

/-- A finite graph prefix and its terminal Rule 1b bonus, at an actual arm. -/
def weight {i : Input} {q : Site i} (d : Directions i q) (s : Fin 3) := rank (direction d s)

/-- The ranked physical ligand coordinates, with the centre representing the
lowest phantom; the result includes completed flat-frame refusals. -/
def reading {i : Input} {q : Site i} (a : i.certified.Atom) (d : Directions i q) : Option Labels :=
  (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
    ((RingStereoSiblingPass.order (weight d) slots).map (atomId d) ++ [a.val])).map
      fun h => (.chiral h,.chiral h.swap)

/-- No full constitutional tree or stereo reader is evaluated by this test. -/
def direct? (i : Input) (q : Site i) : Option (Option Labels) := do
  let a ← RingPyramidalPublication.focusP i q
  let d ← RingPyramidalEarly.directions? i q
  if [weight d 0,weight d 1,weight d 2].Nodup then some (reading a d) else none

/-- Injectivity supplies an exact hit, independently of a frozen stereo view. -/
theorem hit_of_injective {i : Input} {q : Site i} {a : i.certified.Atom}
    (selected : RingPyramidalPublication.focusP i q = some a) (d : Directions i q)
    (strict : Function.Injective (fun s => rank (direction d s))) :
    direct? i q = some (reading a d) := by
  have distinct := (nodup_injective (weight d)).mpr strict
  simp only [direct?,selected,RingPyramidalEarly.directions_of i q d,bind,Option.bind_some,if_pos distinct]

/-- Every hit is the ordinary local publication at every ready view. -/
theorem local_exact {i : Input} {q : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready q r) {v : Option Labels}
    (hit : direct? i q = some v) : RingPyramidalPublication.publish i q r = some v := by
  simp only [direct?,bind,Option.bind_eq_some_iff] at hit
  obtain ⟨a,selected,d,_,tail⟩ := hit
  split at tail <;> try contradiction
  rename_i distinct
  let cs (s : Fin 3) := keyFor (direction d s)
  have native (s : Fin 3) : RingRetainedChemicalTrace.key? i (d.arm s) = some (cs s) := by
    rw [arm_eq d s]
    exact read_key _
  have lower {s t : Fin 3} (lt : weight d s < weight d t) :
      orderWord (cs s) < orderWord (cs t) := rank_lt _ _ lt
  have diff := (nodup_injective (weight d)).mp distinct
  have strict : Function.Injective (fun s => orderWord (cs s)) := by
    intro s t eqn
    by_contra ne
    rcases lt_or_gt_of_ne (diff.ne ne) with lt | lt
    · exact (ne_of_lt (lower lt)) eqn
    · exact (ne_of_lt (lower lt)) eqn.symm
  have legal := RingStereoSiblingPass.legal_order (weight d) slots
  have size : (RingStereoSiblingPass.order (weight d) slots).length = 3 := legal.perm.length_eq
  obtain ⟨j,k,l,row⟩ := List.length_eq_three.mp size
  have nd : [j,k,l].Nodup := (row ▸ legal.perm).nodup_iff.mpr (by decide)
  have sorted : RingStereoSiblingPass.Legal (fun s => orderWord (cs s)) slots [j,k,l] := by
    refine ⟨row ▸ legal.perm, ?_⟩
    have desc := row ▸ legal.descending
    exact List.pairwise_map.mpr (((List.pairwise_map.mp desc).and nd).imp
      (fun h => le_of_lt (lower (lt_of_le_of_ne h.1 (diff.ne h.2.symm)))))
  simp only [RingPyramidalPublication.publish,selected]
  rw [RingPyramidalConstitution.pLabels_strict d ready a cs native strict j k l sorted]
  have result : reading a d = v := Option.some.inj tail
  rw [← result]
  simp only [reading,row,List.map_cons,List.map_nil,List.cons_append,List.nil_append]

/-- A hit is the actual chemical state, with no local-decision premise. -/
theorem sound {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {v : Option Labels} (hit : direct? i q = some v) :
    RingChemicalGraphProof.state i q = some v := by
  rw [RingChemicalGraphProof.state_eq]
  exact local_exact (RingChemicalGraphProof.ready geom q) hit

end TetraStereo.Engine.RingTerminalPyramid
assert_kernel_only TetraStereo.Engine.RingTerminalPyramid.local_exact
assert_kernel_only TetraStereo.Engine.RingTerminalPyramid.hit_of_injective
assert_kernel_only TetraStereo.Engine.RingTerminalPyramid.sound
