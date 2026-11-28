import TetraStereo.Examples.RingPhosphaneOxiraneReport
import TetraStereo.Engine.RingResidualPairDecision
import TetraStereo.Engine.RingObservedTreeMatch

/-! Determine the first priority difference between the two F/Cl phosphane arms
of the oxirane carbon from their signed coordinate readbacks. Atom 1 is the
left arm and atom 2 the right. Both can be flat independently. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace TetraStereo.Engine.RingUnmatchedStereoOrder
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingHydrogenSpelling
open PhosRootKey (reference frameZero)
open PhosphaneOxirane.Representatives (hand)
open RingLigandFirstDifference (Words Decomposes stages directions)
open RingResidualPairDecision (Verdict words Explains)
open private pick pick_exact explained_order from TetraStereo.Engine.RingResidualPairDecision
open RingFullPathEligibility (Key)
open RingFullPathTrialReadings (trialKey bitWord)
open RingSpatialTransport (atGeometry size)
attribute [local instance] lexOrd

/-- Ground priority of one phosphane arm: existence of a chiral auxiliary enters
Rule 4a. Its fixed-R reference bit depends on the geometry of comparison. -/
def ligandKey (rev : Bool) : Option RS → Key
  | none => PhosRootKey.absentPhosphorusKey
  | some h => PhosRootKey.phosphorusKey ((if rev then h.swap else h) == .R)

private theorem key_left (l r : Option RS) (rev : Bool) :
    PhosRootKey.Parameterized.keyWith (PhosRootKey.canonicalReader l r) rev (PhosRootKey.arm 0) =
      some (ligandKey rev l) := by
  rcases l with _ | ⟨_ | _⟩ <;> rcases r with _ | ⟨_ | _⟩ <;> cases rev <;> decide +kernel

private theorem key_right (l r : Option RS) (rev : Bool) :
    PhosRootKey.Parameterized.keyWith (PhosRootKey.canonicalReader l r) rev (PhosRootKey.arm 1) =
      some (ligandKey rev r) := by
  rcases l with _ | ⟨_ | _⟩ <;> rcases r with _ | ⟨_ | _⟩ <;> cases rev <;> decide +kernel

/-- An explicit physical explanation, with the comparison oriented from atom
1 to atom 2. An empty result means equality through all ordinary rules. -/
def determinantOrder (rev : Bool) (l r : Option RS) : Verdict :=
  match l,r with
  | none,none => .tie
  | some _,none => .left .rule4a
  | none,some _ => .right .rule4a
  | some a,some b =>
    if a = b then .tie
    else if (if rev then a.swap else a) = .R then .left .rule5 else .right .rule5

private theorem decomposed (rev : Bool) (h : Option RS) :
    Decomposes (ligandKey rev h) [] (words (ligandKey rev h) []) := by
  rcases h with _ | ⟨_ | _⟩ <;> cases rev <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

private theorem selected (rev : Bool) (l r : Option RS) :
    pick (directions (words (ligandKey rev l) []) (words (ligandKey rev r) [])) stages =
      determinantOrder rev l r := by
  rcases l with _ | ⟨_ | _⟩ <;> rcases r with _ | ⟨_ | _⟩ <;> cases rev <;> decide

def left (x : SpatialConfiguration) := hand x [5,6,0,1]
def right (x : SpatialConfiguration) := hand x [7,8,0,2]

abbrev moved (x : SpatialConfiguration) (full : x.positions.length = size reference) :=
  atGeometry reference x full

abbrev focus (x : SpatialConfiguration) (full : x.positions.length = size reference) :=
  RingGroupedReport.origin (moved x full) (PhosphaneOxirane.atom (moved x full) PhosRootKey.reference_molecule 0)

abbrev read (x : SpatialConfiguration) (full : x.positions.length = size reference) :=
  RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state (moved x full)) (focus x full)

def arm (x : SpatialConfiguration) (full : x.positions.length = size reference) (k : RingActivePairReport.Slot) :=
  RingStereoKeyCoordinates.cursor reference x full (RingGroupedCentre.cursor frameZero k)

/-- The two ordinary keys on the native frozen reader at C0 are computed from
the P determinants, for all admitted rational geometries and both passes. -/
theorem actual_keys (x : SpatialConfiguration) (full : x.positions.length = size reference)
    (valid : LocalizedChemicalRing.coordinatesAdmitted (moved x full) = true) (rev : Bool) :
    RingFullPathEligibility.key? (moved x full) (read x full) rev (arm x full 0) = some (ligandKey rev (left x)) ∧
    RingFullPathEligibility.key? (moved x full) (read x full) rev (arm x full 1) = some (ligandKey rev (right x)) := by
  have frozen := PhosphaneOxirane.frozen_c0 (moved x full) PhosRootKey.reference_molecule valid
  rw [RingWrittenPHReadings.inputGeometry_eq] at frozen
  have transport (k : RingActivePairReport.Slot) :=
    RingStereoKeyCoordinates.key_atGeometry reference x full
      (PhosRootKey.canonicalReader (left x) (right x)) (read x full)
      (fun q => by unfold read; rw [frozen]; rfl) rev (RingGroupedCentre.cursor frameZero k)
  constructor
  · refine (transport 0).trans ?_
    rw [PhosRootKey.Parameterized.keyWith_eq,PhosRootKey.cursor_eq]
    exact key_left _ _ _
  · refine (transport 1).trans ?_
    rw [PhosRootKey.Parameterized.keyWith_eq,PhosRootKey.cursor_eq]
    exact key_right _ _ _

/-- For the complete coordinate family the independent physical formula gives
the native first deciding rule, its direction, and the entire ordinary comparison. -/
theorem actual_order (x : SpatialConfiguration) (full : x.positions.length = size reference)
    (valid : LocalizedChemicalRing.coordinatesAdmitted (moved x full) = true) (rev : Bool) :
    ∃ a b : Key, ∃ u v : Words,
      RingFullPathEligibility.key? (moved x full) (read x full) rev (arm x full 0) = some a ∧
      RingFullPathEligibility.key? (moved x full) (read x full) rev (arm x full 1) = some b ∧
      Decomposes a [] u ∧ Decomposes b [] v ∧
      Explains (directions u v) stages (determinantOrder rev (left x) (right x)) ∧
      compare (trialKey a []) (trialKey b []) =
        (determinantOrder rev (left x) (right x)).order := by
  obtain ⟨a,b⟩ := actual_keys x full valid rev
  have witness := pick_exact (directions (words (ligandKey rev (left x)) [])
    (words (ligandKey rev (right x)) [])) stages
  rw [selected] at witness
  exact ⟨_,_,_,_,a,b,decomposed _ _,decomposed _ _,witness,
    (RingLigandFirstDifference.compare_trial_eq_scan (decomposed _ _) (decomposed _ _)).trans
      (explained_order witness)⟩

/-- Every pair of phosphorus outcomes is attained at either carbon hand
on an admitted coordinate table of the explicit molecule. -/
theorem realized (c : RS) (l r : Option RS) :
    ∃ x : SpatialConfiguration, ∃ full : x.positions.length = size reference,
      LocalizedChemicalRing.coordinatesAdmitted (moved x full) = true ∧
      hand x [1,2,3,4] = some c ∧ left x = l ∧ right x = r := by
  let x := PhosphaneOxirane.Representatives.representative c l r
  obtain ⟨len,hc,hl,hr,h4⟩ := PhosphaneOxirane.Representatives.representative_checks c l r
  let full : x.positions.length = size reference := len.trans PhosRootKey.reference_size.symm
  refine ⟨x,full,?_,hc,hl,hr⟩
  apply (PhosphaneOxirane.coordinates_iff (moved x full) PhosRootKey.reference_molecule).mpr
  exact ⟨by change (hand x [1,2,3,4]).isSome = true; rw [show hand x [1,2,3,4] = some c from hc]; rfl,h4⟩

private theorem key_injective (rev : Bool) : Function.Injective (ligandKey rev) := by
  intro l r h
  rcases l with _ | ⟨_ | _⟩ <;> rcases r with _ | ⟨_ | _⟩ <;> cases rev <;>
    first | rfl | exact False.elim ((by decide : _ ≠ _) h)

/-- Unequal signed P readbacks rule out every ordinary observed-tree exchange.
The result rules out even a correspondence supplied independently of the
canonical matching algorithm. -/
theorem no_exchange (x : SpatialConfiguration) (full : x.positions.length = size reference)
    (valid : LocalizedChemicalRing.coordinatesAdmitted (moved x full) = true)
    (different : left x ≠ right x)
    (fr : RingNestedActivePair.Frame (moved x full)
      (RingSpatialTransport.reindexSite reference x full (PhosRootKey.origin 0))) :
    ¬ Nonempty (RingObservedTreeMatch.Unmarked fr (read x full) 0 1) := by
  rintro ⟨e⟩
  have eqFocus : RingSpatialTransport.reindexSite reference x full (PhosRootKey.origin 0) =
      focus x full := RingSpatialTransport.reindex_origin reference x full _
  have ready : RingGroupedStereo.Ready
      (RingSpatialTransport.reindexSite reference x full (PhosRootKey.origin 0)) (read x full) := by
    rw [eqFocus]
    exact RingChemicalGraphProof.ready valid _
  have key := RingFullPathKeyTransport.key_transport e.carrier e.frozen ready ready false
    e.start (RingGroupedCentre.valid fr 0) (fr.direction 0).property.1
    (e.target.symm ▸ RingGroupedCentre.valid fr 1) (e.target.symm ▸ (fr.direction 1).property.1)
  rw [e.target] at key
  have slot (s : RingActivePairReport.Slot) : RingGroupedCentre.cursor fr s = arm x full s :=
    RingSpatialTransport.frame_cursor_eq reference x full frameZero fr s
  obtain ⟨hl,hr⟩ := actual_keys x full valid false
  rw [slot,slot,hl,hr] at key
  exact different (key_injective false (Option.some.inj key).symm)

end TetraStereo.Engine.RingUnmatchedStereoOrder
assert_kernel_only TetraStereo.Engine.RingUnmatchedStereoOrder.actual_keys
assert_kernel_only TetraStereo.Engine.RingUnmatchedStereoOrder.actual_order
assert_kernel_only TetraStereo.Engine.RingUnmatchedStereoOrder.no_exchange
assert_kernel_only TetraStereo.Engine.RingUnmatchedStereoOrder.realized
