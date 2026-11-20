import TetraStereo.OneCenter.LocalizedChemicalRingOrientationRecorded
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Where `NoTransientOnlyLabels` fails: disagreeing eligible references

`NoTransientOnlyLabels` is not a harmless technicality. At an occurrence whose eligible
references read letters that disagree (under either geometry), the no-context consensus refuses
while each inherited single-reference evaluation still yields a descriptor
(`noTransientOnlyLabels_fails_of_disagreement`). Such an occurrence carries labels that the root
state never records but that inner marked stages of its ancestors consume. This pins the exact
policy-level obstruction to the orientation induction and identifies the smallest conceivable
repair (refuse the inherited single-reference evaluation whenever the local consensus refuses),
which is a production-policy decision and is not made here.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingOrientationDisagreement

open LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingOrientationContexts LocalizedChemicalRingOrientationResidue
open LocalizedChemicalRingOrientationRecorded
open LocalizedMarkedOperationEvaluator (Operations markedReading? underWith)
open LocalizedMarkedReachableConfigurations
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? consensus appendFacts? mirror
  caseFromMirror? eligibleOf strict consistent)

theorem caseFromMirror?_some_some_ne_none (a b : RS) : caseFromMirror? (some a) (some b) ≠ none := by
  simp [caseFromMirror?]

section Step

variable (mol : RawMolecule) (ops : Operations)

/-- The no-context descriptor refuses as soon as two eligible references read different letters
under the original geometry. -/
theorem descriptor_none_of_disagreement (depth : Nat) (geom : Geometry)
    (node : RawMolecule.CanonicalBranchNode) (atoms sorted : List Nat)
    (adjacent : List (Option Ordering)) (frame : frameAtoms? mol node = some atoms)
    (ordered : ops.ordinary [] node = some (sorted, adjacent)) (nodup : atoms.Nodup)
    (consistentOrder : consistent adjacent = true) (tied : strict adjacent = false)
    (m₁ m₂ : Nat) (eligible₁ : m₁ ∈ eligibleOf atoms sorted adjacent)
    (eligible₂ : m₂ ∈ eligibleOf atoms sorted adjacent) (L₁ L₂ : RS) (ne : L₁ ≠ L₂)
    (read₁ : ((appendFacts? [] (underWith mol ops geom [] node
        (LocalizedMarkedOperationEvaluator.facts mol ops depth) m₁)).bind fun temp =>
          markedReading? mol ops geom temp node m₁) = some L₁)
    (read₂ : ((appendFacts? [] (underWith mol ops geom [] node
        (LocalizedMarkedOperationEvaluator.facts mol ops depth) m₂)).bind fun temp =>
          markedReading? mol ops geom temp node m₂) = some L₂) :
    LocalizedMarkedOperationEvaluator.descriptor? mol ops depth geom [] none node = none := by
  unfold LocalizedMarkedOperationEvaluator.descriptor? LocalizedMarkedOperationEvaluator.descriptorWith?
    LocalizedMarkedOperationEvaluator.rawWith?
  rw [rawStep_none_consensus mol ops geom [] node _ atoms sorted adjacent frame ordered nodup
    consistentOrder tied]
  have refused : consensus ((eligibleOf atoms sorted adjacent).map fun r =>
      (appendFacts? [] (underWith mol ops geom [] node
        (LocalizedMarkedOperationEvaluator.facts mol ops depth) r)).bind fun temp =>
          markedReading? mol ops geom temp node r) = none := by
    cases result : consensus _ with
    | none => rfl
    | some v =>
        have all := ((consensus_eq_some_iff _ _).mp result).2
        have h₁ := all _ (List.mem_map_of_mem eligible₁)
        have h₂ := all _ (List.mem_map_of_mem eligible₂)
        simp only at h₁ h₂
        rw [read₁] at h₁
        rw [read₂] at h₂
        exact absurd ((Option.some.inj h₁).trans (Option.some.inj h₂).symm) ne
  rw [refused]
  rfl

/-- An inherited eligible reference still yields a descriptor when its two readings succeed. -/
theorem descriptor_some_of_single (depth : Nat) (geom : Geometry)
    (node : RawMolecule.CanonicalBranchNode) (atoms sorted : List Nat)
    (adjacent : List (Option Ordering)) (frame : frameAtoms? mol node = some atoms)
    (ordered : ops.ordinary [] node = some (sorted, adjacent)) (nodup : atoms.Nodup)
    (consistentOrder : consistent adjacent = true) (tied : strict adjacent = false)
    (m : Nat) (present : m ∈ atoms) (L L' : RS)
    (read : ((appendFacts? [] (underWith mol ops geom [] node
        (LocalizedMarkedOperationEvaluator.facts mol ops depth) m)).bind fun temp =>
          markedReading? mol ops geom temp node m) = some L)
    (readMirror : ((appendFacts? [] (underWith mol ops (mirror geom) [] node
        (LocalizedMarkedOperationEvaluator.facts mol ops depth) m)).bind fun temp =>
          markedReading? mol ops (mirror geom) temp node m) = some L') :
    LocalizedMarkedOperationEvaluator.descriptor? mol ops depth geom [] (some m) node ≠ none := by
  unfold LocalizedMarkedOperationEvaluator.descriptor? LocalizedMarkedOperationEvaluator.descriptorWith?
    LocalizedMarkedOperationEvaluator.rawWith?
  rw [rawStep_ctx_adjacent mol ops geom [] m node _ atoms sorted adjacent frame ordered nodup
    consistentOrder tied present,
    rawStep_ctx_adjacent mol ops (mirror geom) [] m node _ atoms sorted adjacent frame ordered nodup
    consistentOrder tied present, read, readMirror]
  exact caseFromMirror?_some_some_ne_none L L'

end Step

/-- **`NoTransientOnlyLabels` fails at any reached occurrence whose eligible references disagree
while some inherited eligible reference reads under both geometries.** -/
theorem noTransientOnlyLabels_fails_of_disagreement (input : CertifiedLocalizedCIPInput)
    (mol : RawMolecule) (geom : Geometry) (depth : Nat) (node : RawMolecule.CanonicalBranchNode)
    (reached : Reached mol node) (atoms sorted : List Nat) (adjacent : List (Option Ordering))
    (frame : frameAtoms? mol node = some atoms)
    (ordered : (sparseOperations input mol).ordinary [] node = some (sorted, adjacent))
    (nodup : atoms.Nodup) (consistentOrder : consistent adjacent = true)
    (tied : strict adjacent = false) (m₁ m₂ : Nat) (eligible₁ : m₁ ∈ eligibleOf atoms sorted adjacent)
    (eligible₂ : m₂ ∈ eligibleOf atoms sorted adjacent) (present₁ : m₁ ∈ atoms) (L₁ L₂ L' : RS)
    (ne : L₁ ≠ L₂)
    (read₁ : ((appendFacts? [] (underWith mol (sparseOperations input mol) geom [] node
        (LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol) depth) m₁)).bind
          fun temp => markedReading? mol (sparseOperations input mol) geom temp node m₁) = some L₁)
    (read₂ : ((appendFacts? [] (underWith mol (sparseOperations input mol) geom [] node
        (LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol) depth) m₂)).bind
          fun temp => markedReading? mol (sparseOperations input mol) geom temp node m₂) = some L₂)
    (readMirror₁ : ((appendFacts? [] (underWith mol (sparseOperations input mol) (mirror geom) [] node
        (LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol) depth) m₁)).bind
          fun temp => markedReading? mol (sparseOperations input mol) (mirror geom) temp node m₁) =
            some L') :
    ¬ NoTransientOnlyLabels input mol geom := by
  intro property
  have refused := descriptor_none_of_disagreement mol (sparseOperations input mol) depth geom node
    atoms sorted adjacent frame ordered nodup consistentOrder tied m₁ m₂ eligible₁ eligible₂ L₁ L₂ ne
    read₁ read₂
  exact descriptor_some_of_single mol (sparseOperations input mol) depth geom node atoms sorted
    adjacent frame ordered nodup consistentOrder tied m₁ present₁ L₁ L' read₁ readMirror₁
    (property depth node reached (some m₁) refused)

end TetraStereo.OneCenter.LocalizedChemicalRingOrientationDisagreement

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationDisagreement.descriptor_none_of_disagreement
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationDisagreement.descriptor_some_of_single
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationDisagreement.noTransientOnlyLabels_fails_of_disagreement
