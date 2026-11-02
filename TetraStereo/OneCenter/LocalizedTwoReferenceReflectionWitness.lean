import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.OneCenter.LocalizedCompoundUppercaseReflection
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Two-reference Rule-4b readings are not reflection-invariant in the actual compound comparator

P-92.1.3: "Properties associated with the first four Sequence Rules are reflection-invariant."
P-92.6 Example 6 is a pseudoasymmetric centre both of whose ligands carry **two** reference
descriptors; there Rule 4b reaches no decision and Rule 5 assigns `s`.

The actual compound Rules-4b/4c key (`LocalizedRerootCompoundRule4bcKey`) keeps the tied reference
population in the fixed normative order `[R, S]` and compares the two complete readings in that
order (`compareLocalizedRerootCompoundRule4bReadings`).  Under uppercase reflection the alternative
list stays `[R, S]` while the readings are **reversed**
(`buildLocalizedRerootRule4bcReadingsWithRead?_compoundUppercase_reverse`).  Consequently a ligand
whose R-reading and S-reading differ compares *strictly* against its own mirror image at Rule 4b.

This module exhibits that with keys assembled from the actual internal-node equations
(`stageLeaf`/`stageNode`, i.e. the production sort/merge at a constitutionally uniform skeleton).
The ligand skeleton is

* `L  = N[ A₁(R)[B₁(R)],  A₂(S)[B₂(R)] ]` and its mirror `L̄ = N[ A₁(S)[B₁(S)], A₂(R)[B₂(S)] ]`,

a nitrogen branching atom (not a detected centre) carrying two constitutionally identical arms
whose nearest centres are an exact `R/S` tie, so P-92.5.2.1(c) selects both references.

Scope: the keys are constructed, not produced by an actual molecular build; the chemical claim is
the P-92.1.3 reflection-invariance requirement.  A molecular realisation of the same skeleton is
recorded separately.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput)

open LocalizedCumulativeRule45Stage

/-- The arm `N[ A₁(R)[B₁(R)], A₂(S)[B₂(R)] ]` at a cumulative stage. -/
def twoRefArm (stage : LocalizedCumulativeRule45Stage) : input.LocalizedRerootCumulativeRule45Key :=
  input.stageNode stage none
    [input.stageNode stage labelR [input.stageLeaf stage labelR],
     input.stageNode stage labelS [input.stageLeaf stage labelR]]

/-- Its mirror image `N[ A₁(S)[B₁(S)], A₂(R)[B₂(S)] ]`. -/
def twoRefArmMirror (stage : LocalizedCumulativeRule45Stage) : input.LocalizedRerootCumulativeRule45Key :=
  input.stageNode stage none
    [input.stageNode stage labelS [input.stageLeaf stage labelS],
     input.stageNode stage labelR [input.stageLeaf stage labelS]]

/-- The actual compound key assembled exactly as `buildLocalizedRerootCompoundRule4bcKey?` does
from the stage keys: Rule-4a key, P-92 reference selection, count priority and one reading per
alternative in the normative order. -/
def twoRefCompound (arm : LocalizedCumulativeRule45Stage → input.LocalizedRerootCumulativeRule45Key) :
    input.LocalizedRerootCompoundRule4bcKey :=
  let references := localizedRule4bReferencesFromRankedLabels (arm .rule4a).rankedLabels
  { rule4aKey := arm .rule4a
    references := references
    referenceCountPriority := constitutionalRule4bReferenceCountPriority references
    readings := (localizedRule4bcReferenceAlternatives references).map fun
      | none => { reference? := none, rule4bKey := arm .rule4a, rule4cKey := arm .rule4cNoReference }
      | some r => { reference? := some r, rule4bKey := arm (.rule4b r), rule4cKey := arm (.rule4c r) } }

/-- Both arms select the tied population `[R, S]`. -/
theorem twoRefArm_references :
    localizedRule4bReferencesFromRankedLabels (input.twoRefArm .rule4a).rankedLabels = [RS.R, RS.S] ∧
      localizedRule4bReferencesFromRankedLabels (input.twoRefArmMirror .rule4a).rankedLabels =
        [RS.R, RS.S] := by
  constructor <;> rfl

/-- The arms tie under the complete Rule-4a key (so the compound comparison reaches Rule 4b). -/
theorem twoRefArm_rule4a_tie :
    input.compareLocalizedRerootCumulativeRule45Keys (input.twoRefArm .rule4a)
      (input.twoRefArmMirror .rule4a) = .eq := by
  rfl

/-- The mirror arm's R-reading table is the arm's S-reading table and vice versa. -/
theorem twoRefArm_mirror_readings_swap :
    (input.twoRefArmMirror (.rule4b RS.R)).descriptor = (input.twoRefArm (.rule4b RS.S)).descriptor ∧
      (input.twoRefArmMirror (.rule4b RS.S)).descriptor = (input.twoRefArm (.rule4b RS.R)).descriptor := by
  constructor <;> rfl

/-- The arm's own two readings differ. -/
theorem twoRefArm_readings_differ :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      (input.twoRefArm (.rule4b RS.R)).descriptor (input.twoRefArm (.rule4b RS.S)).descriptor = .gt := by
  rfl

/-- **The actual compound Rules-4b/4c comparator separates the arm from its mirror image.**
Rule 4a ties, the reference counts tie, and the first normative reading (R against R) is strict.
Rule 4b therefore decides between two enantiomorphic ligands, contradicting the reflection
invariance of Rules 1--4 (P-92.1.3) and the Rule-5 treatment of P-92.6 Example 6. -/
theorem twoRefCompound_mirror_strict :
    input.compareLocalizedRerootCompoundRule4bcKeys
      (input.twoRefCompound input.twoRefArm) (input.twoRefCompound input.twoRefArmMirror) = .gt := by
  rfl

theorem twoRefCompound_mirror_not_tie :
    input.compareLocalizedRerootCompoundRule4bcKeys
      (input.twoRefCompound input.twoRefArm) (input.twoRefCompound input.twoRefArmMirror) ≠ .eq := by
  rw [twoRefCompound_mirror_strict]; decide

/-! ## The outcome-sorted alternative order ties

The public framed/legacy path (`SmilesTetrahedral.rankRule4bReferences?`) orders a ligand's two
alternatives by their own complete reading before comparison.  The same policy applied to the
compound key restores the tie. -/

/-- Order the (at most two) alternatives of a compound key by their complete Rule-4b reading,
better reading first; one- and zero-alternative keys are unchanged. -/
def outcomeSortReadings (key : input.LocalizedRerootCompoundRule4bcKey) :
    input.LocalizedRerootCompoundRule4bcKey :=
  { key with readings :=
      match key.readings with
      | [first, second] =>
          if input.compareLocalizedRerootRule4bcReadingsByRule4b first second = .lt then
            [second, first]
          else [first, second]
      | readings => readings }

theorem twoRefCompound_outcomeSorted_mirror_tie :
    input.compareLocalizedRerootCompoundRule4bcKeys
      (input.outcomeSortReadings (input.twoRefCompound input.twoRefArm))
      (input.outcomeSortReadings (input.twoRefCompound input.twoRefArmMirror)) = .eq := by
  rfl

/-! ## Controls -/

/-- A single-reference arm (`N[ A₁(R)[B₁(R)], X ]`, X unlabeled) ties with its mirror image. -/
def oneRefArm (stage : LocalizedCumulativeRule45Stage) : input.LocalizedRerootCumulativeRule45Key :=
  input.stageNode stage none
    [input.stageNode stage labelR [input.stageLeaf stage labelR], input.stageLeaf stage none]

def oneRefArmMirror (stage : LocalizedCumulativeRule45Stage) : input.LocalizedRerootCumulativeRule45Key :=
  input.stageNode stage none
    [input.stageNode stage labelS [input.stageLeaf stage labelS], input.stageLeaf stage none]

theorem oneRefCompound_mirror_tie :
    input.compareLocalizedRerootCompoundRule4bcKeys
      (input.twoRefCompound input.oneRefArm) (input.twoRefCompound input.oneRefArmMirror) = .eq := by
  rfl

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.twoRefArm_references
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.twoRefArm_rule4a_tie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.twoRefArm_mirror_readings_swap
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.twoRefArm_readings_differ
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.twoRefCompound_mirror_strict
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.twoRefCompound_mirror_not_tie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.twoRefCompound_outcomeSorted_mirror_tie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oneRefCompound_mirror_tie
