import TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
Reference-context equality for the actual inherited-fallback recursion. The child continuation
is shared by both outer contexts; each selected reference still receives its own recursively
generated child facts. Equal inherited readings therefore suffice even when one reference
belongs to the local frame and the other does not.

These are compositional lemmas. They do not assert equality of the inherited readings or
chemical completeness; the actual key and symmetry arguments must supply those facts.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingContextIndependence

open LocalizedMarkedOperationEvaluator (Operations underWith)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? strict consistent mirror
  flatMap_congr_mem)
open LocalizedPhysicalMarkedDistantReference (inheritedRead? chooseInherited)
open LocalizedChemicalRingSenseTransport (factsWith descriptorWith)

abbrev Node := RawMolecule.CanonicalBranchNode

/-- Equal optional inherited readings yield equal fallback steps, regardless of whether
the two reference atoms occur in the current frame. The continuation is held fixed. -/
theorem rawStep_eq_of_read_eq (mol : RawMolecule) (ops : Operations)
    (geom : Geometry) (state : OccurrenceAuxState) (node : Node)
    (under : Nat → OccurrenceAuxState) (first second : Nat)
    (same : inheritedRead? mol ops geom state node under first =
      inheritedRead? mol ops geom state node under second) :
    LocalizedChemicalRingInheritedFallback.rawStep? mol ops geom state (some first) node under =
      LocalizedChemicalRingInheritedFallback.rawStep? mol ops geom state (some second) node under := by
  unfold LocalizedChemicalRingInheritedFallback.rawStep?
  cases frame : frameAtoms? mol node with
  | none => simp [LocalizedPhysicalMarkedDistantReference.rawStep?, frame]
  | some atoms =>
      cases ordered : ops.ordinary state node with
      | none => simp [LocalizedPhysicalMarkedDistantReference.rawStep?, frame, ordered]
      | some result =>
          obtain ⟨sorted, adjacent⟩ := result
          simp only [LocalizedPhysicalMarkedDistantReference.rawStep?, frame, ordered,
            Option.bind_eq_bind, Option.bind_some]
          by_cases bad : ¬ atoms.Nodup ∨ consistent adjacent = false
          · simp only [if_pos bad]
          · simp only [if_neg bad]
            by_cases strictOrder : strict adjacent = true
            · simp only [if_pos strictOrder]
            · simp only [if_neg strictOrder, chooseInherited, ← same]
              cases reading : inheritedRead? mol ops geom state node under first <;>
                by_cases inFirst : first ∈ atoms <;>
                by_cases inSecond : second ∈ atoms <;>
                simp only [inFirst, inSecond, ite_true, ite_false] <;>
                first | rfl | (cases (LocalizedGenericMarkedRecalculation.consensus
                  ((LocalizedGenericMarkedRecalculation.eligibleOf atoms sorted adjacent).map
                    (inheritedRead? mol ops geom state node under))) <;> rfl)

variable (mol : RawMolecule) (ops : Operations)

/-- Equality is needed only for the two actual generated child continuations, on the
input geometry and its reflection. No comparison success or final descriptor is supplied. -/
theorem descriptor_eq_of_reads_eq (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (first second : Nat)
    (same : ∀ g, g = geom ∨ g = mirror geom →
      inheritedRead? mol ops g state node
          (underWith mol ops g state node
            (factsWith LocalizedChemicalRingInheritedFallback.rawStep? mol ops depth)) first =
        inheritedRead? mol ops g state node
          (underWith mol ops g state node
            (factsWith LocalizedChemicalRingInheritedFallback.rawStep? mol ops depth)) second) :
    LocalizedChemicalRingInheritedFallback.descriptor? mol ops depth geom state (some first) node =
      LocalizedChemicalRingInheritedFallback.descriptor? mol ops depth geom state (some second) node := by
  unfold LocalizedChemicalRingInheritedFallback.descriptor? descriptorWith
  rw [rawStep_eq_of_read_eq mol ops geom state node _ first second (same geom (Or.inl rfl)),
    rawStep_eq_of_read_eq mol ops (mirror geom) state node _ first second
      (same (mirror geom) (Or.inr rfl))]

/-- Lift locally established descriptor-context equality to the actual ordered fact list
on a child-closed region. This preserves full facts, not merely selected label values. -/
theorem facts_eq_of_descriptor_eq (P : Node → Prop)
    (closed : ∀ node child, P node → child ∈ mol.canonicalChildren node → P child)
    (geom : Geometry) (state : OccurrenceAuxState) (first second : Nat)
    (atNode : ∀ depth node, P node →
      LocalizedChemicalRingInheritedFallback.descriptor? mol ops depth geom state (some first) node =
        LocalizedChemicalRingInheritedFallback.descriptor? mol ops depth geom state (some second) node) :
    ∀ depth node, P node →
      LocalizedChemicalRingInheritedFallback.facts mol ops depth geom state (some first) node =
        LocalizedChemicalRingInheritedFallback.facts mol ops depth geom state (some second) node := by
  intro depth
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro node member
      rw [LocalizedChemicalRingInheritedFallback.facts_succ,
        LocalizedChemicalRingInheritedFallback.facts_succ, atNode depth node member]
      congr 1
      exact flatMap_congr_mem _ _ _ fun child edge => ih child (closed node child member edge)

end TetraStereo.OneCenter.LocalizedChemicalRingContextIndependence

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingContextIndependence.rawStep_eq_of_read_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingContextIndependence.descriptor_eq_of_reads_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingContextIndependence.facts_eq_of_descriptor_eq
