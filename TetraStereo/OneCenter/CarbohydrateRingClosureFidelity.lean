import TetraStereo.OneCenter.CarbohydrateFoundationStereochemistrySemantics
import TetraStereo.OneCenter.Euclidean
import TetraStereo.OneCenter.RS
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace Carbohydrate1996Foundation

noncomputable section

/-!
# Reverse ring-closure descriptor fidelity (2-Carb-6.4)

The 1996 recommendation separates two questions for a ring closure:

1. **Which descriptor families are permitted?**  `alpha` and `beta` are applicable only when the
   anomeric carbon atom has a lower locant than the anomeric reference atom.  In the other ring
   closure direction the configuration is indicated by `R` or `S` *according to the sequence rule*.
2. **What is the actual `R`/`S` value?**  That is a CIP priority question, not a letter question.

The foundation module `CarbohydrateFoundationStereochemistrySemantics` now answers only (1), with
`anomerDescriptorFamily` and `descriptorForRingClosure?`; the latter emits `none` in the reverse
branch rather than fabricating `alpha ↦ R`, `beta ↦ S`.

This module supplies (2) by *consuming* the existing checked one-center CIP engine.  The consumer
`checkedAnomericCIPDescriptor` takes three explicit inputs:

* an actual `OneCenterMolecule V` -- the molecular graph, hence the priority input;
* a proof `molecule.ResolvedCIPDescriptor` -- the engine's own evidence that the CIP priorities are
  resolved (no tie is guessed);
* a `TetrahedralGeometry.Realization` -- an actual physical configuration.

The output is the existing descriptor-facing engine result `molecule.rsCIPOfResolved resolved
geometry`, relabelled into the carbohydrate descriptor alphabet by `AnomerDescriptor.ofRS`.  This
module never claims that the engine result is chemically "correct"; it proves only that the value
is the checked CIP result, that it is `R` or `S` (never an alpha/beta letter), and that it is not
determined by the anomer letter.

The key negative regression is `no_anomer_only_assignment_matches_checked_CIP`: reflecting the
physical realization of the same molecule, with the same resolved priorities, swaps `R` and `S`
(`rsCIPOfResolved_reflection`).  Therefore no function of the anomer letter alone -- and in
particular the historical `alpha ↦ cipR`, `beta ↦ cipS` assignment -- can agree with the checked
producer on every realization.  The definition `descriptorForRingClosure?` has no molecular
priority parameter at all, so its reverse branch cannot be an `R`/`S` oracle.
-/

/-! ## The checked CIP result expressed in the carbohydrate alphabet -/

namespace AnomerDescriptor

/-- Relabel an existing `R`/`S` engine result in the carbohydrate descriptor alphabet.  This is a
label correspondence only; it recomputes no priorities and asserts nothing about chemical
correctness. -/
def ofRS : RS → AnomerDescriptor
  | .R => .cipR
  | .S => .cipS

@[simp] theorem ofRS_R : ofRS RS.R = AnomerDescriptor.cipR := rfl

@[simp] theorem ofRS_S : ofRS RS.S = AnomerDescriptor.cipS := rfl

/-- Distinct `R`/`S` results give distinct carbohydrate descriptors. -/
theorem ofRS_injective : Function.Injective ofRS := by
  intro left right equal
  cases left <;> cases right <;> simp_all [ofRS]

/-- A checked `R`/`S` result is never an alpha/beta letter descriptor. -/
theorem ofRS_ne_alphaBeta (rs : RS) (anomer : Anomer) :
    ofRS rs ≠ AnomerDescriptor.alphaBeta anomer := by
  cases rs <;> simp [ofRS]

/-- Swapping the handedness changes the descriptor: `R` and `S` are distinct. -/
theorem ofRS_swap_ne (rs : RS) : ofRS (RS.swap rs) ≠ ofRS rs := by
  cases rs <;> simp [ofRS, RS.swap]

end AnomerDescriptor

/-! ## A concrete physical reflection -/

/-- The reflection across the `yz`-plane, packaged as an orientation-reversing Euclidean motion.
It is a genuine physical transformation of a realization and is used to exhibit the
geometry-dependence of the checked CIP reading. -/
def reflectionMotion : TetrahedralGeometry.OrientationReversingEuclideanMotion :=
  TetrahedralGeometry.OrientationReversingEuclideanMotion.ofImproperRotation
    TetrahedralGeometry.yzPlaneReflection

namespace RingClosureFidelity

/-! ## Checked `R`/`S` consumer with explicit physical and priority binding -/

section CheckedCIP

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reflecting the physical realization of a molecule with resolved CIP priorities swaps its
descriptor-facing `R`/`S` reading.  The molecule and the priority evidence are literally unchanged;
only the geometry is reflected. -/
@[simp] theorem rsCIPOfResolved_reflection (molecule : OneCenterMolecule V)
    (resolved : molecule.ResolvedCIPDescriptor)
    (geometry : TetrahedralGeometry.Realization) :
    molecule.rsCIPOfResolved resolved (reflectionMotion • geometry) =
      RS.swap (molecule.rsCIPOfResolved resolved geometry) := by
  simpa using
    (molecule.rsCycleCutOfResolved_map_of_orientationReversingEuclideanMotion
      resolved reflectionMotion geometry)

/-- The checked CIP consumer for an anomeric centre.  All three inputs are explicit and binding:
the actual molecular graph (priority input), the engine's proof that priorities are resolved, and
an actual physical realization.  The output is the existing descriptor-facing CIP result; no
priority is guessed and no correctness oracle is asserted. -/
def checkedAnomericCIPDescriptor (molecule : OneCenterMolecule V)
    (resolved : molecule.ResolvedCIPDescriptor)
    (geometry : TetrahedralGeometry.Realization) : AnomerDescriptor :=
  AnomerDescriptor.ofRS (molecule.rsCIPOfResolved resolved geometry)

/-- The consumer is exactly the existing checked CIP result, relabelled. -/
@[simp] theorem checkedAnomericCIPDescriptor_eq (molecule : OneCenterMolecule V)
    (resolved : molecule.ResolvedCIPDescriptor)
    (geometry : TetrahedralGeometry.Realization) :
    checkedAnomericCIPDescriptor molecule resolved geometry =
      AnomerDescriptor.ofRS (molecule.rsCIPOfResolved resolved geometry) := rfl

/-- The checked consumer always emits a sequence-rule descriptor, never an alpha/beta letter. -/
theorem checkedAnomericCIPDescriptor_is_cip (molecule : OneCenterMolecule V)
    (resolved : molecule.ResolvedCIPDescriptor)
    (geometry : TetrahedralGeometry.Realization) :
    checkedAnomericCIPDescriptor molecule resolved geometry = .cipR ∨
      checkedAnomericCIPDescriptor molecule resolved geometry = .cipS := by
  unfold checkedAnomericCIPDescriptor
  rcases h : molecule.rsCIPOfResolved resolved geometry with _ | _
  · left
    rfl
  · right
    rfl

/-- The checked consumer is not an alpha/beta descriptor for any letter. -/
theorem checkedAnomericCIPDescriptor_ne_alphaBeta (molecule : OneCenterMolecule V)
    (resolved : molecule.ResolvedCIPDescriptor)
    (geometry : TetrahedralGeometry.Realization) (anomer : Anomer) :
    checkedAnomericCIPDescriptor molecule resolved geometry ≠
      AnomerDescriptor.alphaBeta anomer :=
  AnomerDescriptor.ofRS_ne_alphaBeta _ anomer

/-- Reflecting the realization swaps the checked descriptor. -/
theorem checkedAnomericCIPDescriptor_reflection (molecule : OneCenterMolecule V)
    (resolved : molecule.ResolvedCIPDescriptor)
    (geometry : TetrahedralGeometry.Realization) :
    checkedAnomericCIPDescriptor molecule resolved (reflectionMotion • geometry) =
      AnomerDescriptor.ofRS (RS.swap (molecule.rsCIPOfResolved resolved geometry)) := by
  simp only [checkedAnomericCIPDescriptor_eq, rsCIPOfResolved_reflection]

/-! ### The reverse-closure producer -/

/-- Reverse-closure descriptor producer.  It is available only under the source routing decision
`requiresCIP`, and it consumes the checked CIP result with the explicit molecule, priority-
resolution and geometry binding.  It has no `Anomer` argument, so there is no `alpha ↦ R`
shortcut.

The `_route` argument is a gate, not a computation: it records that the source family decision has
already selected the reverse branch. -/
def reverseClosureDescriptor (anomericLocant referenceLocant : Nat)
    (_route : anomerDescriptorFamily anomericLocant referenceLocant = .requiresCIP)
    (molecule : OneCenterMolecule V)
    (resolved : molecule.ResolvedCIPDescriptor)
    (geometry : TetrahedralGeometry.Realization) : AnomerDescriptor :=
  checkedAnomericCIPDescriptor molecule resolved geometry

/-- The reverse producer is the checked CIP consumer. -/
@[simp] theorem reverseClosureDescriptor_eq (anomericLocant referenceLocant : Nat)
    (route : anomerDescriptorFamily anomericLocant referenceLocant = .requiresCIP)
    (molecule : OneCenterMolecule V) (resolved : molecule.ResolvedCIPDescriptor)
    (geometry : TetrahedralGeometry.Realization) :
    reverseClosureDescriptor anomericLocant referenceLocant route molecule resolved geometry =
      checkedAnomericCIPDescriptor molecule resolved geometry := rfl

/-- The reverse producer emits `R` or `S`. -/
theorem reverseClosureDescriptor_is_cip (anomericLocant referenceLocant : Nat)
    (route : anomerDescriptorFamily anomericLocant referenceLocant = .requiresCIP)
    (molecule : OneCenterMolecule V) (resolved : molecule.ResolvedCIPDescriptor)
    (geometry : TetrahedralGeometry.Realization) :
    reverseClosureDescriptor anomericLocant referenceLocant route molecule resolved geometry =
        .cipR ∨
      reverseClosureDescriptor anomericLocant referenceLocant route molecule resolved geometry =
        .cipS :=
  checkedAnomericCIPDescriptor_is_cip molecule resolved geometry

/-- The reverse producer never emits an alpha/beta descriptor. -/
theorem reverseClosureDescriptor_ne_alphaBeta (anomericLocant referenceLocant : Nat)
    (route : anomerDescriptorFamily anomericLocant referenceLocant = .requiresCIP)
    (molecule : OneCenterMolecule V) (resolved : molecule.ResolvedCIPDescriptor)
    (geometry : TetrahedralGeometry.Realization) (anomer : Anomer) :
    reverseClosureDescriptor anomericLocant referenceLocant route molecule resolved geometry ≠
      AnomerDescriptor.alphaBeta anomer := by
  simp only [reverseClosureDescriptor_eq, checkedAnomericCIPDescriptor_eq]
  exact AnomerDescriptor.ofRS_ne_alphaBeta _ anomer

/-- Reflecting the physical realization swaps the reverse-closure descriptor while the molecule
and its resolved CIP priorities stay fixed. -/
theorem reverseClosureDescriptor_reflection (anomericLocant referenceLocant : Nat)
    (route : anomerDescriptorFamily anomericLocant referenceLocant = .requiresCIP)
    (molecule : OneCenterMolecule V) (resolved : molecule.ResolvedCIPDescriptor)
    (geometry : TetrahedralGeometry.Realization) :
    reverseClosureDescriptor anomericLocant referenceLocant route molecule resolved
        (reflectionMotion • geometry) =
      AnomerDescriptor.ofRS (RS.swap (molecule.rsCIPOfResolved resolved geometry)) := by
  simp only [reverseClosureDescriptor_eq, checkedAnomericCIPDescriptor_eq,
    rsCIPOfResolved_reflection]

/-! ## The routing decision and the assignment are separate -/

/-- The `requiresCIP` family decision is equivalent to the letter router emitting nothing.  This
is the exact separation of the two questions: the router decides *family availability*; it never
assigns a sequence-rule value. -/
theorem requiresCIP_iff_router_none (anomericLocant referenceLocant : Nat) (anomer : Anomer) :
    anomerDescriptorFamily anomericLocant referenceLocant = .requiresCIP ↔
      descriptorForRingClosure? anomericLocant referenceLocant anomer = none := by
  rw [anomerDescriptorFamily_eq_requiresCIP_iff]
  constructor
  · intro notLower
    exact descriptorForRingClosure?_reverse anomericLocant referenceLocant anomer notLower
  · intro empty lower
    rw [descriptorForRingClosure?_lower anomericLocant referenceLocant anomer lower] at empty
    simp at empty

/-- Reverse-closure fidelity: the letter router is empty, and the checked CIP consumer supplies a
genuine `R`/`S` descriptor from actual physical and priority data. -/
theorem reverseClosure_fidelity {anomericLocant referenceLocant : Nat}
    (route : anomerDescriptorFamily anomericLocant referenceLocant = .requiresCIP)
    (anomer : Anomer) (molecule : OneCenterMolecule V)
    (resolved : molecule.ResolvedCIPDescriptor)
    (geometry : TetrahedralGeometry.Realization) :
    descriptorForRingClosure? anomericLocant referenceLocant anomer = none ∧
      (reverseClosureDescriptor anomericLocant referenceLocant route molecule resolved geometry =
          .cipR ∨
        reverseClosureDescriptor anomericLocant referenceLocant route molecule resolved geometry =
          .cipS) :=
  ⟨(requiresCIP_iff_router_none anomericLocant referenceLocant anomer).1 route,
    reverseClosureDescriptor_is_cip anomericLocant referenceLocant route molecule resolved
      geometry⟩

/-! ## Negative regression: the letter alone cannot determine `R` -/

/-- **No anomer-letter-only assignment can match the checked CIP producer.**

Reflecting the physical realization of the same molecule, with the same resolved CIP priorities,
swaps the checked descriptor.  Hence, for any proposed function `assignment : Anomer →
AnomerDescriptor` of the anomer letter, there is a realization on which the checked producer
disagrees with `assignment .alpha`.  The old reverse branch of `descriptorFamilyForRingClosure`,
which returned `cipR` for `alpha` and `cipS` for `beta` without any priority input, is exactly such
a letter-only assignment: its definition has no molecular-priority information. -/
theorem no_anomer_only_assignment_matches_checked_CIP {anomericLocant referenceLocant : Nat}
    (route : anomerDescriptorFamily anomericLocant referenceLocant = .requiresCIP)
    (molecule : OneCenterMolecule V) (resolved : molecule.ResolvedCIPDescriptor)
    (geometry : TetrahedralGeometry.Realization)
    (assignment : Anomer → AnomerDescriptor) :
    ¬ ∀ geometry' : TetrahedralGeometry.Realization,
        reverseClosureDescriptor anomericLocant referenceLocant route molecule resolved
            geometry' = assignment .alpha := by
  intro agrees
  have fixed := agrees geometry
  have reflected := agrees (reflectionMotion • geometry)
  simp only [reverseClosureDescriptor_eq, checkedAnomericCIPDescriptor_eq] at fixed reflected
  rw [rsCIPOfResolved_reflection] at reflected
  exact AnomerDescriptor.ofRS_swap_ne (molecule.rsCIPOfResolved resolved geometry)
    (reflected.trans fixed.symm)

/-- The refuted historical assignment used by the old reverse branch of
`descriptorFamilyForRingClosure`: `alpha ↦ cipR`, `beta ↦ cipS`, with no molecular or priority
input.  It is retained only as a named counterexample target; it is not used by any producer. -/
def fabricatedAlphaBetaToCIPAssignment : Anomer → AnomerDescriptor
  | .alpha => .cipR
  | .beta => .cipS

@[simp] theorem fabricatedAlphaBetaToCIPAssignment_alpha :
    fabricatedAlphaBetaToCIPAssignment .alpha = AnomerDescriptor.cipR := rfl

@[simp] theorem fabricatedAlphaBetaToCIPAssignment_beta :
    fabricatedAlphaBetaToCIPAssignment .beta = AnomerDescriptor.cipS := rfl

/-- The old `alpha ↦ R` rule is not the checked CIP result: for the same molecule and priorities
there is a physical realization on which the checked producer disagrees with
`fabricatedAlphaBetaToCIPAssignment .alpha`. -/
theorem fabricated_assignment_not_checked_CIP {anomericLocant referenceLocant : Nat}
    (route : anomerDescriptorFamily anomericLocant referenceLocant = .requiresCIP)
    (molecule : OneCenterMolecule V) (resolved : molecule.ResolvedCIPDescriptor)
    (geometry : TetrahedralGeometry.Realization) :
    ∃ geometry' : TetrahedralGeometry.Realization,
      reverseClosureDescriptor anomericLocant referenceLocant route molecule resolved geometry' ≠
        fabricatedAlphaBetaToCIPAssignment .alpha := by
  by_contra noWitness
  exact no_anomer_only_assignment_matches_checked_CIP route molecule resolved geometry
    fabricatedAlphaBetaToCIPAssignment (by
      intro geometry'
      by_contra different
      exact noWitness ⟨geometry', different⟩)

end CheckedCIP

end RingClosureFidelity

end

end Carbohydrate1996Foundation
end TetraStereo.OneCenter

/-! ## Kernel receipts -/

assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996Foundation.AnomerDescriptor.ofRS_injective
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996Foundation.AnomerDescriptor.ofRS_ne_alphaBeta
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996Foundation.AnomerDescriptor.ofRS_swap_ne
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996Foundation.RingClosureFidelity.rsCIPOfResolved_reflection
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996Foundation.RingClosureFidelity.checkedAnomericCIPDescriptor_is_cip
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996Foundation.RingClosureFidelity.checkedAnomericCIPDescriptor_ne_alphaBeta
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996Foundation.RingClosureFidelity.reverseClosureDescriptor_is_cip
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996Foundation.RingClosureFidelity.reverseClosureDescriptor_ne_alphaBeta
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996Foundation.RingClosureFidelity.reverseClosureDescriptor_reflection
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996Foundation.RingClosureFidelity.requiresCIP_iff_router_none
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996Foundation.RingClosureFidelity.reverseClosure_fidelity
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996Foundation.RingClosureFidelity.no_anomer_only_assignment_matches_checked_CIP
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996Foundation.RingClosureFidelity.fabricated_assignment_not_checked_CIP
