import TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathLabels
import TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathReconstruction
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-!
For every prescribed detected-terminal path, actual refined-key equality supplies a
molecular automorphism realizing that path's image and preserving the original history
and reference. Detection of the image terminal follows from this graph automorphism;
the same actual path correspondence supplies exact optional raw fact-label equality.

The quantifier is FOR EACH path THERE EXISTS an automorphism. The chosen map may depend
on the path, and it need not preserve physical signs established for an earlier map.
No successful observation or physical properness is asserted.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathFactMatch

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader LocalizedChemicalRingColoredReconstruction
open LocalizedChemicalRingWitnessLabelMatch LocalizedChemicalRingBoundaryWitnessFactMatch
open LocalizedChemicalRingWitnessFactMatch LocalizedChemicalRingPrescribedPathLabels
open LocalizedChemicalRingPrescribedPathReconstruction

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = .realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)

/-- Each prescribed path receives its own reference-fixing realizing automorphism,
with image detection and full-history optional fact labels derived from actual keys. -/
theorem actual_outward_default_tie_prescribed_fact_match
    (reference : input.Atom) (left right : Fin 4) (a b : input.Atom)
    (currentL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.current? = some a)
    (currentR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.current? = some b)
    (realL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.provenance = .realAtom)
    (realR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.provenance = .realAtom)
    (rootL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.root = target.1.root)
    (rootR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.root = target.1.root)
    (slotL slotR : Nat)
    (addressL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.address = target.1.address ++ [slotL])
    (addressR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.address = target.1.address ++ [slotR])
    (tie : refinedKey input single state target real unit targetUnit reference
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) left =
      refinedKey input single state target real unit targetUnit reference
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) right)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph) :
    ∃ e : ResidualPathTreeEquiv input.moleculeGraph
        target.1.node.history.reverse target.1.node.history.reverse a b,
      ∀ p : {p : List input.Atom //
          ResidualObsPath input.moleculeGraph target.1.node.history.reverse a p},
        IsDetectedCenter input.moleculeGraph (pathTerminal p.1 p.2.nonempty) →
        ∃ π : Equiv.Perm input.Atom,
          input.moleculeGraph.IsAutomorphism π ∧
          (∀ atom ∈ target.1.node.history, π atom = atom) ∧
          π a = b ∧ π reference = reference ∧
          (∀ z, ¬ InComponent input.moleculeGraph target.1.node.history.reverse a z →
            ¬ InComponent input.moleculeGraph target.1.node.history.reverse b z → π z = z) ∧
          (e.toEquiv p).1 = p.1.map π ∧
          IsDetectedCenter input.moleculeGraph (π (pathTerminal p.1 p.2.nonempty)) ∧
          PathLabelsAgree
            (slotTree input single state target real unit targetUnit left)
            (slotTree input single state target real unit targetUnit right)
            (rawStateReader input state target) (rawStateReader input state target)
            target.1.node.history.reverse p.1 (p.1.map π) ∧
          (state.factAt? (rawPathNode target.1.root (boundaryPath target p.1))).map factLabel =
            (state.factAt? (rawPathNode target.1.root
              (boundaryPath target (p.1.map π)))).map factLabel := by
  obtain ⟨e, referencePreserved, matched⟩ := actual_outward_default_tie_path_equivalence
    input single state target real unit targetUnit reference left right a b currentL currentR
    realL realR rootL rootR slotL slotR addressL addressR tie charge
  refine ⟨e, ?_⟩
  intro p detected
  have outside : a ∉ target.1.node.history.reverse :=
    p.2.outside a (List.mem_of_head?_eq_some p.2.head)
  obtain ⟨π, automorphism, fixed, entry, colors, support, image⟩ :=
    exists_forced_color_preserving_aut e outside (referenceColor reference) referencePreserved p
  have referenceFixed : π reference = reference := by
    have equal := colors reference
    by_contra different
    simp [referenceColor, different] at equal
  let graphAut : input.moleculeGraph.Aut := ⟨π, automorphism⟩
  have imageDetected : IsDetectedCenter input.moleculeGraph (π (pathTerminal p.1 p.2.nonempty)) :=
    (input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card _).mp
      ((input.moleculeGraph.isTetrahedralCenter_apply_aut_iff graphAut _).mpr
        ((input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card _).mpr detected))
  have imageTerminal : pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty =
      π (pathTerminal p.1 p.2.nonempty) := by
    simp only [pathTerminal, image, List.getLast_map]
  have detectedQ : IsDetectedCenter input.moleculeGraph
      (pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty) := by
    rw [imageTerminal]
    exact imageDetected
  refine ⟨π, automorphism, ?_, entry, referenceFixed, support, image, imageDetected, ?_, ?_⟩
  · intro atom member
    exact fixed atom (List.mem_reverse.mpr member)
  · simpa only [image] using (matched p).1
  · simpa only [image] using (matched p).2 detected detectedQ

/-- One automorphism realizes the whole prescribed path and every nonempty prefix.
The final vertex need not be detected. Every detected prefix terminal has a detected
image and the exact matching optional fact label under this SAME automorphism. -/
theorem actual_outward_default_tie_prescribed_prefixes
    (reference : input.Atom) (left right : Fin 4) (a b : input.Atom)
    (currentL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.current? = some a)
    (currentR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.current? = some b)
    (realL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.provenance = .realAtom)
    (realR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.provenance = .realAtom)
    (rootL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.root = target.1.root)
    (rootR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.root = target.1.root)
    (slotL slotR : Nat)
    (addressL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.address = target.1.address ++ [slotL])
    (addressR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.address = target.1.address ++ [slotR])
    (tie : refinedKey input single state target real unit targetUnit reference
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) left =
      refinedKey input single state target real unit targetUnit reference
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) right)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph) :
    ∃ e : ResidualPathTreeEquiv input.moleculeGraph
        target.1.node.history.reverse target.1.node.history.reverse a b,
      ∀ p : {p : List input.Atom //
          ResidualObsPath input.moleculeGraph target.1.node.history.reverse a p},
        ∃ π : Equiv.Perm input.Atom,
          input.moleculeGraph.IsAutomorphism π ∧
          (∀ atom ∈ target.1.node.history, π atom = atom) ∧
          π a = b ∧ π reference = reference ∧
          (∀ z, ¬ InComponent input.moleculeGraph target.1.node.history.reverse a z →
            ¬ InComponent input.moleculeGraph target.1.node.history.reverse b z → π z = z) ∧
          (e.toEquiv p).1 = p.1.map π ∧
          ∀ k (positive : 0 < k) (bounded : k ≤ p.1.length),
            PathLabelsAgree
              (slotTree input single state target real unit targetUnit left)
              (slotTree input single state target real unit targetUnit right)
              (rawStateReader input state target) (rawStateReader input state target)
              target.1.node.history.reverse (p.1.take k) ((p.1.take k).map π) ∧
            (IsDetectedCenter input.moleculeGraph
                (pathTerminal (p.1.take k) (obs_take input.moleculeGraph p.2 bounded positive).nonempty) →
              IsDetectedCenter input.moleculeGraph
                (π (pathTerminal (p.1.take k) (obs_take input.moleculeGraph p.2 bounded positive).nonempty)) ∧
              (state.factAt? (rawPathNode target.1.root
                (boundaryPath target (p.1.take k)))).map factLabel =
                (state.factAt? (rawPathNode target.1.root
                  (boundaryPath target ((p.1.take k).map π)))).map factLabel) := by
  obtain ⟨e, referencePreserved, matched⟩ := actual_outward_default_tie_path_equivalence
    input single state target real unit targetUnit reference left right a b currentL currentR
    realL realR rootL rootR slotL slotR addressL addressR tie charge
  refine ⟨e, ?_⟩
  intro p
  have outside : a ∉ target.1.node.history.reverse :=
    p.2.outside a (List.mem_of_head?_eq_some p.2.head)
  obtain ⟨π, automorphism, fixed, entry, colors, support, image⟩ :=
    exists_forced_color_preserving_aut e outside (referenceColor reference) referencePreserved p
  have referenceFixed : π reference = reference := by
    have equal := colors reference
    by_contra different
    simp [referenceColor, different] at equal
  refine ⟨π, automorphism, ?_, entry, referenceFixed, support, image, ?_⟩
  · intro atom member
    exact fixed atom (List.mem_reverse.mpr member)
  · intro k positive bounded
    let q : {q : List input.Atom //
        ResidualObsPath input.moleculeGraph target.1.node.history.reverse a q} :=
      ⟨p.1.take k, obs_take input.moleculeGraph p.2 bounded positive⟩
    have prefixImage : (e.toEquiv q).1 = q.1.map π := by
      simpa only [q, image, List.map_take] using take_image e p k bounded positive
    refine ⟨?_, ?_⟩
    · simpa only [prefixImage] using (matched q).1
    · intro detected
      let graphAut : input.moleculeGraph.Aut := ⟨π, automorphism⟩
      have imageDetected : IsDetectedCenter input.moleculeGraph
          (π (pathTerminal q.1 q.2.nonempty)) :=
        (input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card _).mp
          ((input.moleculeGraph.isTetrahedralCenter_apply_aut_iff graphAut _).mpr
            ((input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card _).mpr detected))
      have imageTerminal : pathTerminal (e.toEquiv q).1 (e.toEquiv q).2.nonempty =
          π (pathTerminal q.1 q.2.nonempty) := by
        simp only [pathTerminal, prefixImage, List.getLast_map]
      have detectedQ : IsDetectedCenter input.moleculeGraph
          (pathTerminal (e.toEquiv q).1 (e.toEquiv q).2.nonempty) := by
        rw [imageTerminal]
        exact imageDetected
      refine ⟨imageDetected, ?_⟩
      simpa only [prefixImage] using (matched q).2 detected detectedQ

end
end TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathFactMatch

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathFactMatch.actual_outward_default_tie_prescribed_fact_match
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathFactMatch.actual_outward_default_tie_prescribed_prefixes
