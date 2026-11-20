import TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransportExecution
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution
import TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathOrientation
import TetraStereo.OneCenter.LocalizedChemicalRingOrientationReadback
import TetraStereo.OneCenter.LocalizedChemicalRingResidualReadingTransport
import TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases
import TetraStereo.OneCenter.LocalizedMarkedTerminalReferenceScope
import TetraStereo.OneCenter.LocalizedMarkedReachableConfigurations
import TetraStereo.OneCenter.LocalizedMarkedReachedFrameNeighbors
import TetraStereo.OneCenter.LocalizedMarkedCertifiedTerminalRefusal
import TetraStereo.OneCenter.LocalizedMarkedCyclicDiscardedReference
import TetraStereo.KernelOnly

import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryFlip

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! Calibrated physical transport of actual prepared fallback readings. Molecular relabeling
and the physical frame sign supply the two parts of this equation; child readback agreement
is the explicit local induction hypothesis. Entire accumulated and newly extended reference
contexts are retained, separately on each geometry side. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalTransport

open CertifiedLocalizedCIPInput
open LocalizedGenericMarkedRecalculation
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingMultiMarkRecursion (MultiOperations markedReadingJoint?)
open LocalizedChemicalRingJointPreparedCovariance
open LocalizedChemicalRingJointOperationTransportExecution
open LocalizedChemicalRingJointPreparedExecution
open LocalizedChemicalRingJointMarkerOperations
open LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingRelabel
open LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingCoveredPathOrientation
open LocalizedChemicalRingOrientationReadback
open LocalizedChemicalRingResidualReadingTransport
open LocalizedChemicalRingInheritedRefusalCases
open LocalizedMarkedTerminalReferenceScope
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedReachedFrameNeighbors (SingleBonded reached_atom_valid)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedMarkedCyclicDiscardedReference (rankedAtoms_subset)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open scoped Classical


noncomputable section
abbrev Node := RawMolecule.CanonicalBranchNode
abbrev MarkContext := List Nat
abbrev moleculeRelabel (input : CertifiedLocalizedCIPInput) (e : input.moleculeGraph.Aut) : Nat → Nat :=
  relabelOf input (e : Equiv.Perm input.Atom)

theorem map_eq_self_of_pointwise (σ : Nat → Nat) (L : List Nat)
    (fixed : ∀ x ∈ L, σ x = x) : L.map σ = L := by
  calc
    L.map σ = L.map id := List.map_congr_left (fun x member => fixed x member)
    _ = L := List.map_id L

/-! ## The two signs of a reading -/

theorem sign_swap_ne (v : RS) : v.swap ≠ v := by
  cases v <;> simp [RS.swap]

/-! ## Descent and the covered-history geometry producer -/

theorem strictDescendant_child (mol : RawMolecule) (node child : Node)
    (member : child ∈ mol.canonicalChildren node) : StrictDescendant mol node child :=
  ⟨child, member, Relation.ReflTransGen.refl⟩

theorem strictDescendant_closed (mol : RawMolecule) (root : Node) :
    ∀ node child, StrictDescendant mol root node →
      child ∈ mol.canonicalChildren node → StrictDescendant mol root child := by
  intro node child below member
  rcases below with ⟨middle, memberMid, descends⟩
  exact ⟨middle, memberMid, Relation.ReflTransGen.tail descends member⟩

/-- **Calibrated physical transport of an actual prepared fallback.** The image occurrence under
the observed geometry and the source occurrence under the observed geometry differ by exactly the
sign at the current centre. The two mirror orientations are handled separately through
`reflected`. The child facts below the source occurrence are only assumed to agree between the
pulled-back and observed geometries; the root readback difference is derived from calibration,
not assumed. -/
theorem actual_evaluateFallback_transport
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (e : input.moleculeGraph.Aut) (ePhys : input.detectedMultiCenterMolecule.Aut)
    (samePerm : (ePhys : Equiv.Perm input.Atom) = (e : Equiv.Perm input.Atom))
    (sym : StructuralSymmetry mol (moleculeRelabel input e))
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (c : input.detectedMultiCenterMolecule.Center) (node : Node)
    (current : node.atom = c.1.val) (reached : Reached mol node) (reflected : Bool)
    (childAgree : AgreeOn (StrictDescendant mol node) mol
      (pullback (moleculeRelabel input e) (observedGeometry input reflected))
      (observedGeometry input reflected))
    (atoms : List Nat) (frame : frameAtoms? mol node = some atoms)
    (depth : Nat) (M : MarkContext) (s : Nat) :
    evaluateFallback? mol (jointOperations input mol) (observedGeometry input reflected) []
        (mapNode (moleculeRelabel input e) node)
        (M.map (moleculeRelabel input e))
        (childrenUnder mol (preparedFacts mol (jointOperations input mol) depth)
          (observedGeometry input reflected) [] (mapNode (moleculeRelabel input e) node))
        (moleculeRelabel input e s) =
      flipBy (relativeSign input.detectedMultiCenterMolecule cfg ePhys c)
        (evaluateFallback? mol (jointOperations input mol) (observedGeometry input reflected) []
          node M
          (childrenUnder mol (preparedFacts mol (jointOperations input mol) depth)
            (observedGeometry input reflected) [] node)
          s) := by
  have rawSingle : SingleBonded mol :=
    raw_single mol input agreement admissible.1.1 admissible.1.2 supported single
  obtain ⟨atoms', frame', _⟩ :=
    frameAtoms_map_some sym admissible.1.1 admissible.1.2 rawSingle node atoms frame
      (reached_atom_valid mol admissible.1.1 node reached)
  have mapped := actual_evaluateFallback_map input mol agreement admissible supported single e sym
    depth (observedGeometry input reflected) M node reached atoms atoms' frame frame' s
  have childrenEq :
      childrenUnder mol (preparedFacts mol (jointOperations input mol) depth)
          (pullback (moleculeRelabel input e) (observedGeometry input reflected)) [] node =
        childrenUnder mol (preparedFacts mol (jointOperations input mol) depth)
          (observedGeometry input reflected) [] node := by
    funext L
    unfold childrenUnder
    exact flatMap_congr_mem _ _ _ fun child member =>
      LocalizedChemicalRingJointPreparedGeometryCongruence.preparedFacts_congr
        mol (jointOperations input mol) (StrictDescendant mol node)
        (strictDescendant_closed mol node) depth _ _ childAgree [] L child
        (strictDescendant_child mol node child member)
  have rel : relabelOf input (ePhys : Equiv.Perm input.Atom) =
      relabelOf input (e : Equiv.Perm input.Atom) := congrArg (relabelOf input) samePerm
  have readFlip : ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) →
      readback? (pullback (moleculeRelabel input e) (observedGeometry input reflected)) L =
        flipBy (relativeSign input.detectedMultiCenterMolecule cfg ePhys c)
          (readback? (observedGeometry input reflected) L) := by
    intro L sub
    have h := frame_readback_flip input mol agreement admissible supported single cfg ePhys
      calibrated c node reached current atoms frame reflected L sub
    rw [rel] at h
    exact h
  have flipped := LocalizedChemicalRingJointPreparedGeometryFlip.evaluateFallback_flip
    mol (jointOperations input mol)
    (relativeSign input.detectedMultiCenterMolecule cfg ePhys c)
    (pullback (moleculeRelabel input e) (observedGeometry input reflected))
    (observedGeometry input reflected) node atoms frame readFlip [] M
    (childrenUnder mol (preparedFacts mol (jointOperations input mol) depth)
      (observedGeometry input reflected) [] node) s
  rw [mapped, childrenEq]
  exact flipped

/-- **Slot-level fallback transport at a fixed occurrence.** The occurrence and its inherited
references are fixed by `e`; the image reference slot `b` is the image of the source slot `a`.
Then the actual fallback at `b` is the sign flip of the actual fallback at `a`. This is the
occurrence-level reading comparison consumed by the orientation step; the desired reading
equality is not assumed. -/
theorem actual_fallback_transport_of_slot
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (e : input.moleculeGraph.Aut) (ePhys : input.detectedMultiCenterMolecule.Aut)
    (samePerm : (ePhys : Equiv.Perm input.Atom) = (e : Equiv.Perm input.Atom))
    (sym : StructuralSymmetry mol (moleculeRelabel input e))
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (c : input.detectedMultiCenterMolecule.Center) (node : Node)
    (current : node.atom = c.1.val) (reached : Reached mol node)
    (data : OccurrenceData input mol c node) (reflected : Bool)
    (childAgree : AgreeOn (StrictDescendant mol node) mol
      (pullback (moleculeRelabel input e) (observedGeometry input reflected))
      (observedGeometry input reflected))
    (depth : Nat) (references : List input.Atom)
    (historyFixed : ∀ atom ∈ node.history, moleculeRelabel input e atom = atom)
    (fixedReferences : ∀ reference ∈ references, ((e : Equiv.Perm input.Atom) reference).val = reference.val)
    (a b : Fin 4)
    (moves : moleculeRelabel input e (referenceAt input mol c node data a).val =
      (referenceAt input mol c node data b).val) :
    fallback input mol c node data depth (observedGeometry input reflected) references b =
      flipBy (relativeSign input.detectedMultiCenterMolecule cfg ePhys c)
        (fallback input mol c node data depth (observedGeometry input reflected) references a) := by
  have contextFixed : ∀ mark ∈ references.map Fin.val,
      moleculeRelabel input e mark = mark := by
    intro mark member
    rw [List.mem_map] at member
    obtain ⟨reference, refMember, rfl⟩ := member
    exact (relabelOf_val input (e : Equiv.Perm input.Atom) reference).trans
      (fixedReferences reference refMember)
  have core := actual_evaluateFallback_transport input mol agreement admissible supported single
    cfg e ePhys samePerm sym calibrated c node current reached reflected childAgree
    data.atoms data.rawFrame depth (references.map Fin.val) (referenceAt input mol c node data a).val
  rw [mapNode_eq_of_history_fixed mol (moleculeRelabel input e) node reached historyFixed,
      map_eq_self_of_pointwise (moleculeRelabel input e) (references.map Fin.val) contextFixed,
      moves] at core
  unfold fallback
  exact core

/-- **Even actual fallback equality at a fixed occurrence.** If the sign at the current centre is
`1`, the two corresponding actual fallbacks at the fixed occurrence are equal. -/
theorem actual_fallback_eq_of_even_slot
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (e : input.moleculeGraph.Aut) (ePhys : input.detectedMultiCenterMolecule.Aut)
    (samePerm : (ePhys : Equiv.Perm input.Atom) = (e : Equiv.Perm input.Atom))
    (sym : StructuralSymmetry mol (moleculeRelabel input e))
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (c : input.detectedMultiCenterMolecule.Center) (node : Node)
    (current : node.atom = c.1.val) (reached : Reached mol node)
    (data : OccurrenceData input mol c node) (reflected : Bool)
    (childAgree : AgreeOn (StrictDescendant mol node) mol
      (pullback (moleculeRelabel input e) (observedGeometry input reflected))
      (observedGeometry input reflected))
    (depth : Nat) (references : List input.Atom)
    (historyFixed : ∀ atom ∈ node.history, moleculeRelabel input e atom = atom)
    (fixedReferences : ∀ reference ∈ references, ((e : Equiv.Perm input.Atom) reference).val = reference.val)
    (a b : Fin 4)
    (moves : moleculeRelabel input e (referenceAt input mol c node data a).val =
      (referenceAt input mol c node data b).val)
    (even : relativeSign input.detectedMultiCenterMolecule cfg ePhys c = 1) :
    fallback input mol c node data depth (observedGeometry input reflected) references b =
      fallback input mol c node data depth (observedGeometry input reflected) references a := by
  have h := actual_fallback_transport_of_slot input mol agreement admissible supported single
    cfg e ePhys samePerm sym calibrated c node current reached data reflected childAgree depth
    references historyFixed fixedReferences a b moves
  rw [flipBy_eq_id (relativeSign input.detectedMultiCenterMolecule cfg ePhys c) even] at h
  simpa using h


end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalTransport.map_eq_self_of_pointwise
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalTransport.sign_swap_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalTransport.strictDescendant_child
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalTransport.strictDescendant_closed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalTransport.actual_evaluateFallback_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalTransport.actual_fallback_transport_of_slot
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalTransport.actual_fallback_eq_of_even_slot
