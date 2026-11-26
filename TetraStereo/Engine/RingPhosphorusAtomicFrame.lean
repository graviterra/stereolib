import TetraStereo.Engine.RingPyramidalConstitution

/-! A molecular atomic-number order fixes the native three-coordinate P frame
at every real occurrence, including its incoming physical direction. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPhosphorusAtomicFrame
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActivePairs (Site)
open RingNestedActivePair (Reader)
open RingPyramidalSource
open RingPyramidalConstitution
open private direction_rank from TetraStereo.Engine.RingPyramidalConstitution

/-- Strict atomic-number order on a physical neighbor enumeration determines
the uppercase P reading on every ready reader. The occurrence's retained slot
correspondence is derived from the graph, including the incoming direction. -/
theorem pLabels_strict_atomic {i : Input} {q : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready q r) (a : i.certified.Atom)
    (selected : RingPyramidalPublication.focusP i q = some a)
    (enum : Fin 3 ≃ i.certified.moleculeGraph.Neighbor a) (records : Fin 3 → AtomSpec)
    (written : ∀ s, i.molecule.atoms[(enum s).val.val]? = some (records s))
    (descending : StrictAnti (fun s => (records s).element.atomicNumber)) :
    RingPyramidalPublication.pLabels i q r a =
      (readback? (inputGeometry i.certified)
        [(enum 0).val.val,(enum 1).val.val,(enum 2).val.val,a.val]).map fun h =>
        (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap) := by
  obtain ⟨d⟩ := selected_framed selected
  obtain ⟨e,ranked⟩ := direction_rank d selected enum
  let recsAt (s : Fin 3) := records (e s)
  have recs (s : Fin 3) : i.molecule.atoms[(d.atom s).val]? = some (recsAt s) := by
    rw [ranked s]
    exact written (e s)
  have strict : Function.Injective (fun s => (recsAt s).element.atomicNumber) := descending.injective.comp e.injective
  have legal : RingStereoSiblingPass.Legal (fun s => (recsAt s).element.atomicNumber)
      slots [e.symm 0,e.symm 1,e.symm 2] := by
    refine ⟨Equiv.Perm.map_finRange_perm e.symm,?_⟩
    simp only [List.map_cons,List.map_nil,recsAt,e.apply_symm_apply]
    have h01 := le_of_lt (descending (by decide : (0:Fin 3) < 1))
    have h02 := le_of_lt (descending (by decide : (0:Fin 3) < 2))
    have h12 := le_of_lt (descending (by decide : (1:Fin 3) < 2))
    simpa [List.pairwise_cons] using And.intro (And.intro h01 h02) h12
  have result := pLabels_first_Z d ready a recsAt recs strict
    (e.symm 0) (e.symm 1) (e.symm 2) legal
  have ids (s : Fin 3) : atomId d (e.symm s) = (enum s).val.val := by
    unfold atomId
    rw [ranked,e.apply_symm_apply]
  simpa only [ids] using result

/-- The actual distance-scheduled chemical state has the physical Z-ordered P
reading on every real occurrence. No earlier-label or frozen-store equality is assumed. -/
theorem state_strict_atomic {i : Input}
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i)
    (a : i.certified.Atom) (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some a)
    (phosphorus : RingPyramidalPublication.phosphorus i a = true)
    (enum : Fin 3 ≃ i.certified.moleculeGraph.Neighbor a) (records : Fin 3 → AtomSpec)
    (written : ∀ s, i.molecule.atoms[(enum s).val.val]? = some (records s))
    (descending : StrictAnti (fun s => (records s).element.atomicNumber)) :
    RingChemicalGraphProof.state i q = some
      ((readback? (inputGeometry i.certified)
        [(enum 0).val.val,(enum 1).val.val,(enum 2).val.val,a.val]).map fun h =>
        (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap)) := by
  have selected : RingPyramidalPublication.focusP i q = some a := by
    simp [RingPyramidalPublication.focusP,real,current,phosphorus]
  rw [RingChemicalGraphProof.state_eq,RingPyramidalPublication.publish,selected]
  exact congrArg some (pLabels_strict_atomic (RingChemicalGraphProof.ready admitted q)
    a selected enum records written descending)

end TetraStereo.Engine.RingPhosphorusAtomicFrame
assert_kernel_only TetraStereo.Engine.RingPhosphorusAtomicFrame.pLabels_strict_atomic
assert_kernel_only TetraStereo.Engine.RingPhosphorusAtomicFrame.state_strict_atomic
