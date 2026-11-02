import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness
import TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision
import TetraStereo.OneCenter.FinitePhysicalBranchSearch
import TetraStereo.OneCenter.FiniteHistoryResidualReach
import TetraStereo.OneCenter.FinitePrunedMapSearch
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Finite search for retained-context auxiliary branch transport

The search below uses the single generic `FinitePrunedMapSearch.searchAux` engine. Its candidate
is one whole-molecule map, checked for atom labels, bond orders, detected-center membership, every
history fix, the selected ligand image, and every signed center law in the component computed by
`FiniteHistoryResidualReach`. No per-center choices are made.
-/

namespace TetraStereo.OneCenter.FiniteAuxiliaryBranchTransport

open FinitePhysicalBranchSearch FiniteHistoryResidualReach
open LocalizedRecursiveAuxiliaryPhysicalCorrectness
open RootedTetrahedralBranchSymmetry
open LocalizedActualPhysicalBranchDecision
open RetainedCoherentSymmetry
open CertifiedLocalizedCIPInput
open DeclarativeCIP

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (m : MultiCenterMolecule V)

/-- Constraints already forced by the source assignments in `seen`. -/
def AuxiliaryPrefixCompatible (history : List V) (source target : V)
    (f : V → V) (seen : List V) : Prop :=
  (∀ u ∈ seen, ∀ v ∈ seen, f u = f v → u = v) ∧
  (∀ v ∈ seen, m.mol.atomZ (f v) = m.mol.atomZ v) ∧
  (∀ v ∈ seen, m.mol.atomMass (f v) = m.mol.atomMass v) ∧
  (∀ v ∈ seen, m.mol.formalCharge (f v) = m.mol.formalCharge v) ∧
  (∀ v ∈ seen, v ∈ m.centers ↔ f v ∈ m.centers) ∧
  (∀ u ∈ seen, ∀ v ∈ seen, m.mol.bond (f u) (f v) = m.mol.bond u v) ∧
  (∀ x ∈ seen, x ∈ history → f x = x) ∧
  (source ∈ seen → f source = target)

/-- Executable prefix gate for the context-specific constraints. -/
def auxiliaryPrefixCheck (history : List V) (source target : V)
    (f : V → V) (seen : List V) : Bool :=
  seen.all (fun u => seen.all (fun v => decide (f u = f v → u = v))) &&
  seen.all (fun v => decide (m.mol.atomZ (f v) = m.mol.atomZ v)) &&
  seen.all (fun v => decide (m.mol.atomMass (f v) = m.mol.atomMass v)) &&
  seen.all (fun v => decide (m.mol.formalCharge (f v) = m.mol.formalCharge v)) &&
  seen.all (fun v => decide (v ∈ m.centers ↔ f v ∈ m.centers)) &&
  seen.all (fun u => seen.all (fun v => decide (m.mol.bond (f u) (f v) = m.mol.bond u v))) &&
  seen.all (fun x => if x ∈ history then decide (f x = x) else true) &&
  (if source ∈ seen then decide (f source = target) else true)

theorem auxiliaryPrefixCheck_eq_true_iff (history : List V) (source target : V)
    (f : V → V) (seen : List V) :
    auxiliaryPrefixCheck m history source target f seen = true ↔
      AuxiliaryPrefixCompatible m history source target f seen := by
  unfold auxiliaryPrefixCheck AuxiliaryPrefixCompatible
  simp [List.all_eq_true, decide_eq_true_eq, and_assoc, imp_iff_not_or]

/-- Full map checks independent of stereo signs. -/
def fullMapConstitutionOK (f : V → V) : Bool :=
  decide (((∀ v, m.mol.atomZ (f v) = m.mol.atomZ v) ∧
      (∀ v, m.mol.atomMass (f v) = m.mol.atomMass v) ∧
      (∀ v, m.mol.formalCharge (f v) = m.mol.formalCharge v) ∧
      (∀ u v, m.mol.bond (f u) (f v) = m.mol.bond u v)) ∧
    (∀ v, v ∈ m.centers ↔ f v ∈ m.centers))

theorem fullMapConstitutionOK_iff (f : V → V) :
    fullMapConstitutionOK m f = true ↔
      (((∀ v, m.mol.atomZ (f v) = m.mol.atomZ v) ∧
        (∀ v, m.mol.atomMass (f v) = m.mol.atomMass v) ∧
        (∀ v, m.mol.formalCharge (f v) = m.mol.formalCharge v) ∧
        (∀ u v, m.mol.bond (f u) (f v) = m.mol.bond u v)) ∧
       (∀ v, v ∈ m.centers ↔ f v ∈ m.centers)) := by
  simp [fullMapConstitutionOK, decide_eq_true_eq]

/-- One total map, required to satisfy all history, ligand, and residual-component constraints. -/
def fullAuxiliaryCandidateOK (cfg : m.Configuration) (history : List V)
    (source target : V) (mirror : Bool) (f : V → V) : Bool :=
  decide (Function.Injective f) &&
    fullMapConstitutionOK m f &&
    decide (∀ x ∈ history, f x = x) &&
    decide (f source = target) &&
    decide (∀ d : m.Center,
      d.1 ∈ historyResidualReachSet m.mol history source →
        FinitePhysicalBranchSearch.functionSignOK m cfg mirror f d = true)

/-- Finite executable decision for the generic retained-history relation on `m`. -/
def decideAuxiliaryComponentTransport (cfg : m.Configuration) (history : List V)
    (source target : V) (mirror : Bool) (vertices : List V) : Bool :=
  FinitePrunedMapSearch.searchAux
    (fun f seen => auxiliaryPrefixCheck m history source target f seen)
    (fun f => fullAuxiliaryCandidateOK m cfg history source target mirror f)
    vertices vertices [] id

/-- Proposition represented by `decideAuxiliaryComponentTransport`; the automorphism is of the
whole molecule and its sign requirements apply exactly to the deleted-history component. -/
def AuxiliaryComponentTransport (cfg : m.Configuration) (history : List V)
    (source target : V) (mirror : Bool) : Prop :=
  ∃ E : m.Aut,
    (∀ x ∈ history, (E : Equiv.Perm V) x = x) ∧
    (E : Equiv.Perm V) source = target ∧
    ∀ d : m.Center, InComponent m.mol history source d.1 →
      m.configurationSign cfg d * permHandedness (m.ligandPermAt E d) =
        physicalMirrorFactor mirror *
          m.configurationSign cfg (m.centerPerm E d)

theorem functionSignOK_iff_componentLaw (cfg : m.Configuration) (mirror : Bool)
    (E : m.Aut) (d : m.Center) :
    FinitePhysicalBranchSearch.functionSignOK m cfg mirror (E : Equiv.Perm V) d = true ↔
      m.configurationSign cfg d * permHandedness (m.ligandPermAt E d) =
        physicalMirrorFactor mirror * m.configurationSign cfg (m.centerPerm E d) := by
  have hcenter : (E : Equiv.Perm V) d.1 ∈ m.centers := (m.centerPerm E d).2
  have hcheck := FinitePhysicalBranchSearch.functionSignOK_perm m cfg mirror
    (E : Equiv.Perm V) d
  rw [hcheck, FinitePhysicalBranchTransport.signOK, dif_pos hcenter, decide_eq_true_iff]
  have himage : (⟨(E : Equiv.Perm V) d.1, hcenter⟩ : m.Center) = m.centerPerm E d :=
    Subtype.ext rfl
  rw [himage, FinitePhysicalBranchTransport.localFun_eq m E d,
    FinitePhysicalBranchTransport.funSign_perm]
  have hunits := FinitePhysicalBranchTransport.sign_equation_iff
    (Equiv.Perm.sign (cfg d))
    (Equiv.Perm.sign (m.ligandPermAt E d))
    (Equiv.Perm.sign (cfg (m.centerPerm E d))) mirror
  simpa [MultiCenterMolecule.configurationSign, permHandedness,
    CertifiedLocalizedCIPInput.physicalMirrorFactor] using hunits.symm

theorem fullAuxiliaryCandidateOK_of_aut (cfg : m.Configuration) (history : List V)
    (source target : V) (mirror : Bool) (E : m.Aut)
    (historyFixed : ∀ x ∈ history, (E : Equiv.Perm V) x = x)
    (ligandSent : (E : Equiv.Perm V) source = target)
    (componentLaw : ∀ d : m.Center, InComponent m.mol history source d.1 →
      m.configurationSign cfg d * permHandedness (m.ligandPermAt E d) =
        physicalMirrorFactor mirror * m.configurationSign cfg (m.centerPerm E d)) :
    fullAuxiliaryCandidateOK m cfg history source target mirror (E : Equiv.Perm V) = true := by
  unfold fullAuxiliaryCandidateOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨decide_eq_true_eq.mpr E.1.injective,
      (fullMapConstitutionOK_iff m (E : Equiv.Perm V)).mpr ?_⟩,
      decide_eq_true_eq.mpr historyFixed⟩,
      decide_eq_true_eq.mpr ligandSent⟩, ?_⟩
  · exact ⟨E.property.1, E.property.2⟩
  · apply decide_eq_true_eq.mpr
    intro d hd
    exact (functionSignOK_iff_componentLaw m cfg mirror E d).2
      (componentLaw d ((mem_historyResidualReachSet_iff m.mol history source d.1).mp hd))

theorem fullAuxiliaryCandidateOK_true_exists_transport (cfg : m.Configuration)
    (history : List V) (source target : V) (mirror : Bool) (f : V → V)
    (h : fullAuxiliaryCandidateOK m cfg history source target mirror f = true) :
    AuxiliaryComponentTransport m cfg history source target mirror := by
  have hparts := h
  simp only [fullAuxiliaryCandidateOK, Bool.and_eq_true, decide_eq_true_eq] at hparts
  rcases hparts with ⟨⟨⟨⟨hinj, hconstitutive⟩, hhistory⟩, hligand⟩, hsigns⟩
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  let e : Equiv.Perm V := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hconst := (fullMapConstitutionOK_iff m f).mp hconstitutive
  have heaut : e ∈ m.Aut := by
    change e ∈ m.mol.Aut ∧ m.PreservesCenters e
    refine ⟨?_, ?_⟩
    · change m.mol.IsAutomorphism e
      simpa [e] using hconst.1
    · intro v
      simpa [e] using hconst.2 v
  let E : m.Aut := ⟨e, heaut⟩
  refine ⟨E, ?_, ?_, ?_⟩
  · simpa [E, e] using hhistory
  · simpa [E, e] using hligand
  · intro d hd
    have h := hsigns d ((mem_historyResidualReachSet_iff m.mol history source d.1).2 hd)
    exact (functionSignOK_iff_componentLaw m cfg mirror E d).1 (by simpa [E, e] using h)

theorem decideAuxiliaryComponentTransport_iff (cfg : m.Configuration)
    (history : List V) (source target : V) (mirror : Bool)
    (vertices : List V) (verticesNodup : vertices.Nodup)
    (verticesComplete : ∀ v, v ∈ vertices) :
    decideAuxiliaryComponentTransport m cfg history source target mirror vertices = true ↔
      AuxiliaryComponentTransport m cfg history source target mirror := by
  unfold decideAuxiliaryComponentTransport AuxiliaryComponentTransport
  constructor
  · intro h
    obtain ⟨result, _trace, hleaf⟩ :=
      (FinitePrunedMapSearch.searchAux_eq_true_iff_trace
        (fun f seen => auxiliaryPrefixCheck m history source target f seen)
        (fun f => fullAuxiliaryCandidateOK m cfg history source target mirror f)
        vertices vertices [] id).mp h
    exact fullAuxiliaryCandidateOK_true_exists_transport m cfg history source target mirror
      result hleaf
  · rintro ⟨E, hhistory, hligand, hcomponent⟩
    have hleaf := fullAuxiliaryCandidateOK_of_aut m cfg history source target mirror E
      hhistory hligand hcomponent
    have hprefix : ∀ (f : V → V) (seen : List V),
        (∀ v ∈ seen, f v = (E : Equiv.Perm V) v) → ∀ x, x ∉ seen →
          auxiliaryPrefixCheck m history source target
            (Function.update f x ((E : Equiv.Perm V) x)) (x :: seen) = true := by
      intro f seen agreement x xFresh
      have agreement' : ∀ v ∈ x :: seen,
          Function.update f x ((E : Equiv.Perm V) x) v = (E : Equiv.Perm V) v := by
        intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · simp [Function.update_self]
        · have hne : x ≠ v := by
            intro heq
            subst x
            exact xFresh hv
          rw [Function.update_of_ne hne.symm]
          exact agreement v hv
      rw [auxiliaryPrefixCheck_eq_true_iff]
      let GE : m.mol.Aut := ⟨(E : Equiv.Perm V), E.property.1⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hu v hv heq
        apply (E : Equiv.Perm V).injective
        rw [← agreement' u hu, ← agreement' v hv]
        exact heq
      · intro v hv
        rw [agreement' v hv]
        exact MoleculeGraph.Aut.atomZ_eq (m := m.mol) GE v
      · intro v hv
        rw [agreement' v hv]
        exact MoleculeGraph.Aut.atomMass_eq (m := m.mol) GE v
      · intro v hv
        rw [agreement' v hv]
        exact MoleculeGraph.Aut.formalCharge_eq (m := m.mol) GE v
      · intro v hv
        rw [agreement' v hv]
        exact MultiCenterMolecule.Aut.mem_centers_iff (m := m) (e := E) v
      · intro u hu v hv
        rw [agreement' u hu, agreement' v hv]
        exact MoleculeGraph.Aut.bond_eq (m := m.mol) GE u v
      · intro z hz zHistory
        rw [agreement' z hz]
        exact hhistory z zHistory
      · intro sourceSeen
        rw [agreement' source sourceSeen]
        exact hligand
    exact FinitePrunedMapSearch.searchAux_true_of_target
      (fun f seen => auxiliaryPrefixCheck m history source target f seen)
      (fun f => fullAuxiliaryCandidateOK m cfg history source target mirror f)
      vertices vertices [] id (E : Equiv.Perm V) hleaf
      verticesNodup (by simp) (fun v => Or.inl (verticesComplete v))
      verticesComplete (by simp) hprefix

/-- Retained-history transport is exactly invariant under the accepted per-center frame
reindexing. Reachability itself is unchanged because `reindexFrames` keeps the graph verbatim;
each center sign is transported by the existing pointwise frame-sign theorem. -/
theorem auxiliaryComponentTransport_reindexFrames_iff
    (τ : m.Center → Equiv.Perm (Fin 4)) (cfg : m.Configuration)
    (history : List V) (source target : V) (mirror : Bool) :
    AuxiliaryComponentTransport (m.reindexFrames τ) (m.reindexConfiguration τ cfg)
        history source target mirror ↔
      AuxiliaryComponentTransport m cfg history source target mirror := by
  constructor
  · rintro ⟨E, hhistory, hligand, hcomponent⟩
    let E0 := m.autUnreindex τ E
    have Eeq : m.autReindex τ E0 = E := by simp [E0]
    refine ⟨E0, ?_, ?_, ?_⟩
    · simpa [E0] using hhistory
    · simpa [E0] using hligand
    · intro d hd
      have hnew := hcomponent d (by simpa using hd)
      have hnew' :
          (m.reindexFrames τ).configurationSign (m.reindexConfiguration τ cfg) d *
              permHandedness ((m.reindexFrames τ).ligandPermAt
                (m.autReindex τ E0) d) =
            physicalMirrorFactor mirror *
              (m.reindexFrames τ).configurationSign (m.reindexConfiguration τ cfg)
                ((m.reindexFrames τ).centerPerm (m.autReindex τ E0) d) := by
        simpa [Eeq] using hnew
      exact (MultiCenterMolecule.branchTransportSign_reindexFrames_iff
        m τ cfg E0 d mirror).1 hnew'
  · rintro ⟨E, hhistory, hligand, hcomponent⟩
    let Eτ := m.autReindex τ E
    have Eeq : m.autUnreindex τ Eτ = E := by simp [Eτ]
    refine ⟨Eτ, ?_, ?_, ?_⟩
    · simpa [Eτ] using hhistory
    · simpa [Eτ] using hligand
    · intro d hd
      have hold := hcomponent d (by simpa using hd)
      have hnew := (MultiCenterMolecule.branchTransportSign_reindexFrames_iff
        m τ cfg E d mirror).2 hold
      simpa [Eτ, CertifiedLocalizedCIPInput.physicalMirrorFactor] using hnew

/-- Equality transport for the generic retained-history relation. This isolates dependent
configuration casts from frame-specific facts. -/
theorem auxiliaryComponentTransport_congr
    {m₁ m₂ : MultiCenterMolecule V} (hm : m₁ = m₂)
    (cfg₁ : m₁.Configuration) (cfg₂ : m₂.Configuration)
    (hcfg : Eq.mp (congrArg (fun n : MultiCenterMolecule V => n.Configuration) hm) cfg₁ = cfg₂)
    (history : List V) {source₁ source₂ target₁ target₂ : V}
    (hsource : source₁ = source₂) (htarget : target₁ = target₂) (mirror : Bool) :
    AuxiliaryComponentTransport m₁ cfg₁ history source₁ target₁ mirror ↔
      AuxiliaryComponentTransport m₂ cfg₂ history source₂ target₂ mirror := by
  cases hm
  cases hcfg
  cases hsource
  cases htarget
  rfl

/-- Configuration on the executable canonical frame whose reindexing is the accepted detected
configuration. The convention subtracts the frame permutation on reindexing. -/
def canonicalAuxiliaryConfiguration
    (input : LocalizedRuleMajorReference.Input)
    (τ : (actualCanonicalMolecule input.certified).Center → Equiv.Perm (Fin 4))
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration) :
    (actualCanonicalMolecule input.certified).Configuration :=
  fun c => cfg c * τ c

theorem canonicalAuxiliaryConfiguration_reindex
    (input : LocalizedRuleMajorReference.Input)
    (τ : (actualCanonicalMolecule input.certified).Center → Equiv.Perm (Fin 4))
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration) :
    (actualCanonicalMolecule input.certified).reindexConfiguration τ
        (canonicalAuxiliaryConfiguration input τ cfg) = cfg := by
  funext c
  simp [canonicalAuxiliaryConfiguration, MultiCenterMolecule.reindexConfiguration]

/-! ## Exact specialization to the accepted auxiliary transport -/

variable {input : LocalizedRuleMajorReference.Input}
variable {target : input.certified.LocalizedCIPOccurrence
  (LocalizedUniversalReference.carrierFuel input)}
variable {unit : DeclarativeCIP.DetectedOccurrence input.certified.moleculeGraph}
variable {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}

theorem auxiliaryComponentTransport_iff_auxiliaryBranchTransport
    (frames : LocalizedRuleMajorReference.ContextFrameCompilation input target unit targetUnit)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (a b : Fin 4) (mirror : Bool) :
    AuxiliaryComponentTransport input.certified.detectedMultiCenterMolecule cfg
      target.1.node.history
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation a))
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation b)) mirror ↔
    ∃ σ : input.certified.moleculeGraph.Aut,
      AuxiliaryBranchTransport frames σ cfg a b mirror := by
  constructor
  · rintro ⟨E, hhistory, hligand, hcomponent⟩
    let σ' : input.certified.moleculeGraph.Aut :=
      ⟨(E : Equiv.Perm input.certified.Atom), E.property.1⟩
    have hE : input.certified.physicalDetectedAut σ' = E := by
      apply Subtype.ext
      rfl
    refine ⟨σ', ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa using hhistory
    · simpa using hligand
    · intro d hd
      simpa [hE] using hcomponent d hd
  · rintro ⟨σ', h⟩
    refine ⟨input.certified.physicalDetectedAut σ', ?_, ?_, ?_⟩
    · exact h.historyFixed
    · exact h.ligandSent
    · exact h.componentLaw

theorem decideAuxiliaryComponentTransport_exact
    (frames : LocalizedRuleMajorReference.ContextFrameCompilation input target unit targetUnit)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (a b : Fin 4) (mirror : Bool) (vertices : List input.certified.Atom)
    (verticesNodup : vertices.Nodup) (verticesComplete : ∀ v, v ∈ vertices) :
    decideAuxiliaryComponentTransport input.certified.detectedMultiCenterMolecule cfg
      target.1.node.history
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation a))
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation b)) mirror vertices = true ↔
    ∃ σ : input.certified.moleculeGraph.Aut,
      AuxiliaryBranchTransport frames σ cfg a b mirror := by
  rw [decideAuxiliaryComponentTransport_iff _ _ _ _ _ _ vertices verticesNodup verticesComplete]
  exact auxiliaryComponentTransport_iff_auxiliaryBranchTransport frames cfg a b mirror



/-- Exact canonical-frame search, parameterized by the accepted reindexing witness. The source
and target are the actual detected ligand atoms, which are the same atom identifiers in the
canonical graph; frame reindexing changes their slot labels but does not rename atoms. -/
theorem decideCanonicalAuxiliaryBranchTransport_exact
    {input : LocalizedRuleMajorReference.Input}
    {target : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input)}
    {unit : DeclarativeCIP.DetectedOccurrence input.certified.moleculeGraph}
    {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
    (frames : LocalizedRuleMajorReference.ContextFrameCompilation input target unit targetUnit)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (τ : (actualCanonicalMolecule input.certified).Center → Equiv.Perm (Fin 4))
    (hτ : (actualCanonicalMolecule input.certified).reindexFrames τ =
      input.certified.detectedMultiCenterMolecule)
    (a b : Fin 4) (mirror : Bool) (vertices : List input.certified.Atom)
    (verticesNodup : vertices.Nodup) (verticesComplete : ∀ v, v ∈ vertices) :
    decideAuxiliaryComponentTransport (actualCanonicalMolecule input.certified)
      (canonicalAuxiliaryConfiguration input τ cfg) target.1.node.history
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation a))
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation b)) mirror vertices = true ↔
    ∃ σ : input.certified.moleculeGraph.Aut,
      AuxiliaryBranchTransport frames σ cfg a b mirror := by
  let m := actualCanonicalMolecule input.certified
  let cfgC := canonicalAuxiliaryConfiguration input τ cfg
  let cfgR := m.reindexConfiguration τ cfgC
  have canonicalExact := decideAuxiliaryComponentTransport_iff m cfgC
    target.1.node.history
    (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
      (frames.detectedLigandPermutation a))
    (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
      (frames.detectedLigandPermutation b)) mirror vertices verticesNodup verticesComplete
  have frameReindex := auxiliaryComponentTransport_reindexFrames_iff m τ cfgC
    target.1.node.history
    (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
      (frames.detectedLigandPermutation a))
    (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
      (frames.detectedLigandPermutation b)) mirror
  have cfgEq : cfgR = cfg := by
    dsimp [cfgR, cfgC, m]
    exact canonicalAuxiliaryConfiguration_reindex input τ cfg
  have hcfg : Eq.mp (congrArg (fun n : MultiCenterMolecule input.certified.Atom => n.Configuration) hτ)
      cfgR = cfg := by
    have hc :
        congrArg (fun n : MultiCenterMolecule input.certified.Atom => n.Configuration) hτ =
          (rfl : (actualCanonicalMolecule input.certified).Configuration =
            (actualCanonicalMolecule input.certified).Configuration) :=
      Subsingleton.elim _ _
    rw [hc]
    exact cfgEq
  have modelBridge :
      AuxiliaryComponentTransport (m.reindexFrames τ) cfgR target.1.node.history
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
          (frames.detectedLigandPermutation a))
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
          (frames.detectedLigandPermutation b)) mirror ↔
      AuxiliaryComponentTransport input.certified.detectedMultiCenterMolecule cfg
        target.1.node.history
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
          (frames.detectedLigandPermutation a))
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
          (frames.detectedLigandPermutation b)) mirror :=
    auxiliaryComponentTransport_congr (m₁ := m.reindexFrames τ)
      (m₂ := input.certified.detectedMultiCenterMolecule) hτ cfgR cfg hcfg
      target.1.node.history
      (source₁ := input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation a))
      (source₂ := input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation a))
      (target₁ := input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation b))
      (target₂ := input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation b)) rfl rfl mirror
  exact canonicalExact.trans (frameReindex.symm.trans (modelBridge.trans
    (auxiliaryComponentTransport_iff_auxiliaryBranchTransport frames cfg a b mirror)))

end TetraStereo.OneCenter.FiniteAuxiliaryBranchTransport

assert_kernel_only TetraStereo.OneCenter.FiniteAuxiliaryBranchTransport.auxiliaryPrefixCheck_eq_true_iff
assert_kernel_only TetraStereo.OneCenter.FiniteAuxiliaryBranchTransport.functionSignOK_iff_componentLaw
assert_kernel_only TetraStereo.OneCenter.FiniteAuxiliaryBranchTransport.fullAuxiliaryCandidateOK_true_exists_transport
assert_kernel_only TetraStereo.OneCenter.FiniteAuxiliaryBranchTransport.decideAuxiliaryComponentTransport_iff
assert_kernel_only TetraStereo.OneCenter.FiniteAuxiliaryBranchTransport.auxiliaryComponentTransport_iff_auxiliaryBranchTransport
assert_kernel_only TetraStereo.OneCenter.FiniteAuxiliaryBranchTransport.decideAuxiliaryComponentTransport_exact

assert_kernel_only TetraStereo.OneCenter.FiniteAuxiliaryBranchTransport.decideCanonicalAuxiliaryBranchTransport_exact
assert_kernel_only TetraStereo.OneCenter.FiniteAuxiliaryBranchTransport.canonicalAuxiliaryConfiguration_reindex
assert_kernel_only TetraStereo.OneCenter.FiniteAuxiliaryBranchTransport.auxiliaryComponentTransport_reindexFrames_iff
assert_kernel_only TetraStereo.OneCenter.FiniteAuxiliaryBranchTransport.auxiliaryComponentTransport_congr
assert_kernel_only TetraStereo.OneCenter.FiniteAuxiliaryBranchTransport.canonicalAuxiliaryConfiguration_reindex
