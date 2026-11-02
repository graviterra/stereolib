import TetraStereo.OneCenter.LocalizedActualOrderedRootMirrorRule5Decision
import TetraStereo.OneCenter.LocalizedFirstSpherePhysicalPriority
import TetraStereo.Examples.TwoReferenceSupport.FixtureGraphDomain
import TetraStereo.Examples.TwoReferenceSupport.FixtureCalibration
import TetraStereo.Examples.TwoReferenceSupport.FixtureOccurrences
import TetraStereo.Examples.TwoReferenceSupport.FixtureReaderTransfer
import TetraStereo.Examples.TwoReferenceSupport.FixtureRootGeometry
import TetraStereo.KernelOnly

set_option autoImplicit false

































namespace TetraStereo.OneCenter
namespace LocalizedTwoReferenceFixturePhysicalInstance

open CertifiedLocalizedCIPInput
open RootedTetrahedralBranchSymmetry
open LocalizedTwoReferencePseudoasymmetryFixture
open FixtureOccurrences (occurrence4 occurrence7 occurrence11 occurrence14 occurrence19
  occurrence22 occurrence26 occurrence29 atom0 atom3 atom4 atom7 atom11 atom14 atom18 atom19
  atom22 atom26 atom29)

noncomputable section
open scoped Classical

/-! ## The physical domain -/

/-- The detected molecule of the fixture. -/
abbrev Physical := input.certified.detectedMultiCenterMolecule

/-- The accepted actual configuration. -/
abbrev cfg : Physical.Configuration := FixtureCalibration.actualConfiguration

/-- The actual root centre (atom `0`). -/
abbrev rootP : Physical.Center := FixtureOccurrences.rootCenter

/-- **The general rigid physical domain of the fixture at the root.**  Every non-root detected
centre is one of the eight accepted calibrated rigid centres. -/
theorem physicalDomain : ActualGeneralRigidPhysicalDomain input.certified Physical cfg rootP := by
  refine ⟨rfl, ?_⟩
  intro center hne
  have hmem : center.1 ∈ FixtureInventory.Input.tetrahedralCenterSet := center.2
  rw [FixtureInventory.detectedCenterSet] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · exact absurd (Subtype.ext h) hne
  · rw [show center = FixtureOccurrences.center4 from Subtype.ext h]
    exact Or.inr FixtureCalibration.actualCalibration4
  · rw [show center = FixtureOccurrences.center7 from Subtype.ext h]
    exact Or.inr FixtureCalibration.actualCalibration7
  · rw [show center = FixtureOccurrences.center11 from Subtype.ext h]
    exact Or.inr FixtureCalibration.actualCalibration11
  · rw [show center = FixtureOccurrences.center14 from Subtype.ext h]
    exact Or.inr FixtureCalibration.actualCalibration14
  · rw [show center = FixtureOccurrences.center19 from Subtype.ext h]
    exact Or.inr FixtureCalibration.actualCalibration19
  · rw [show center = FixtureOccurrences.center22 from Subtype.ext h]
    exact Or.inr FixtureCalibration.actualCalibration22
  · rw [show center = FixtureOccurrences.center26 from Subtype.ext h]
    exact Or.inr FixtureCalibration.actualCalibration26
  · rw [show center = FixtureOccurrences.center29 from Subtype.ext h]
    exact Or.inr FixtureCalibration.actualCalibration29

/-! ## Physical contexts at the eight accepted occurrences -/

/-- The physical context of one non-root centre at an accepted carrier occurrence. -/
def context (center : Physical.Center) (hne : center ≠ rootP)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1)
    (root_eq : rootP.1 = target.1.root) : DomainPhysicalContext input where
  singleBonded := FixtureGraphDomain.simpleBonded
  acyclic := FixtureGraphDomain.acyclic
  hcharge := FixtureGraphDomain.constantFormalCharge
  noDouble := FixtureGraphDomain.noLocalizedDoubleBondRecords
  cfg := cfg
  root := rootP
  domain := physicalDomain
  center := center
  center_ne_root := hne
  target := target
  targetCurrent := targetCurrent
  root_eq := root_eq

/-- The rigid branch of a calibrated centre. -/
def branch {center : Physical.Center} {hne : center ≠ rootP}
    {target : LocalizedUniversalReference.Occurrence input}
    {targetCurrent : target.1.node.current? = some center.1} {root_eq : rootP.1 = target.1.root}
    (calibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified Physical cfg center) :
    DomainPhysicalRigidBranch (context center hne target targetCurrent root_eq) :=
  ⟨localizedGeneralRigidPhysicalTerminalTwinCenter_false_of_physicalCalibrated calibrated⟩

/-! ## The canonical slots of a context -/

variable {ctx : DomainPhysicalContext input} (br : DomainPhysicalRigidBranch ctx)

/-- The frame slot carrying the canonical (ascending-index) ligand `i` of the centre. -/
def slotEquiv : Fin 4 ≃ Fin 4 :=
  (input.certified.canonicalLigandReindex ctx.center).symm.trans (ctx.frameData br).alpha.symm

theorem cursorAtom_slotEquiv (i : Fin 4) :
    cursorAtom ctx.singleBonded ctx.acyclic ((ctx.frame br).cursorAt (slotEquiv br i)) =
      input.certified.canonicalLigandAtom ctx.center i := by
  apply cursorAtom_eq_of_observed
  show ((ctx.frameData br).frame.cursorAt _).occurrence.1.node.current? = _
  rw [(ctx.frameData br).cursorAtom]
  simp only [slotEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [canonicalLigandReindex_spec, Equiv.apply_symm_apply]

theorem spatial_slotEquiv (i : Fin 4) :
    input.certified.spatialPointAt? (input.certified.canonicalLigandAtom ctx.center i) =
      some (ctx.pointsAt br (slotEquiv br i)) := by
  show _ = some ((ctx.frameData br).pointAt ((ctx.frameData br).alpha (slotEquiv br i)))
  simp only [slotEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  have h := (ctx.frameData br).observed
    ((input.certified.canonicalLigandReindex ctx.center).symm i)
  rw [canonicalLigandReindex_spec, Equiv.apply_symm_apply] at h
  exact h

theorem pointsAt_slotEquiv (points : Fin 4 → CartesianPoint3)
    (observed : ∀ i, input.certified.spatialPointAt?
      (input.certified.canonicalLigandAtom ctx.center i) = some (points i)) (i : Fin 4) :
    ctx.pointsAt br (slotEquiv br i) = points i :=
  Option.some.inj ((spatial_slotEquiv br i).symm.trans (observed i))

/-- The canonical priority between two canonical slots follows from their atomic numbers. -/
theorem canonicalPriority_slotEquiv_of_lt (z : Fin 4 → ℕ)
    (hz : ∀ i, input.certified.moleculeGraph.atomZ
      (input.certified.canonicalLigandAtom ctx.center i) = z i)
    {i j : Fin 4} (hlt : z j < z i) :
    ctx.canonicalPriority br (slotEquiv br i) (slotEquiv br j) := by
  apply ctx.canonicalPriority_of_atomZ_gt br
  rw [cursorAtom_slotEquiv, cursorAtom_slotEquiv, hz, hz]
  exact hlt

theorem finRange_map_perm (e : Fin 4 ≃ Fin 4) :
    ((List.finRange 4).map e).Perm (List.finRange 4) := by
  have nd : ((List.finRange 4).map e).Nodup := (List.nodup_finRange 4).map e.injective
  apply List.perm_of_nodup_nodup_toFinset_eq nd (List.nodup_finRange 4)
  have h₁ : ((List.finRange 4).map e).toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup nd]; simp)
  have h₂ : (List.finRange 4).toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup (List.nodup_finRange 4)]; simp)
  rw [h₁, h₂]

/-- **The generated letter from the canonical order and the accepted geometry.**  If the four
canonical ligands have atomic numbers `z` and `[i₀, i₁, i₂, i₃]` lists them in strictly
descending atomic number, the generated reference state at the context's occurrence is the
rational descriptor of the ligand points in that order. -/
theorem referenceState_of_canonicalData (br : DomainPhysicalRigidBranch ctx)
    (points : Fin 4 → CartesianPoint3)
    (observed : ∀ i, input.certified.spatialPointAt?
      (input.certified.canonicalLigandAtom ctx.center i) = some (points i))
    (z : Fin 4 → ℕ)
    (hz : ∀ i, input.certified.moleculeGraph.atomZ
      (input.certified.canonicalLigandAtom ctx.center i) = z i)
    (i₀ i₁ i₂ i₃ : Fin 4) (perm : [i₀, i₁, i₂, i₃].Perm (List.finRange 4))
    (d₀ : z i₁ < z i₀) (d₁ : z i₂ < z i₁) (d₂ : z i₃ < z i₂)
    (rs : RS)
    (geometry : RationalTetrahedralDescriptor [points i₀, points i₁, points i₂, points i₃] rs) :
    LocalizedUniversalReference.referenceState input ctx.target = some (.chiral rs) := by
  rw [ctx.referenceState_iff_canonicalPhysicalDescriptor br rs]
  refine ⟨[i₀, i₁, i₂, i₃].map (slotEquiv br), ⟨?_, ?_⟩, ?_⟩
  · exact (perm.map (slotEquiv br)).trans (finRange_map_perm (slotEquiv br))
  · have p : ∀ {i j : Fin 4}, z j < z i →
        ctx.canonicalPriority br (slotEquiv br i) (slotEquiv br j) :=
      fun h => canonicalPriority_slotEquiv_of_lt br z hz h
    simp only [List.map_cons, List.map_nil]
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
      (List.Pairwise.cons ?_ List.Pairwise.nil)))
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact p d₀
      · exact p (d₀.trans' d₁)
      · exact p ((d₀.trans' d₁).trans' d₂)
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact p d₁
      · exact p (d₁.trans' d₂)
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact p d₂
    · intro b hb
      simp at hb
  · simp only [List.map_cons, List.map_nil, pointsAt_slotEquiv br points observed]
    exact geometry

/-! ## The eight generated labels -/

section Labels

open FixtureInventory (fixtureAtom)
open FixtureCalibration

/-- The canonical atomic numbers of a `C(N)(H)(F)(C)` carbon in ascending atom-index order. -/
def zA : Fin 4 → ℕ := ![7, 1, 9, 6]

/-- The canonical atomic numbers of a `C(C)(H)(Cl)(Br)` carbon in ascending atom-index order. -/
def zB : Fin 4 → ℕ := ![6, 1, 17, 35]

private theorem permA : ([2, 0, 3, 1] : List (Fin 4)).Perm (List.finRange 4) := by decide
private theorem permB : ([3, 2, 0, 1] : List (Fin 4)).Perm (List.finRange 4) := by decide

theorem context4_ne : FixtureOccurrences.center4 ≠ rootP := by decide +kernel
theorem context7_ne : FixtureOccurrences.center7 ≠ rootP := by decide +kernel
theorem context11_ne : FixtureOccurrences.center11 ≠ rootP := by decide +kernel
theorem context14_ne : FixtureOccurrences.center14 ≠ rootP := by decide +kernel
theorem context19_ne : FixtureOccurrences.center19 ≠ rootP := by decide +kernel
theorem context22_ne : FixtureOccurrences.center22 ≠ rootP := by decide +kernel
theorem context26_ne : FixtureOccurrences.center26 ≠ rootP := by decide +kernel
theorem context29_ne : FixtureOccurrences.center29 ≠ rootP := by decide +kernel

def context4 := context FixtureOccurrences.center4 context4_ne occurrence4
  FixtureOccurrences.occurrence4_current_center FixtureOccurrences.occurrence4_root_eq
def context7 := context FixtureOccurrences.center7 context7_ne occurrence7
  FixtureOccurrences.occurrence7_current_center FixtureOccurrences.occurrence7_root_eq
def context11 := context FixtureOccurrences.center11 context11_ne occurrence11
  FixtureOccurrences.occurrence11_current_center FixtureOccurrences.occurrence11_root_eq
def context14 := context FixtureOccurrences.center14 context14_ne occurrence14
  FixtureOccurrences.occurrence14_current_center FixtureOccurrences.occurrence14_root_eq
def context19 := context FixtureOccurrences.center19 context19_ne occurrence19
  FixtureOccurrences.occurrence19_current_center FixtureOccurrences.occurrence19_root_eq
def context22 := context FixtureOccurrences.center22 context22_ne occurrence22
  FixtureOccurrences.occurrence22_current_center FixtureOccurrences.occurrence22_root_eq
def context26 := context FixtureOccurrences.center26 context26_ne occurrence26
  FixtureOccurrences.occurrence26_current_center FixtureOccurrences.occurrence26_root_eq
def context29 := context FixtureOccurrences.center29 context29_ne occurrence29
  FixtureOccurrences.occurrence29_current_center FixtureOccurrences.occurrence29_root_eq

def branch4 : DomainPhysicalRigidBranch context4 := branch actualCalibration4
def branch7 : DomainPhysicalRigidBranch context7 := branch actualCalibration7
def branch11 : DomainPhysicalRigidBranch context11 := branch actualCalibration11
def branch14 : DomainPhysicalRigidBranch context14 := branch actualCalibration14
def branch19 : DomainPhysicalRigidBranch context19 := branch actualCalibration19
def branch22 : DomainPhysicalRigidBranch context22 := branch actualCalibration22
def branch26 : DomainPhysicalRigidBranch context26 := branch actualCalibration26
def branch29 : DomainPhysicalRigidBranch context29 := branch actualCalibration29

/-- The atomic numbers of the canonical ligands of centre `4`. -/
theorem atomZ4 : ∀ i, FixtureInventory.Input.moleculeGraph.atomZ
    (FixtureInventory.Input.canonicalLigandAtom FixtureInventory.center4 i) = zA i := by
  intro i
  rw [canonicalLigands4]
  fin_cases i <;> decide +kernel

theorem atomZ7 : ∀ i, FixtureInventory.Input.moleculeGraph.atomZ
    (FixtureInventory.Input.canonicalLigandAtom FixtureInventory.center7 i) = zB i := by
  intro i
  rw [canonicalLigands7]
  fin_cases i <;> decide +kernel

theorem atomZ11 : ∀ i, FixtureInventory.Input.moleculeGraph.atomZ
    (FixtureInventory.Input.canonicalLigandAtom FixtureInventory.center11 i) = zA i := by
  intro i
  rw [canonicalLigands11]
  fin_cases i <;> decide +kernel

theorem atomZ14 : ∀ i, FixtureInventory.Input.moleculeGraph.atomZ
    (FixtureInventory.Input.canonicalLigandAtom FixtureInventory.center14 i) = zB i := by
  intro i
  rw [canonicalLigands14]
  fin_cases i <;> decide +kernel

theorem atomZ19 : ∀ i, FixtureInventory.Input.moleculeGraph.atomZ
    (FixtureInventory.Input.canonicalLigandAtom FixtureInventory.center19 i) = zA i := by
  intro i
  rw [canonicalLigands19]
  fin_cases i <;> decide +kernel

theorem atomZ22 : ∀ i, FixtureInventory.Input.moleculeGraph.atomZ
    (FixtureInventory.Input.canonicalLigandAtom FixtureInventory.center22 i) = zB i := by
  intro i
  rw [canonicalLigands22]
  fin_cases i <;> decide +kernel

theorem atomZ26 : ∀ i, FixtureInventory.Input.moleculeGraph.atomZ
    (FixtureInventory.Input.canonicalLigandAtom FixtureInventory.center26 i) = zA i := by
  intro i
  rw [canonicalLigands26]
  fin_cases i <;> decide +kernel

theorem atomZ29 : ∀ i, FixtureInventory.Input.moleculeGraph.atomZ
    (FixtureInventory.Input.canonicalLigandAtom FixtureInventory.center29 i) = zB i := by
  intro i
  rw [canonicalLigands29]
  fin_cases i <;> decide +kernel

/-- Geometry of the descending-Z order `[F, N, C, H]` at centre `4` (atoms `6, 3, 7, 5`). -/
theorem geometry4 : RationalTetrahedralDescriptor
    [canonicalPoint4 2, canonicalPoint4 0, canonicalPoint4 3, canonicalPoint4 1] RS.R := by
  refine ⟨_, _, _, _, rfl, ?_⟩
  show CartesianPoint3.orientedVolume _ _ _ _ < 0
  norm_num [canonicalPoint4, FixtureGeometry.pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, CartesianPoint3.orientedVolume]

theorem geometry7 : RationalTetrahedralDescriptor
    [canonicalPoint7 3, canonicalPoint7 2, canonicalPoint7 0, canonicalPoint7 1] RS.R := by
  refine ⟨_, _, _, _, rfl, ?_⟩
  show CartesianPoint3.orientedVolume _ _ _ _ < 0
  norm_num [canonicalPoint7, FixtureGeometry.pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, CartesianPoint3.orientedVolume]

theorem geometry11 : RationalTetrahedralDescriptor
    [canonicalPoint11 2, canonicalPoint11 0, canonicalPoint11 3, canonicalPoint11 1] RS.S := by
  refine ⟨_, _, _, _, rfl, ?_⟩
  show 0 < CartesianPoint3.orientedVolume _ _ _ _
  norm_num [canonicalPoint11, FixtureGeometry.pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, CartesianPoint3.orientedVolume]

theorem geometry14 : RationalTetrahedralDescriptor
    [canonicalPoint14 3, canonicalPoint14 2, canonicalPoint14 0, canonicalPoint14 1] RS.R := by
  refine ⟨_, _, _, _, rfl, ?_⟩
  show CartesianPoint3.orientedVolume _ _ _ _ < 0
  norm_num [canonicalPoint14, FixtureGeometry.pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, CartesianPoint3.orientedVolume]

theorem geometry19 : RationalTetrahedralDescriptor
    [canonicalPoint19 2, canonicalPoint19 0, canonicalPoint19 3, canonicalPoint19 1] RS.S := by
  refine ⟨_, _, _, _, rfl, ?_⟩
  show 0 < CartesianPoint3.orientedVolume _ _ _ _
  norm_num [canonicalPoint19, FixtureGeometry.pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, CartesianPoint3.orientedVolume]

theorem geometry22 : RationalTetrahedralDescriptor
    [canonicalPoint22 3, canonicalPoint22 2, canonicalPoint22 0, canonicalPoint22 1] RS.S := by
  refine ⟨_, _, _, _, rfl, ?_⟩
  show 0 < CartesianPoint3.orientedVolume _ _ _ _
  norm_num [canonicalPoint22, FixtureGeometry.pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, CartesianPoint3.orientedVolume]

theorem geometry26 : RationalTetrahedralDescriptor
    [canonicalPoint26 2, canonicalPoint26 0, canonicalPoint26 3, canonicalPoint26 1] RS.R := by
  refine ⟨_, _, _, _, rfl, ?_⟩
  show CartesianPoint3.orientedVolume _ _ _ _ < 0
  norm_num [canonicalPoint26, FixtureGeometry.pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, CartesianPoint3.orientedVolume]

theorem geometry29 : RationalTetrahedralDescriptor
    [canonicalPoint29 3, canonicalPoint29 2, canonicalPoint29 0, canonicalPoint29 1] RS.S := by
  refine ⟨_, _, _, _, rfl, ?_⟩
  show 0 < CartesianPoint3.orientedVolume _ _ _ _
  norm_num [canonicalPoint29, FixtureGeometry.pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, CartesianPoint3.orientedVolume]

/-- **Generated label at centre `4`: `R`.** -/
theorem label4 :
    LocalizedUniversalReference.referenceState input occurrence4 = some (.chiral RS.R) :=
  referenceState_of_canonicalData branch4 canonicalPoint4 canonicalObserved4 zA atomZ4
    2 0 3 1 permA (by decide) (by decide) (by decide) RS.R geometry4

/-- **Generated label at centre `7`: `R`.** -/
theorem label7 :
    LocalizedUniversalReference.referenceState input occurrence7 = some (.chiral RS.R) :=
  referenceState_of_canonicalData branch7 canonicalPoint7 canonicalObserved7 zB atomZ7
    3 2 0 1 permB (by decide) (by decide) (by decide) RS.R geometry7

/-- **Generated label at centre `11`: `S`.** -/
theorem label11 :
    LocalizedUniversalReference.referenceState input occurrence11 = some (.chiral RS.S) :=
  referenceState_of_canonicalData branch11 canonicalPoint11 canonicalObserved11 zA atomZ11
    2 0 3 1 permA (by decide) (by decide) (by decide) RS.S geometry11

/-- **Generated label at centre `14`: `R`.** -/
theorem label14 :
    LocalizedUniversalReference.referenceState input occurrence14 = some (.chiral RS.R) :=
  referenceState_of_canonicalData branch14 canonicalPoint14 canonicalObserved14 zB atomZ14
    3 2 0 1 permB (by decide) (by decide) (by decide) RS.R geometry14

/-- **Generated label at centre `19`: `S`.** -/
theorem label19 :
    LocalizedUniversalReference.referenceState input occurrence19 = some (.chiral RS.S) :=
  referenceState_of_canonicalData branch19 canonicalPoint19 canonicalObserved19 zA atomZ19
    2 0 3 1 permA (by decide) (by decide) (by decide) RS.S geometry19

/-- **Generated label at centre `22`: `S`.** -/
theorem label22 :
    LocalizedUniversalReference.referenceState input occurrence22 = some (.chiral RS.S) :=
  referenceState_of_canonicalData branch22 canonicalPoint22 canonicalObserved22 zB atomZ22
    3 2 0 1 permB (by decide) (by decide) (by decide) RS.S geometry22

/-- **Generated label at centre `26`: `R`.** -/
theorem label26 :
    LocalizedUniversalReference.referenceState input occurrence26 = some (.chiral RS.R) :=
  referenceState_of_canonicalData branch26 canonicalPoint26 canonicalObserved26 zA atomZ26
    2 0 3 1 permA (by decide) (by decide) (by decide) RS.R geometry26

/-- **Generated label at centre `29`: `S`.** -/
theorem label29 :
    LocalizedUniversalReference.referenceState input occurrence29 = some (.chiral RS.S) :=
  referenceState_of_canonicalData branch29 canonicalPoint29 canonicalObserved29 zB atomZ29
    3 2 0 1 permB (by decide) (by decide) (by decide) RS.S geometry29

end Labels

/-! ## The generated molecular-reader labels -/

section Reader

/-- The molecular units of the eight centres (root `0`, actual atom paths). -/
def unit4 : DeclarativeCIP.DetectedOccurrence input.certified.moleculeGraph :=
  ⟨⟨atom0, [atom3, atom4]⟩, by decide +kernel⟩
def unit11 : DeclarativeCIP.DetectedOccurrence input.certified.moleculeGraph :=
  ⟨⟨atom0, [atom3, atom11]⟩, by decide +kernel⟩
def unit19 : DeclarativeCIP.DetectedOccurrence input.certified.moleculeGraph :=
  ⟨⟨atom0, [atom18, atom19]⟩, by decide +kernel⟩
def unit26 : DeclarativeCIP.DetectedOccurrence input.certified.moleculeGraph :=
  ⟨⟨atom0, [atom18, atom26]⟩, by decide +kernel⟩
def unit7 : DeclarativeCIP.DetectedOccurrence input.certified.moleculeGraph :=
  ⟨⟨atom0, [atom3, atom4, atom7]⟩, by decide +kernel⟩
def unit14 : DeclarativeCIP.DetectedOccurrence input.certified.moleculeGraph :=
  ⟨⟨atom0, [atom3, atom11, atom14]⟩, by decide +kernel⟩
def unit22 : DeclarativeCIP.DetectedOccurrence input.certified.moleculeGraph :=
  ⟨⟨atom0, [atom18, atom19, atom22]⟩, by decide +kernel⟩
def unit29 : DeclarativeCIP.DetectedOccurrence input.certified.moleculeGraph :=
  ⟨⟨atom0, [atom18, atom26, atom29]⟩, by decide +kernel⟩

/-- A descriptor-map entry whose localized label is a chiral letter is that letter. -/
theorem descriptor_eq_of_label {entry : Option DeclarativeCIP.Descriptor} {rs : RS}
    (h : entry.bind DeclarativeCIP.Descriptor.toLocalizedLabel = some (.chiral rs)) :
    entry = some (match rs with | RS.R => DeclarativeCIP.Descriptor.R | RS.S => .S) := by
  cases entry with
  | none => simp at h
  | some d =>
      cases d <;> cases rs <;> simp [DeclarativeCIP.Descriptor.toLocalizedLabel] at h ⊢

theorem mapLabel4 : (actualReferenceDescriptorMap input unit4).bind
    DeclarativeCIP.Descriptor.toLocalizedLabel = some (.chiral RS.R) := by
  rw [actualReferenceDescriptorMap_readback input FixtureGraphDomain.simpleBonded
    FixtureGraphDomain.acyclic unit4 occurrence4 FixtureReaderTransfer.molecularFrameUnit4]
  exact label4

theorem mapLabel11 : (actualReferenceDescriptorMap input unit11).bind
    DeclarativeCIP.Descriptor.toLocalizedLabel = some (.chiral RS.S) := by
  rw [actualReferenceDescriptorMap_readback input FixtureGraphDomain.simpleBonded
    FixtureGraphDomain.acyclic unit11 occurrence11
    FixtureReaderTransfer.molecularFrameUnit11]
  exact label11

theorem mapLabel19 : (actualReferenceDescriptorMap input unit19).bind
    DeclarativeCIP.Descriptor.toLocalizedLabel = some (.chiral RS.S) := by
  rw [actualReferenceDescriptorMap_readback input FixtureGraphDomain.simpleBonded
    FixtureGraphDomain.acyclic unit19 occurrence19
    FixtureReaderTransfer.molecularFrameUnit19]
  exact label19

theorem mapLabel26 : (actualReferenceDescriptorMap input unit26).bind
    DeclarativeCIP.Descriptor.toLocalizedLabel = some (.chiral RS.R) := by
  rw [actualReferenceDescriptorMap_readback input FixtureGraphDomain.simpleBonded
    FixtureGraphDomain.acyclic unit26 occurrence26
    FixtureReaderTransfer.molecularFrameUnit26]
  exact label26

theorem mapLabel7 : (actualReferenceDescriptorMap input unit7).bind
    DeclarativeCIP.Descriptor.toLocalizedLabel = some (.chiral RS.R) := by
  rw [actualReferenceDescriptorMap_readback input FixtureGraphDomain.simpleBonded
    FixtureGraphDomain.acyclic unit7 occurrence7 FixtureReaderTransfer.molecularFrameUnit7]
  exact label7

theorem mapLabel14 : (actualReferenceDescriptorMap input unit14).bind
    DeclarativeCIP.Descriptor.toLocalizedLabel = some (.chiral RS.R) := by
  rw [actualReferenceDescriptorMap_readback input FixtureGraphDomain.simpleBonded
    FixtureGraphDomain.acyclic unit14 occurrence14
    FixtureReaderTransfer.molecularFrameUnit14]
  exact label14

theorem mapLabel22 : (actualReferenceDescriptorMap input unit22).bind
    DeclarativeCIP.Descriptor.toLocalizedLabel = some (.chiral RS.S) := by
  rw [actualReferenceDescriptorMap_readback input FixtureGraphDomain.simpleBonded
    FixtureGraphDomain.acyclic unit22 occurrence22
    FixtureReaderTransfer.molecularFrameUnit22]
  exact label22

theorem mapLabel29 : (actualReferenceDescriptorMap input unit29).bind
    DeclarativeCIP.Descriptor.toLocalizedLabel = some (.chiral RS.S) := by
  rw [actualReferenceDescriptorMap_readback input FixtureGraphDomain.simpleBonded
    FixtureGraphDomain.acyclic unit29 occurrence29
    FixtureReaderTransfer.molecularFrameUnit29]
  exact label29

/-- **The actual generated descriptor map at the eight molecular units.** -/
theorem mapDescriptor4 : actualReferenceDescriptorMap input unit4 = some .R :=
  descriptor_eq_of_label mapLabel4
theorem mapDescriptor7 : actualReferenceDescriptorMap input unit7 = some .R :=
  descriptor_eq_of_label mapLabel7
theorem mapDescriptor11 : actualReferenceDescriptorMap input unit11 = some .S :=
  descriptor_eq_of_label mapLabel11
theorem mapDescriptor14 : actualReferenceDescriptorMap input unit14 = some .R :=
  descriptor_eq_of_label mapLabel14
theorem mapDescriptor19 : actualReferenceDescriptorMap input unit19 = some .S :=
  descriptor_eq_of_label mapLabel19
theorem mapDescriptor22 : actualReferenceDescriptorMap input unit22 = some .S :=
  descriptor_eq_of_label mapLabel22
theorem mapDescriptor26 : actualReferenceDescriptorMap input unit26 = some .R :=
  descriptor_eq_of_label mapLabel26
theorem mapDescriptor29 : actualReferenceDescriptorMap input unit29 = some .S :=
  descriptor_eq_of_label mapLabel29

end Reader

/-! ## The root setup and the root endpoint -/

theorem exists_rootFrame :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input)) (alpha : Equiv.Perm (Fin 4)),
      input.certified.localizedOccurrenceFourLigandFrame?
          (ActualReaderPhysicalBranchInverse.topTarget input rootP) = some frame ∧
        ∀ i, (frame.cursorAt i).occurrence.1.node.current? =
          some (Physical.ligandAtomAt rootP (alpha i)) :=
  input.certified.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation_detected
    FixtureGraphDomain.simpleBonded FixtureGraphDomain.acyclic
    (globalCarrierFuel_adequate input) (ActualReaderPhysicalBranchInverse.topTarget input rootP)
    (ActualReaderPhysicalBranchInverse.topTarget_current input rootP) rootP rfl

/-- The actual four-ligand frame of the root. -/
def rootFrame : input.certified.LocalizedOccurrenceFourLigandFrame
    (LocalizedUniversalReference.carrierFuel input) :=
  Classical.choose exists_rootFrame

theorem rootFrameComputed :
    input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input rootP) = some rootFrame :=
  (Classical.choose_spec (Classical.choose_spec exists_rootFrame)).1

/-- **The physical centre setup of the fixture's root.** -/
def setup : Rule4aTableBridge.ActualCentrePhysicalSetup input where
  c := rootP
  frame := rootFrame
  frameComputed := rootFrameComputed
  singleBonded := FixtureGraphDomain.simpleBonded
  acyclic := FixtureGraphDomain.acyclic
  hcharge := FixtureGraphDomain.constantFormalCharge
  noDouble := FixtureGraphDomain.noLocalizedDoubleBondRecords
  cfg := cfg
  physicalDomain := physicalDomain
  center := FixtureRootGeometry.rootCenter
  hcenter := rfl




theorem root_descriptor_of_distinct
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport Physical cfg rootP i j) :
    ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
      input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
          (ActualReaderPhysicalBranchInverse.topTarget input rootP) = some descriptor ∧
        (descriptor.IsLowercase ↔ physicalEnantiomorphicPairCount Physical cfg rootP = 1) :=
  setup.exists_orderedReferenceState_descriptor_lowercase_iff_physicalCount distinct
    FixtureRootGeometry.actualCanonicalRootCoordinates

/-- **The root endpoint at the fixture, with the geometric witness.**  Besides the descriptor
equation this keeps the R4 theorem's permutation and the oriented-volume reading of the ordered
points; the independent-order and Rule-5 seniority conjuncts of the R4 theorem are not retained
here (they are consumed by `LocalizedTwoReferenceFixtureRootLetter`). -/
theorem root_classification_of_distinct
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport Physical cfg rootP i j) :
    ∃ (tracked : TrackedLocalizedLigandOrder) (normalizedRS : RS)
      (pointsAt : Fin 4 → CartesianPoint3),
      input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
          (ActualReaderPhysicalBranchInverse.topTarget input rootP) =
        some (classifyTetrahedralRSPseudo normalizedRS
          (physicalEnantiomorphicPairCount Physical cfg rootP)) ∧
      (∀ index : Fin 4,
        input.certified.localizedRerootCursorSpatialPoint? (rootFrame.cursorAt index) =
          some (pointsAt index)) ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      RationalTetrahedralDescriptor (tracked.highestFirst.map pointsAt) normalizedRS ∧
      ((classifyTetrahedralRSPseudo normalizedRS
          (physicalEnantiomorphicPairCount Physical cfg rootP)).IsLowercase ↔
        physicalEnantiomorphicPairCount Physical cfg rootP = 1) :=
  let ⟨tracked, normalizedRS, pointsAt, stateEq, spatial, perm, rational, lowercase, _, _, _⟩ :=
    setup.orderedReferenceState_top_eq_classify_physical_rule5 distinct
      FixtureRootGeometry.actualCanonicalRootCoordinates
  ⟨tracked, normalizedRS, pointsAt, stateEq, spatial, perm, rational, lowercase⟩

end

end LocalizedTwoReferenceFixturePhysicalInstance
end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance.physicalDomain
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance.referenceState_of_canonicalData
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance.label4
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance.label7
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance.label11
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance.label14
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance.label19
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance.label22
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance.label26
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance.label29
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance.mapDescriptor4
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance.mapDescriptor29
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance.setup
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance.root_descriptor_of_distinct
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance.root_classification_of_distinct
