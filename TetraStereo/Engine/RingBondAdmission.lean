import TetraStereo.Engine.RingSpatialTransport
import TetraStereo.Engine.RingBondRecordOrder
import TetraStereo.OneCenter.LocalizedRawAdmissionCompleteness

/-! Bond-record order preserves both localized reference and public structural
admission. The public proof transports the simple-bond and uniform-charge gates
explicitly; it does not assume that hydrogen completion always passes them. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingBondAdmission
open OneCenter

/-- Semantic readiness is insensitive to interaction order, including uniqueness. -/
theorem ready_perm {a b : SemanticMolecule} (atoms : a.atoms = b.atoms)
    (interactions : a.interactions.Perm b.interactions) :
    a.LocalizedCIPGraphReady ↔ b.LocalizedCIPGraphReady := by
  have count : a.atomCount = b.atomCount := congrArg List.length atoms
  have structural : a.StructurallyWellFormed ↔ b.StructurallyWellFormed := by
    simp only [SemanticMolecule.StructurallyWellFormed,List.all_eq_true]
    constructor
    · intro h x hx
      rw [← count]
      exact h x (interactions.mem_iff.mpr hx)
    · intro h x hx
      rw [count]
      exact h x (interactions.mem_iff.mp hx)
  have localized : a.LocalizedCovalentPairsOnly ↔ b.LocalizedCovalentPairsOnly := by
    simp only [SemanticMolecule.LocalizedCovalentPairsOnly]
    constructor
    · intro h x hx; exact h x (interactions.mem_iff.mpr hx)
    · intro h x hx; exact h x (interactions.mem_iff.mp hx)
  have unique : a.LocalizedCovalentRecordsUnique ↔ b.LocalizedCovalentRecordsUnique :=
    ((interactions.filterMap SemanticInteraction.localizedCovalentRecord?).map Prod.fst).nodup_iff
  simp only [SemanticMolecule.LocalizedCIPGraphReady,structural,localized,unique,
    SemanticMolecule.ExplicitLocalizedClosedShellAtoms,SemanticMolecule.AllRule2MassesKnown,atoms]

/-- Raw conversion preserves atom equality and sends a bond permutation to an
interaction permutation. No equality of ordered semantic interaction lists is asserted. -/
theorem conversion_perm {m n : RawMolecule} (atoms : m.atoms = n.atoms)
    (bonds : m.bonds.Perm n.bonds) {a : SemanticMolecule}
    (converted : m.toSemanticMolecule? = some a) :
    ∃ b, n.toSemanticMolecule? = some b ∧ a.atoms = b.atoms ∧
      a.interactions.Perm b.interactions := by
  cases observed : m.semanticAtoms? with
  | none => simp [RawMolecule.toSemanticMolecule?,observed] at converted
  | some sa =>
    have other : n.semanticAtoms? = some sa := by simpa only [RawMolecule.semanticAtoms?,← atoms] using observed
    simp [RawMolecule.toSemanticMolecule?,observed] at converted
    subst a
    exact ⟨⟨sa,n.bonds.map RawBond.toSemanticInteraction⟩,
      by simp [RawMolecule.toSemanticMolecule?,other],rfl,
      bonds.map RawBond.toSemanticInteraction⟩

/-- Full equivalence of localized reference admission, including all diagram
wellformedness checks through constructive admission completeness. -/
theorem localized_admission {m n : RawMolecule} (atoms : m.atoms = n.atoms)
    (bonds : m.bonds.Perm n.bonds) (g : SpatialConfiguration) :
    (LocalizedReference.admitRawSpatial? m g).isSome = true ↔
      (LocalizedReference.admitRawSpatial? n g).isSome = true := by
  rw [LocalizedRawAdmission.admitRawSpatial?_isSome_iff,
    LocalizedRawAdmission.admitRawSpatial?_isSome_iff]
  constructor
  · rintro ⟨a,converted,ready,full⟩
    obtain ⟨b,converted',same,permuted⟩ := conversion_perm atoms bonds converted
    exact ⟨b,converted',(ready_perm same permuted).mp ready,
      full.trans (congrArg List.length same)⟩
  · rintro ⟨b,converted,ready,full⟩
    obtain ⟨a,converted',same,permuted⟩ := conversion_perm atoms.symm bonds.symm converted
    exact ⟨a,converted',(ready_perm same permuted).mp ready,
      full.trans (congrArg List.length same)⟩

/-- A public admitted presentation transports to a stereochemically admissible
bond-table permutation, retaining the same geometry and atom records. -/
theorem public_forward (i : LocalizedChemicalRing.Input) (n : RawMolecule)
    (atoms : i.molecule.atoms = n.atoms) (bonds : i.molecule.bonds.Perm n.bonds)
    (admissible : n.StereochemicalAdmissible) :
    ∃ j, LocalizedChemicalRing.admitRawSpatial? n i.spatial = some j := by
  obtain ⟨b,converted,same,permuted⟩ := conversion_perm atoms bonds i.agreement.1
  have ready := (ready_perm same permuted).mp i.certified.graphReady
  have full : i.spatial.positions.length = b.atomCount :=
    (RingSpatialTransport.full_original i).trans (congrArg List.length same)
  obtain ⟨k,accepted,semantic,agreement,spatial⟩ :=
    LocalizedRawAdmission.admitRawSpatial?_complete n b i.spatial converted ready full
  have supported : ∀ bond ∈ n.bonds, bond.kind.IsLocalizedCovalent := by
    intro bond member
    exact i.supported bond (bonds.mem_iff.mpr member)
  have atomLists : k.certified.certified.input.molecule.atoms =
      i.certified.certified.input.molecule.atoms := by rw [semantic]; exact same.symm
  have count : i.certified.certified.input.molecule.atomCount =
      k.certified.certified.input.molecule.atomCount := (congrArg List.length atomLists).symm
  let e : i.certified.Atom ≃ k.certified.Atom := finCongr count
  have edge (a c : i.certified.Atom) :
      k.certified.moleculeGraph.bond (e a) (e c) = i.certified.moleculeGraph.bond a c := by
    rw [moleculeGraph_bond_eq_rawBondOrder
      n k.certified agreement admissible.1.1 admissible.1.2 supported,
      moleculeGraph_bond_eq_rawBondOrder
      i.molecule i.certified i.agreement i.admissible.1.1 i.admissible.1.2 i.supported]
    exact (RingBondRecordOrder.bondOrder bonds a.val c.val).symm
  have single : k.certified.moleculeGraph.SimpleBonded := by
    intro a c adj
    obtain ⟨u,rfl⟩ := e.surjective a
    obtain ⟨v,rfl⟩ := e.surjective c
    change 0 < k.certified.moleculeGraph.bond (e u) (e v) at adj
    rw [edge] at adj ⊢
    exact i.single u v adj
  have charges (a : i.certified.Atom) :
      k.certified.moleculeGraph.formalCharge (e a) = i.certified.moleculeGraph.formalCharge a := by
    change (k.certified.certified.input.molecule.atoms.get (e a)).formalCharge =
      (i.certified.certified.input.molecule.atoms.get a).formalCharge
    simp only [List.get_eq_getElem]
    simp only [atomLists]
    rfl
  have charge : ∃ z, ∀ a : k.certified.Atom, k.certified.moleculeGraph.formalCharge a = z := by
    obtain ⟨z,hz⟩ := i.charge
    refine ⟨z,?_⟩
    intro a
    obtain ⟨u,rfl⟩ := e.surjective a
    exact (charges u).trans (hz u)
  let j : LocalizedChemicalRing.Input :=
    ⟨k.certified,n,i.spatial,agreement,spatial,admissible,supported,single,charge⟩
  exact ⟨j,RingSpatialTransport.readmit j⟩

/-- Structural public admission is equivalent across arbitrary bond permutations
when both written-neighbor presentations satisfy stereochemical admission. -/
theorem public_admission {m n : RawMolecule} (atoms : m.atoms = n.atoms)
    (bonds : m.bonds.Perm n.bonds) (first : m.StereochemicalAdmissible)
    (second : n.StereochemicalAdmissible) (g : SpatialConfiguration) :
    (LocalizedChemicalRing.admitRawSpatial? m g).isSome = true ↔
      (LocalizedChemicalRing.admitRawSpatial? n g).isSome = true := by
  constructor
  · intro success
    obtain ⟨i,admitted⟩ := Option.isSome_iff_exists.mp success
    obtain ⟨raw,spatial⟩ := RingChemicalReport.admission_fields admitted
    obtain ⟨j,accepted⟩ := public_forward i n (raw ▸ atoms) (raw ▸ bonds) second
    rw [spatial] at accepted
    exact Option.isSome_iff_exists.mpr ⟨j,accepted⟩
  · intro success
    obtain ⟨j,admitted⟩ := Option.isSome_iff_exists.mp success
    obtain ⟨raw,spatial⟩ := RingChemicalReport.admission_fields admitted
    obtain ⟨i,accepted⟩ := public_forward j m (raw ▸ atoms.symm) (raw ▸ bonds.symm) first
    rw [spatial] at accepted
    exact Option.isSome_iff_exists.mpr ⟨i,accepted⟩

end TetraStereo.Engine.RingBondAdmission
assert_kernel_only TetraStereo.Engine.RingBondAdmission.ready_perm
assert_kernel_only TetraStereo.Engine.RingBondAdmission.conversion_perm
assert_kernel_only TetraStereo.Engine.RingBondAdmission.localized_admission

assert_kernel_only TetraStereo.Engine.RingBondAdmission.public_forward
assert_kernel_only TetraStereo.Engine.RingBondAdmission.public_admission
