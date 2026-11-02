import TetraStereo.OneCenter.LocalizedAcyclicRerootNeighborCorrespondence
import TetraStereo.OneCenter.LocalizedOccurrenceRule45Descriptor
import TetraStereo.OneCenter.MultiCenter
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.Card
import TetraStereo.KernelOnly

set_option autoImplicit false
















































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput)

/-! ## Current atoms of actual carrier cursors -/

/-- Every actual carrier cursor carries a definite current physical atom. -/
theorem localizedRerootCursor_current_exists
    {carrierFuel : Nat} (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∃ w, cursor.occurrence.1.node.current? = some w :=
  Option.isSome_iff_exists.mp
    (input.declarativeLocalizedOccurrence_node_current_isSome
      ((input.mem_localizedOccurrences_iff carrierFuel cursor.occurrence.1).mp
        cursor.occurrence.2))

/-! ## The actual root expansion is a physical neighbor bijection -/









theorem exists_localizedRerootChildren_neighborEquiv
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    {oAtom : input.Atom}
    (oObserved : target.1.node.current? = some oAtom)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren?
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) = some children) :
    ∃ ligand : {child // child ∈ children} ≃ input.moleculeGraph.Neighbor oAtom,
      ∀ child, child.1.occurrence.1.node.current? = some (ligand child).1 := by
  classical
  let rootCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := none }
  have correspondence := input.localizedRerootChildren?_current_iff_adjacent_root
    singleBonded acyclic enough rootCursor rfl oObserved children computed
  have injective := input.localizedRerootChildren?_current_injective
    singleBonded acyclic rootCursor children computed
  let atomOf : {child // child ∈ children} → input.Atom :=
    fun child => Classical.choose (input.localizedRerootCursor_current_exists child.1)
  have atomOf_spec : ∀ child : {child // child ∈ children},
      child.1.occurrence.1.node.current? = some (atomOf child) :=
    fun child => Classical.choose_spec (input.localizedRerootCursor_current_exists child.1)
  have adjOf : ∀ child : {child // child ∈ children},
      input.moleculeGraph.Adj oAtom (atomOf child) :=
    fun child =>
      (correspondence (atomOf child)).mp ⟨child.1, child.2, atomOf_spec child⟩
  let toNeighbor : {child // child ∈ children} → input.moleculeGraph.Neighbor oAtom :=
    fun child => ⟨atomOf child, adjOf child⟩
  have toNeighbor_injective : Function.Injective toNeighbor := by
    intro left right equal
    have sameAtom : atomOf left = atomOf right := congrArg Subtype.val equal
    have sameCurrent : left.1.occurrence.1.node.current? =
        right.1.occurrence.1.node.current? := by
      rw [atomOf_spec left, atomOf_spec right, sameAtom]
    exact Subtype.ext (injective left.1 left.2 right.1 right.2 sameCurrent)
  have toNeighbor_surjective : Function.Surjective toNeighbor := by
    intro neighbor
    obtain ⟨child, present, current⟩ :=
      (correspondence neighbor.1).mpr neighbor.2
    refine ⟨⟨child, present⟩, ?_⟩
    apply Subtype.ext
    exact Option.some.inj ((atomOf_spec ⟨child, present⟩).symm.trans current)
  exact ⟨Equiv.ofBijective toNeighbor ⟨toNeighbor_injective, toNeighbor_surjective⟩,
    fun child => atomOf_spec child⟩

/-- **Child count equals physical degree.**  The actual root expansion of a carrier occurrence has
exactly as many children as its current physical atom has neighbors.  This is the genuine
cardinality statement behind the four-ligand frame; it is proved from the explicit bijection, not
assumed. -/
theorem localizedRerootChildren_length_eq_neighbor_card
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    {oAtom : input.Atom}
    (oObserved : target.1.node.current? = some oAtom)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren?
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) = some children) :
    children.length = Fintype.card (input.moleculeGraph.Neighbor oAtom) := by
  classical
  obtain ⟨ligand, _ligandSpec⟩ := input.exists_localizedRerootChildren_neighborEquiv
    singleBonded acyclic enough target oObserved children computed
  have sound := input.localizedRerootChildren?_sound
    ({ occurrence := target, previous? := none } :
      input.LocalizedRerootCursor carrierFuel) children computed
  have nodup := input.localizedRerootChildren_nodup
    ({ occurrence := target, previous? := none } :
      input.LocalizedRerootCursor carrierFuel) children sound
  have card := Fintype.card_congr ((List.Nodup.getEquiv children nodup).trans ligand)
  simpa using card

/-! ## The actual four-ligand frame at a tetrahedral current atom -/

/-- **Actual four-ligand frame completeness.**  Let `input` be a certified localized CIP input
that is single-bonded and acyclic, let `target` be an actual occurrence at any carrier fuel at
least the atom count, and suppose the target's current physical atom `oAtom` has exactly four
neighbors.  Then the **actual** executable constructor succeeds:

`input.localizedOccurrenceFourLigandFrame? target = some frame`,

and moreover the four frame slots are carried by an explicit physical bijection
`Fin 4 ≃ input.moleculeGraph.Neighbor oAtom` that reads each cursor's own `current?` atom.

Neither a successful frame, a declarative frame, a desired label, a child-list equality, a
neighbor bisection nor a slot permutation is assumed. -/
theorem exists_localizedOccurrenceFourLigandFrame_and_neighborEquiv
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    {oAtom : input.Atom}
    (oObserved : target.1.node.current? = some oAtom)
    (tetrahedral : input.moleculeGraph.IsTetrahedralCenter oAtom) :
    ∃ (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
      (ligand : Fin 4 ≃ input.moleculeGraph.Neighbor oAtom),
      input.localizedOccurrenceFourLigandFrame? target = some frame ∧
        (∀ i, (frame.cursorAt i).occurrence.1.node.current? = some (ligand i).1) := by
  classical
  let rootCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := none }
  obtain ⟨children, computed⟩ := input.exists_localizedRerootChildren rootCursor
  have sound := input.localizedRerootChildren?_sound rootCursor children computed
  have nodup := input.localizedRerootChildren_nodup rootCursor children sound
  have lengthEq : children.length = 4 := by
    have degree := input.localizedRerootChildren_length_eq_neighbor_card
      singleBonded acyclic enough target oObserved children computed
    rw [degree]
    exact tetrahedral
  let frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel :=
    { cursors := children, length_eq := lengthEq }
  have frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame := by
    rw [input.localizedOccurrenceFourLigandFrame?_eq_some_iff]
    show input.DeclarativeLocalizedRerootChildren
        ({ occurrence := target, previous? := none } :
          input.LocalizedRerootCursor carrierFuel) frame.cursors ∧
      frame.cursors.length = 4
    exact ⟨sound, lengthEq⟩
  obtain ⟨ligandSub, ligandSub_spec⟩ :=
    input.exists_localizedRerootChildren_neighborEquiv singleBonded acyclic enough
      target oObserved children computed
  let indexEquiv : Fin 4 ≃ {child // child ∈ children} :=
    (finCongr lengthEq.symm).trans (List.Nodup.getEquiv children nodup)
  let ligand : Fin 4 ≃ input.moleculeGraph.Neighbor oAtom := indexEquiv.trans ligandSub
  have ligand_spec : ∀ i : Fin 4,
      (frame.cursorAt i).occurrence.1.node.current? = some (ligand i).1 := by
    intro i
    exact ligandSub_spec (indexEquiv i)
  exact ⟨frame, ligand, frameComputed, ligand_spec⟩

/-- **Actual frame existence.**  Structural form of
`exists_localizedOccurrenceFourLigandFrame_and_neighborEquiv`: a tetrahedral current atom of an
actual occurrence forces the executable four-ligand frame constructor to succeed. -/
theorem exists_localizedOccurrenceFourLigandFrame_of_tetrahedral
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    {oAtom : input.Atom}
    (oObserved : target.1.node.current? = some oAtom)
    (tetrahedral : input.moleculeGraph.IsTetrahedralCenter oAtom) :
    ∃ frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel,
      input.localizedOccurrenceFourLigandFrame? target = some frame := by
  obtain ⟨frame, _ligand, computed, _ligandSpec⟩ :=
    input.exists_localizedOccurrenceFourLigandFrame_and_neighborEquiv
      singleBonded acyclic enough target oObserved tetrahedral
  exact ⟨frame, computed⟩

/-- **Converse: an actual frame forces a tetrahedral current atom.**  Every successful actual
four-ligand frame at an actual occurrence has exactly four physical ligand atoms, so the current
atom has four neighbors. -/
theorem isTetrahedralCenter_of_localizedOccurrenceFourLigandFrame
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    {oAtom : input.Atom}
    (oObserved : target.1.node.current? = some oAtom)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    input.moleculeGraph.IsTetrahedralCenter oAtom := by
  have sound :=
    ((input.localizedOccurrenceFourLigandFrame?_eq_some_iff target frame).mp computed).1
  have childrenComputed : input.localizedRerootChildren?
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) = some frame.cursors :=
    (input.localizedRerootChildren?_eq_some_iff _ frame.cursors).mpr sound
  have degree := input.localizedRerootChildren_length_eq_neighbor_card
    singleBonded acyclic enough target oObserved frame.cursors childrenComputed
  show Fintype.card (input.moleculeGraph.Neighbor oAtom) = 4
  rw [← degree]
  exact frame.length_eq

/-- **Exact characterization.**  On a finite acyclic single-bond certified input at any sufficient
carrier fuel, an actual occurrence admits an actual four-ligand frame exactly when its current
physical atom is tetrahedral.  This is the formal statement that the frame is discovered, not
assumed. -/
theorem localizedOccurrenceFourLigandFrame?_isSome_iff_isTetrahedralCenter
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    {oAtom : input.Atom}
    (oObserved : target.1.node.current? = some oAtom) :
    (input.localizedOccurrenceFourLigandFrame? target).isSome = true ↔
      input.moleculeGraph.IsTetrahedralCenter oAtom := by
  constructor
  · intro someTrue
    obtain ⟨frame, computed⟩ := Option.isSome_iff_exists.mp someTrue
    exact input.isTetrahedralCenter_of_localizedOccurrenceFourLigandFrame
      singleBonded acyclic enough target oObserved frame computed
  · intro tetrahedral
    obtain ⟨frame, computed⟩ := input.exists_localizedOccurrenceFourLigandFrame_of_tetrahedral
      singleBonded acyclic enough target oObserved tetrahedral
    simp [computed]

/-- **Physical bijection of any actually computed frame.**  Given an actual successful frame at an
actual occurrence, its four slots are explicitly bijective with the physical neighbors of the
current atom, and the bijection reads the cursor's `current?` atom.  The tetrahedral hypothesis is
derived from the frame itself. -/
theorem exists_localizedOccurrenceFourLigandFrame_neighborEquiv
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    {oAtom : input.Atom}
    (oObserved : target.1.node.current? = some oAtom)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    ∃ ligand : Fin 4 ≃ input.moleculeGraph.Neighbor oAtom,
      ∀ i, (frame.cursorAt i).occurrence.1.node.current? = some (ligand i).1 := by
  obtain ⟨builtFrame, ligand, builtComputed, ligandSpec⟩ :=
    input.exists_localizedOccurrenceFourLigandFrame_and_neighborEquiv
      singleBonded acyclic enough target oObserved
      (input.isTetrahedralCenter_of_localizedOccurrenceFourLigandFrame
        singleBonded acyclic enough target oObserved frame computed)
  have frameEq : frame = builtFrame := Option.some.inj (computed.symm.trans builtComputed)
  subst frameEq
  exact ⟨ligand, ligandSpec⟩

/-! ## The canonical molecular ligand-slot permutation -/

/-- The physical ligand atom map of a distinguished center of an actual `MultiCenterMolecule`,
transported along the identification of its molecular graph with the certified input's graph. -/
noncomputable def physicalLigandAtom
    (m : MultiCenterMolecule input.Atom)
    (graphEq : m.mol = input.moleculeGraph)
    (center : m.Center) (i : Fin 4) :
    input.moleculeGraph.Neighbor center.1 :=
  ⟨m.ligandAtomAt center i, by
    have adjacent := m.ligandAtomAt_adj center i
    rw [graphEq] at adjacent
    exact adjacent⟩

/-- The transported physical ligand atom is the molecule's chosen ligand atom. -/
@[simp] theorem physicalLigandAtom_apply_coe
    (m : MultiCenterMolecule input.Atom)
    (graphEq : m.mol = input.moleculeGraph)
    (center : m.Center) (i : Fin 4) :
    (input.physicalLigandAtom m graphEq center i).1 = m.ligandAtomAt center i := rfl

/-- The actual physical ligand enumeration of a distinguished center, as an equivalence with the
neighbors of that center in the certified input's graph.  This is the physical half of the frame
link; it uses only the molecule's own adjacency, injectivity and surjectivity data. -/
noncomputable def physicalLigandEquiv
    (m : MultiCenterMolecule input.Atom)
    (graphEq : m.mol = input.moleculeGraph)
    (center : m.Center) :
    Fin 4 ≃ input.moleculeGraph.Neighbor center.1 where
  toFun i := input.physicalLigandAtom m graphEq center i
  invFun neighbor :=
    Classical.choose (m.ligandAtomAt_surjective center neighbor.1 (by
      rw [graphEq]
      exact neighbor.2))
  left_inv i :=
    m.ligandAtomAt_injective center
      (Classical.choose_spec
        (m.ligandAtomAt_surjective center (m.ligandAtomAt center i)
          (m.ligandAtomAt_adj center i)))
  right_inv neighbor :=
    Subtype.ext
      (Classical.choose_spec
        (m.ligandAtomAt_surjective center neighbor.1 (by
          rw [graphEq]
          exact neighbor.2)))

/-- The physical ligand equivalence reads the molecule's chosen ligand atom. -/
@[simp] theorem physicalLigandEquiv_apply_coe
    (m : MultiCenterMolecule input.Atom)
    (graphEq : m.mol = input.moleculeGraph)
    (center : m.Center) (i : Fin 4) :
    (input.physicalLigandEquiv m graphEq center i).1 = m.ligandAtomAt center i := rfl

/-- An actual physical center of the molecule makes its atom a tetrahedral center of the certified
input's graph.  The degree-four hypothesis is therefore not an extra assumption when the molecule
supplies the distinguished center. -/
theorem isTetrahedralCenter_of_physicalLigandEquiv
    (m : MultiCenterMolecule input.Atom)
    (graphEq : m.mol = input.moleculeGraph)
    (center : m.Center) :
    input.moleculeGraph.IsTetrahedralCenter center.1 := by
  have card := Fintype.card_congr (input.physicalLigandEquiv m graphEq center)
  show Fintype.card (input.moleculeGraph.Neighbor center.1) = 4
  rw [← card]
  simp











theorem exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    {oAtom : input.Atom}
    (oObserved : target.1.node.current? = some oAtom)
    (m : MultiCenterMolecule input.Atom)
    (graphEq : m.mol = input.moleculeGraph)
    (center : m.Center)
    (centerEq : center.1 = oAtom) :
    ∃ (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
      (alpha : Equiv.Perm (Fin 4)),
      input.localizedOccurrenceFourLigandFrame? target = some frame ∧
        ∀ i, (frame.cursorAt i).occurrence.1.node.current? =
          some (m.ligandAtomAt center (alpha i)) := by
  classical
  have oObserved' : target.1.node.current? = some center.1 := by
    simpa [← centerEq] using oObserved
  obtain ⟨frame, ligand, frameComputed, ligandSpec⟩ :=
    input.exists_localizedOccurrenceFourLigandFrame_and_neighborEquiv
      singleBonded acyclic enough target oObserved'
      (input.isTetrahedralCenter_of_physicalLigandEquiv m graphEq center)
  let alpha : Equiv.Perm (Fin 4) :=
    ligand.trans (input.physicalLigandEquiv m graphEq center).symm
  refine ⟨frame, alpha, frameComputed, fun i => ?_⟩
  have key : input.physicalLigandEquiv m graphEq center (alpha i) = ligand i := by
    simp [alpha]
  calc (frame.cursorAt i).occurrence.1.node.current?
      = some (ligand i).1 := ligandSpec i
    _ = some (input.physicalLigandEquiv m graphEq center (alpha i)).1 := by rw [← key]
    _ = some (m.ligandAtomAt center (alpha i)) := by
          rw [input.physicalLigandEquiv_apply_coe]

/-- **Detected-center frame existence.**  If the distinguished center is an automatically detected
tetrahedral center of the certified input's graph and its atom is the target's current atom, then
the actual frame exists.  Here the tetrahedral property comes from graph detection rather than
from a supplied `MultiCenterMolecule` enumeration. -/
theorem exists_localizedOccurrenceFourLigandFrame_of_detectedCenter
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    {oAtom : input.Atom}
    (oObserved : target.1.node.current? = some oAtom)
    (center : input.detectedMultiCenterMolecule.Center)
    (centerEq : center.1 = oAtom) :
    ∃ frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel,
      input.localizedOccurrenceFourLigandFrame? target = some frame := by
  have oObserved' : target.1.node.current? = some center.1 := by
    simpa [← centerEq] using oObserved
  have tetrahedral : input.moleculeGraph.IsTetrahedralCenter center.1 :=
    (input.moleculeGraph.mem_tetrahedralCenterSet center.1).mp center.2
  exact input.exists_localizedOccurrenceFourLigandFrame_of_tetrahedral
    singleBonded acyclic enough target oObserved' tetrahedral

/-- **Detected-center physical frame link.**  The detected-center specialization of
`exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation`, using the automatically
constructed multi-center molecule of the certified input. -/
theorem exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation_detected
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    {oAtom : input.Atom}
    (oObserved : target.1.node.current? = some oAtom)
    (center : input.detectedMultiCenterMolecule.Center)
    (centerEq : center.1 = oAtom) :
    ∃ (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
      (alpha : Equiv.Perm (Fin 4)),
      input.localizedOccurrenceFourLigandFrame? target = some frame ∧
        ∀ i, (frame.cursorAt i).occurrence.1.node.current? =
          some (input.detectedMultiCenterMolecule.ligandAtomAt center (alpha i)) :=
  input.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation
    singleBonded acyclic enough target oObserved
    input.detectedMultiCenterMolecule rfl center centerEq

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCursor_current_exists
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_localizedRerootChildren_neighborEquiv
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildren_length_eq_neighbor_card
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_localizedOccurrenceFourLigandFrame_and_neighborEquiv
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_localizedOccurrenceFourLigandFrame_of_tetrahedral
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.isTetrahedralCenter_of_localizedOccurrenceFourLigandFrame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame?_isSome_iff_isTetrahedralCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_localizedOccurrenceFourLigandFrame_neighborEquiv
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.physicalLigandAtom
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.physicalLigandAtom_apply_coe
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.physicalLigandEquiv
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.physicalLigandEquiv_apply_coe
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.isTetrahedralCenter_of_physicalLigandEquiv
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_localizedOccurrenceFourLigandFrame_of_detectedCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation_detected
