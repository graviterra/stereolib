import TetraStereo.OneCenter.LocalizedPhysicalCompoundForwardTransport
import TetraStereo.OneCenter.LocalizedPhysicalNearestRule4bReference
import TetraStereo.OneCenter.LocalizedActualKeyTiePhysicalTransport
import TetraStereo.OneCenter.LocalizedActualPhysicalReferenceSelection
import TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalLabelCovariance

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false





























namespace TetraStereo
namespace OneCenter

open CertifiedLocalizedCIPInput
open RootedTetrahedralBranchSymmetry
open LocalizedCumulativeDecoratedTree

namespace LocalizedPhysicalReferenceCovariance

/-! ## Graph-level equivariance of the branch -/

/-- The underlying-simple-graph homomorphism induced by a multi-center automorphism. -/
def graphHomOfAut {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (e : m.Aut) :
    m.mol.underlyingSimpleGraph →g m.mol.underlyingSimpleGraph where
  toFun := (e : Equiv.Perm V)
  map_rel' := by
    intro a b hab
    exact (MoleculeGraph.Aut.adj_iff m.mol
      (⟨(e : Equiv.Perm V),
        MultiCenterMolecule.Aut.mem_molAut (m := m) e⟩ : m.mol.Aut) a b).2 hab

@[simp] theorem graphHomOfAut_apply {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (e : m.Aut) (a : V) :
    graphHomOfAut m e a = (e : Equiv.Perm V) a := rfl

/-- Copying a walk along equal endpoints preserves pathhood. -/
theorem walk_isPath_copy {V : Type*} {G : SimpleGraph V} {u v u' v' : V}
    {walk : G.Walk u v} (path : walk.IsPath) (startEq : u = u') (endEq : v = v') :
    (walk.copy startEq endEq).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_copy]
  exact (SimpleGraph.Walk.isPath_def walk).mp path

/-- A root-fixing automorphism carrying ligand index `i` to `j` maps the ligand branch at `i`
exactly onto the ligand branch at `j`. -/
theorem ligandBranchReaches_map_iff {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) {c : m.Center} {i j : Fin 4}
    {e : m.Aut} (hc : m.centerPerm e c = c) (hi : m.ligandPermAt e c i = j)
    {v : V} :
    LigandBranchReaches m c i v ↔ LigandBranchReaches m c j ((e : Equiv.Perm V) v) := by
  constructor
  · intro h
    exact ligandBranchReaches_map (m := m) hc hi h
  · intro h
    have hc' : m.centerPerm (e⁻¹ : m.Aut) c = c :=
      centerPerm_inv_eq m e c hc
    have hi' : m.ligandPermAt (e⁻¹ : m.Aut) c j = i :=
      ligandPermAt_inv_apply m e c i j hc hi
    have back := ligandBranchReaches_map (m := m) hc' hi' h
    simpa using back

/-- Membership in the certified-input cut branch is transported by a root-fixing automorphism. -/
theorem cutBranch_mem_transport {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) {mol : MoleculeGraph V} (graphEq : m.mol = mol)
    {c : m.Center} {i j : Fin 4} {e : m.Aut}
    (hc : m.centerPerm e c = c) (hi : m.ligandPermAt e c i = j) {v : V} :
    v ∈ AcyclicCutBranchAutomorphism.CutBranch mol c.1 (m.ligandAtomAt c i) ↔
      ((e : Equiv.Perm V) v) ∈
        AcyclicCutBranchAutomorphism.CutBranch mol c.1 (m.ligandAtomAt c j) := by
  rw [← graphEq]
  rw [show v ∈ AcyclicCutBranchAutomorphism.CutBranch m.mol c.1 (m.ligandAtomAt c i) ↔
      LigandBranchReaches m c i v from
    AcyclicCutBranchAutomorphism.ligandBranchReaches_iff_cutBranchReaches m c i v]
  rw [show ((e : Equiv.Perm V) v) ∈
      AcyclicCutBranchAutomorphism.CutBranch m.mol c.1 (m.ligandAtomAt c j) ↔
      LigandBranchReaches m c j ((e : Equiv.Perm V) v) from
    AcyclicCutBranchAutomorphism.ligandBranchReaches_iff_cutBranchReaches m c j
      ((e : Equiv.Perm V) v)]
  exact ligandBranchReaches_map_iff m hc hi

/-- A root-fixing automorphism maps the physical simple sphere at the attachment of branch `i`
onto the corresponding sphere of branch `j` at the same distance. -/
theorem physicalSimpleSphere_transport
    {input : CertifiedLocalizedCIPInput}
    (m : MultiCenterMolecule input.Atom) {c : m.Center} {i j : Fin 4} {e : m.Aut}
    (hc : m.centerPerm e c = c) (hi : m.ligandPermAt e c i = j)
    (distance : Nat) (a : input.Atom) :
    a ∈ PhysicalSimpleSphere m.mol.underlyingSimpleGraph (m.ligandAtomAt c i) distance ↔
      ((e : Equiv.Perm input.Atom) a) ∈ PhysicalSimpleSphere m.mol.underlyingSimpleGraph
        (m.ligandAtomAt c j) distance := by
  constructor
  · rintro ⟨walk, path, length⟩
    have hstart : graphHomOfAut m e (m.ligandAtomAt c i) = m.ligandAtomAt c j := by
      have h := m.ligandAtomAt_ligandPermAt (e := e) (c := c) (i := i)
      rw [hc, hi] at h
      exact h.symm
    have mapped : (walk.map (graphHomOfAut m e)).IsPath :=
      SimpleGraph.Walk.map_isPath_of_injective
        (f := graphHomOfAut m e) (e : Equiv.Perm input.Atom).injective path
    refine ⟨(walk.map (graphHomOfAut m e)).copy hstart rfl, ?_, ?_⟩
    · exact walk_isPath_copy mapped hstart rfl
    · rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]
      exact length
  · rintro ⟨walk, path, length⟩
    have hc' : m.centerPerm (e⁻¹ : m.Aut) c = c :=
      centerPerm_inv_eq m e c hc
    have hi' : m.ligandPermAt (e⁻¹ : m.Aut) c j = i :=
      ligandPermAt_inv_apply m e c i j hc hi
    have hstart : graphHomOfAut m (e⁻¹ : m.Aut) (m.ligandAtomAt c j) =
        m.ligandAtomAt c i := by
      have h := m.ligandAtomAt_ligandPermAt (e := (e⁻¹ : m.Aut)) (c := c) (i := j)
      rw [hc', hi'] at h
      exact h.symm
    have hend : graphHomOfAut m (e⁻¹ : m.Aut) ((e : Equiv.Perm input.Atom) a) = a := by
      simp
    have mapped : (walk.map (graphHomOfAut m (e⁻¹ : m.Aut))).IsPath :=
      SimpleGraph.Walk.map_isPath_of_injective
        (f := graphHomOfAut m (e⁻¹ : m.Aut))
        (((e⁻¹ : m.Aut) : Equiv.Perm input.Atom)).injective path
    refine ⟨(walk.map (graphHomOfAut m (e⁻¹ : m.Aut))).copy hstart hend, ?_, ?_⟩
    · exact walk_isPath_copy mapped hstart hend
    · rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]
      exact length

/-! ## Reflected marks and the actual reference state -/

/-- The mirror action on an upper-case descriptor: the `R/S` swap in the mirror case and the
identity otherwise. -/
def mirrorReference (mirror : Bool) (descriptor : RS) : RS :=
  if mirror then RS.swap descriptor else descriptor

@[simp] theorem mirrorReference_true (descriptor : RS) :
    mirrorReference true descriptor = RS.swap descriptor := rfl

@[simp] theorem mirrorReference_false (descriptor : RS) :
    mirrorReference false descriptor = descriptor := rfl

/-- Reading an upper-case descriptor through the mirror reflection.  The reflected label carries
`descriptor` exactly when the original label carried the unique preimage of `descriptor`. -/
theorem reflectUppercaseOptionalLabel_chiral_iff (mirror : Bool)
    (label : Option LocalizedAuxiliaryLabel) (descriptor : RS) :
    (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id) label =
        some (.chiral descriptor) ↔
      ∃ other : RS, label = some (.chiral other) ∧
        mirrorReference mirror other = descriptor := by
  cases mirror with
  | false =>
      constructor
      · intro h
        exact ⟨descriptor, h, rfl⟩
      · rintro ⟨other, h, rfl⟩
        exact h
  | true =>
      constructor
      · intro h
        unfold CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel at h
        cases label with
        | none => simp at h
        | some label =>
            cases label with
            | chiral other =>
                refine ⟨other, rfl, ?_⟩
                have injected : some (RS.swap other) = some descriptor := by
                  simpa [CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel,
                    CertifiedLocalizedCIPInput.reflectUppercaseAuxiliaryLabel] using h
                exact Option.some.inj injected
            | pseudoasymmetric other =>
                simp [CertifiedLocalizedCIPInput.reflectUppercaseAuxiliaryLabel] at h
      · rintro ⟨other, rfl, rfl⟩
        simp [CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel,
          CertifiedLocalizedCIPInput.reflectUppercaseAuxiliaryLabel, mirrorReference]






theorem referenceState_transport_of_centers
    (input : LocalizedUniversalReference.Input)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration) (root : m.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg root)
    (e : m.Aut) (mirror : Bool) {i : Fin 4}
    (signLaw : ∀ d : m.Center, LigandBranchReaches m root i d.1 →
      ActualLocalSignLaw m cfg e mirror d)
    (d : m.Center) (d_ne_root : d ≠ root)
    (image_ne_root : m.centerPerm e d ≠ root)
    (t u : LocalizedUniversalReference.Occurrence input)
    (tCurrent : t.1.node.current? = some d.1)
    (uCurrent : u.1.node.current? = some (m.centerPerm e d).1)
    (tRoot : input.certified.moleculeGraph.IsTetrahedralCenter t.1.root)
    (uRoot : input.certified.moleculeGraph.IsTetrahedralCenter u.1.root)
    (branchMem : LigandBranchReaches m root i d.1) :
    LocalizedUniversalReference.referenceState input u =
      (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input t) := by
  by_cases twin : ActualPhysicalTerminalTwinCenter input.certified m d
  · have imageTwin : ActualPhysicalTerminalTwinCenter input.certified m
        (m.centerPerm e d) :=
      (actualPhysicalTerminalTwinCenter_centerPerm_iff input.certified m e d).mpr twin
    have tNone := referenceState_eq_none_of_globalTwinCenter input singleBonded acyclic
      noDouble m domain.graphEq d t tCurrent tRoot twin
    have uNone := referenceState_eq_none_of_globalTwinCenter input singleBonded acyclic
      noDouble m domain.graphEq (m.centerPerm e d) u uCurrent uRoot imageTwin
    rw [tNone, uNone]
    cases mirror <;> rfl
  · have imageNotTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified m
        (m.centerPerm e d) :=
      fun h => twin ((actualPhysicalTerminalTwinCenter_centerPerm_iff input.certified m e d).mp h)
    exact (actual_referenceState_automorphism_sign_iff input noDouble singleBonded acyclic m
      cfg root domain d e mirror d_ne_root image_ne_root twin imageNotTwin t u tCurrent
      uCurrent).mpr (signLaw d branchMem)





theorem referenceState_transport_of_atoms
    (input : LocalizedUniversalReference.Input)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration) (root : m.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg root)
    (coverage : m.centers = input.certified.tetrahedralCenterSet)
    (e : m.Aut) (mirror : Bool) {i : Fin 4}
    (signLaw : ∀ d : m.Center, LigandBranchReaches m root i d.1 →
      ActualLocalSignLaw m cfg e mirror d)
    (centerFixed : m.centerPerm e root = root)
    {y a : input.certified.Atom}
    (imageEq : (e : Equiv.Perm input.certified.Atom) y = a)
    (branchMem : y ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph
      root.1 (m.ligandAtomAt root i))
    (t u : LocalizedUniversalReference.Occurrence input)
    (tCurrent : t.1.node.current? = some y)
    (uCurrent : u.1.node.current? = some a)
    (tRoot : input.certified.moleculeGraph.IsTetrahedralCenter t.1.root)
    (uRoot : input.certified.moleculeGraph.IsTetrahedralCenter u.1.root) :
    LocalizedUniversalReference.referenceState input u =
      (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input t) := by
  by_cases candidate : y ∈ m.centers
  · let d : m.Center := ⟨y, candidate⟩
    have rootFixed : (e : Equiv.Perm input.certified.Atom) root.1 = root.1 :=
      congrArg Subtype.val centerFixed
    have branchNe : y ≠ root.1 :=
      AcyclicCutBranchAutomorphism.cutBranch_ne_center input.certified.moleculeGraph
        branchMem
    have dNe : d ≠ root := fun h => branchNe (congrArg Subtype.val h)
    have imageNe : a ≠ root.1 := by
      intro h
      have same : (e : Equiv.Perm input.certified.Atom) y =
          (e : Equiv.Perm input.certified.Atom) root.1 := by
        rw [imageEq, h, rootFixed]
      exact branchNe ((e : Equiv.Perm input.certified.Atom).injective same)
    have imageCenterNe : m.centerPerm e d ≠ root := by
      intro h
      apply imageNe
      have value : (m.centerPerm e d).1 = root.1 := congrArg Subtype.val h
      rw [← imageEq]
      exact value
    have tCurrent' : t.1.node.current? = some d.1 := tCurrent
    have uCurrent' : u.1.node.current? = some (m.centerPerm e d).1 := by
      have value : (m.centerPerm e d).1 = (e : Equiv.Perm input.certified.Atom) y := rfl
      rw [value, imageEq]
      exact uCurrent
    have reaches : LigandBranchReaches m root i d.1 := by
      have mem := branchMem
      rw [← domain.graphEq] at mem
      exact (AcyclicCutBranchAutomorphism.ligandBranchReaches_iff_cutBranchReaches
        m root i d.1).mpr mem
    exact referenceState_transport_of_centers input noDouble singleBonded acyclic m cfg
      root domain e mirror signLaw d dNe imageCenterNe t u tCurrent' uCurrent' tRoot uRoot
      reaches
  · have notMem : y ∉ input.certified.tetrahedralCenterSet := by
      rw [← coverage]
      exact candidate
    have notMemImage : a ∉ input.certified.tetrahedralCenterSet := by
      rw [← coverage]
      intro imageMem
      exact candidate (by
        have preimage : ((e⁻¹ : m.Aut) : Equiv.Perm input.certified.Atom) a ∈ m.centers :=
          (MultiCenterMolecule.Aut.apply_mem_centers_iff (m := m) (e := e⁻¹) a).mpr imageMem
        simpa [← imageEq] using preimage)
    have tNone := referenceState_eq_none_of_actualPhysicalNoncandidate input noDouble t
      ⟨y, tCurrent, notMem⟩
    have uNone := referenceState_eq_none_of_actualPhysicalNoncandidate input noDouble u
      ⟨a, uCurrent, notMemImage⟩
    rw [tNone, uNone]
    cases mirror <;> rfl

/-! ## Transport of physical walks and of the physical nearest predicate -/

/-- Any physical walk from the attachment of branch `i` is carried by the transport automorphism to
a physical walk from the attachment of branch `j`, with the same length and pathhood. -/
theorem exists_walk_image {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) {c : m.Center} {i j : Fin 4} {e : m.Aut}
    (hc : m.centerPerm e c = c) (hi : m.ligandPermAt e c i = j) {a : V}
    (walk : m.mol.underlyingSimpleGraph.Walk (m.ligandAtomAt c i) a) :
    ∃ w : m.mol.underlyingSimpleGraph.Walk (m.ligandAtomAt c j)
        ((e : Equiv.Perm V) a),
      w.length = walk.length ∧ (walk.IsPath → w.IsPath) := by
  have hstart : graphHomOfAut m e (m.ligandAtomAt c i) = m.ligandAtomAt c j := by
    have h := m.ligandAtomAt_ligandPermAt (e := e) (c := c) (i := i)
    rw [hc, hi] at h
    exact h.symm
  refine ⟨(walk.map (graphHomOfAut m e)).copy hstart rfl, ?_, fun path => ?_⟩
  · rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]
  · exact walk_isPath_copy
      (SimpleGraph.Walk.map_isPath_of_injective (f := graphHomOfAut m e)
        (e : Equiv.Perm V).injective path) hstart rfl

/-- The inverse transport carries physical walks from the attachment of branch `j` back to
physical walks from the attachment of branch `i`, with the same length and pathhood. -/
theorem exists_walk_preimage {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) {c : m.Center} {i j : Fin 4} {e : m.Aut}
    (hc : m.centerPerm e c = c) (hi : m.ligandPermAt e c i = j) {a : V}
    (walk : m.mol.underlyingSimpleGraph.Walk (m.ligandAtomAt c j) a) :
    ∃ w : m.mol.underlyingSimpleGraph.Walk (m.ligandAtomAt c i)
        (((e⁻¹ : m.Aut) : Equiv.Perm V) a),
      w.length = walk.length ∧ (walk.IsPath → w.IsPath) := by
  have hc' : m.centerPerm (e⁻¹ : m.Aut) c = c :=
    centerPerm_inv_eq m e c hc
  have hi' : m.ligandPermAt (e⁻¹ : m.Aut) c j = i :=
    ligandPermAt_inv_apply m e c i j hc hi
  have hstart : graphHomOfAut m (e⁻¹ : m.Aut) (m.ligandAtomAt c j) =
      m.ligandAtomAt c i := by
    have h := m.ligandAtomAt_ligandPermAt (e := (e⁻¹ : m.Aut)) (c := c) (i := j)
    rw [hc', hi'] at h
    exact h.symm
  refine ⟨(walk.map (graphHomOfAut m (e⁻¹ : m.Aut))).copy hstart rfl, ?_, fun path => ?_⟩
  · rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]
  · exact walk_isPath_copy
      (SimpleGraph.Walk.map_isPath_of_injective (f := graphHomOfAut m (e⁻¹ : m.Aut))
        (((e⁻¹ : m.Aut) : Equiv.Perm V)).injective path) hstart rfl

/-- Walk transport along an equality of simple graphs. -/
theorem walk_congr_graph {V : Type*} {G H : SimpleGraph V} (h : G = H) {u v : V}
    (walk : G.Walk u v) :
    ∃ w : H.Walk u v, w.length = walk.length ∧ (walk.IsPath → w.IsPath) := by
  cases h
  exact ⟨walk, rfl, id⟩

/-- The physical mark of a branch atom: a non-root global center which is not a physical terminal
twin.  This is a proposition about physical data only; it carries no reader value. -/
def PhysicalBranchMarked (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom) (root : m.Center) (atom : input.Atom) : Prop :=
  atom ≠ root.1 ∧ ∃ member : atom ∈ m.centers,
    ¬ ActualPhysicalTerminalTwinCenter input m ⟨atom, member⟩

/-- The physical mark is invariant under a root-fixing physical automorphism. -/
theorem physicalBranchMarked_transport (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom) (e : m.Aut) {root : m.Center}
    (hc : m.centerPerm e root = root) (atom : input.Atom) :
    PhysicalBranchMarked input m root ((e : Equiv.Perm input.Atom) atom) ↔
      PhysicalBranchMarked input m root atom := by
  have rootFixed : (e : Equiv.Perm input.Atom) root.1 = root.1 :=
    congrArg Subtype.val hc
  constructor
  · rintro ⟨ne, member, notTwin⟩
    have memberPre : atom ∈ m.centers :=
      (MultiCenterMolecule.Aut.apply_mem_centers_iff (m := m) (e := e) atom).mp member
    refine ⟨?_, memberPre, ?_⟩
    · intro h
      exact ne (by rw [h, rootFixed])
    · intro twin
      have himg : m.centerPerm e ⟨atom, memberPre⟩ =
          ⟨(e : Equiv.Perm input.Atom) atom, member⟩ := Subtype.ext rfl
      have imageTwin :
          ActualPhysicalTerminalTwinCenter input m
            (m.centerPerm e ⟨atom, memberPre⟩) :=
        (actualPhysicalTerminalTwinCenter_centerPerm_iff input m e
          ⟨atom, memberPre⟩).mpr twin
      rw [himg] at imageTwin
      exact notTwin imageTwin
  · rintro ⟨ne, member, notTwin⟩
    have memberImage : (e : Equiv.Perm input.Atom) atom ∈ m.centers :=
      (MultiCenterMolecule.Aut.apply_mem_centers_iff (m := m) (e := e) atom).mpr member
    refine ⟨?_, memberImage, ?_⟩
    · intro h
      have same : (e : Equiv.Perm input.Atom) atom =
          (e : Equiv.Perm input.Atom) root.1 := by
        rw [h, rootFixed]
      exact ne ((e : Equiv.Perm input.Atom).injective same)
    · intro twin
      have himg : m.centerPerm e ⟨atom, member⟩ =
          ⟨(e : Equiv.Perm input.Atom) atom, memberImage⟩ := Subtype.ext rfl
      have imageTwin :
          ActualPhysicalTerminalTwinCenter input m
            (m.centerPerm e ⟨atom, member⟩) := by
        rw [himg]
        exact twin
      exact notTwin ((actualPhysicalTerminalTwinCenter_centerPerm_iff input m e
        ⟨atom, member⟩).mp imageTwin)

/-- Reader-free physical unique-nearest data on a cut branch: the branch contains a physical mark
at a physical simple-walk distance, no physical mark lies at a smaller path distance, and the mark
at that distance is unique. -/
def PhysicalBranchUniqueNearest (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom) (root : m.Center)
    (attachment : input.Atom) (center : input.Atom) (distance : Nat) : Prop :=
  center ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph root.1 attachment ∧
    PhysicalBranchMarked input m root center ∧
      center ∈ PhysicalSimpleSphere input.moleculeGraph.underlyingSimpleGraph attachment
        distance ∧
        (∀ (y : input.Atom), y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph
            root.1 attachment → PhysicalBranchMarked input m root y →
          ∀ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk attachment y,
            walk.IsPath → walk.length < distance → False) ∧
          (∀ (y : input.Atom), y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph
              root.1 attachment → PhysicalBranchMarked input m root y →
            ∀ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk attachment y,
              walk.IsPath → walk.length = distance → y = center)

/-- **Physical unique-nearest transport.**  The root-fixing automorphism carrying ligand slot `i`
to slot `j` maps reader-free unique-nearest data of the branch at `i` to unique-nearest data of the
branch at `j` at the same distance, with the center carried along. -/
theorem physicalBranchUniqueNearest_transport
    (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom) (graphEq : m.mol = input.moleculeGraph)
    {c : m.Center} {i j : Fin 4} {e : m.Aut}
    (hc : m.centerPerm e c = c) (hi : m.ligandPermAt e c i = j)
    {center : input.Atom} {distance : Nat}
    (data : PhysicalBranchUniqueNearest input m c (m.ligandAtomAt c i) center distance) :
    PhysicalBranchUniqueNearest input m c (m.ligandAtomAt c j)
      ((e : Equiv.Perm input.Atom) center) distance := by
  obtain ⟨mem, marked, sphere, earlier, unique⟩ := data
  have graphEqSimple : m.mol.underlyingSimpleGraph =
      input.moleculeGraph.underlyingSimpleGraph :=
    congrArg MoleculeGraph.underlyingSimpleGraph graphEq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (cutBranch_mem_transport m graphEq hc hi).mp mem
  · exact (physicalBranchMarked_transport input m e hc center).mpr marked
  · obtain ⟨walk, path, length⟩ := sphere
    obtain ⟨walkM, walkMLength, walkMPath⟩ := walk_congr_graph graphEqSimple.symm walk
    have sphereM : center ∈ PhysicalSimpleSphere m.mol.underlyingSimpleGraph
        (m.ligandAtomAt c i) distance :=
      ⟨walkM, walkMPath path, by rw [walkMLength]; exact length⟩
    obtain ⟨w, pathW, lengthW⟩ :=
      (physicalSimpleSphere_transport m hc hi distance center).mp sphereM
    obtain ⟨wInput, wInputLength, wInputPath⟩ := walk_congr_graph graphEqSimple w
    exact ⟨wInput, wInputPath pathW, by rw [wInputLength]; exact lengthW⟩
  · intro y memY markedY walk path length
    have memBack : (((e⁻¹ : m.Aut) : Equiv.Perm input.Atom) y) ∈
        AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph c.1
          (m.ligandAtomAt c i) := by
      have h := (cutBranch_mem_transport m graphEq hc hi (v :=
        ((e⁻¹ : m.Aut) : Equiv.Perm input.Atom) y)).mpr ?_
      · exact h
      · simpa using memY
    have markedBack : PhysicalBranchMarked input m c
        (((e⁻¹ : m.Aut) : Equiv.Perm input.Atom) y) :=
      (physicalBranchMarked_transport input m e hc
        (((e⁻¹ : m.Aut) : Equiv.Perm input.Atom) y)).mp (by simpa using markedY)
    obtain ⟨walkM, walkMLength, walkMPath⟩ := walk_congr_graph graphEqSimple.symm walk
    obtain ⟨back, backLength, backPath⟩ :=
      exists_walk_preimage m hc hi walkM
    obtain ⟨backInput, backInputLength, backInputPath⟩ :=
      walk_congr_graph graphEqSimple back
    exact earlier _ memBack markedBack backInput
      (backInputPath (backPath (walkMPath path)))
      (by rw [backInputLength, backLength, walkMLength]; exact length)
  · intro y memY markedY walk path length
    have memBack : (((e⁻¹ : m.Aut) : Equiv.Perm input.Atom) y) ∈
        AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph c.1
          (m.ligandAtomAt c i) := by
      have h := (cutBranch_mem_transport m graphEq hc hi (v :=
        ((e⁻¹ : m.Aut) : Equiv.Perm input.Atom) y)).mpr ?_
      · exact h
      · simpa using memY
    have markedBack : PhysicalBranchMarked input m c
        (((e⁻¹ : m.Aut) : Equiv.Perm input.Atom) y) :=
      (physicalBranchMarked_transport input m e hc
        (((e⁻¹ : m.Aut) : Equiv.Perm input.Atom) y)).mp (by simpa using markedY)
    obtain ⟨walkM, walkMLength, walkMPath⟩ := walk_congr_graph graphEqSimple.symm walk
    obtain ⟨back, backLength, backPath⟩ :=
      exists_walk_preimage m hc hi walkM
    obtain ⟨backInput, backInputLength, backInputPath⟩ :=
      walk_congr_graph graphEqSimple back
    have eq := unique _ memBack markedBack backInput
      (backInputPath (backPath (walkMPath path)))
      (by rw [backInputLength, backLength, walkMLength]; exact length)
    rw [← eq]
    simp

/-- A branch with no physical mark stays mark-free under the transport automorphism. -/
theorem physicalBranchUnmarked_transport
    (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom) (graphEq : m.mol = input.moleculeGraph)
    {c : m.Center} {i j : Fin 4} {e : m.Aut}
    (hc : m.centerPerm e c = c) (hi : m.ligandPermAt e c i = j)
    (unmarked : ∀ v : input.Atom, v ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.moleculeGraph c.1 (m.ligandAtomAt c i) → ¬ PhysicalBranchMarked input m c v) :
    ∀ a : input.Atom, a ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph c.1
        (m.ligandAtomAt c j) → ¬ PhysicalBranchMarked input m c a := by
  intro a memA markedA
  have memBack : (((e⁻¹ : m.Aut) : Equiv.Perm input.Atom) a) ∈
      AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph c.1
        (m.ligandAtomAt c i) := by
    have h := (cutBranch_mem_transport m graphEq hc hi (v :=
      ((e⁻¹ : m.Aut) : Equiv.Perm input.Atom) a)).mpr ?_
    · exact h
    · simpa using memA
  have markedBack : PhysicalBranchMarked input m c
      (((e⁻¹ : m.Aut) : Equiv.Perm input.Atom) a) :=
    (physicalBranchMarked_transport input m e hc
      (((e⁻¹ : m.Aut) : Equiv.Perm input.Atom) a)).mp (by simpa using markedA)
  exact unmarked _ memBack markedBack

/-- The heterogeneous physical branch domain — no mark, or unique nearest mark — is transported
from slot `i` to slot `j`. -/
theorem physicalBranchDomain_transport
    (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom) (graphEq : m.mol = input.moleculeGraph)
    {c : m.Center} {i j : Fin 4} {e : m.Aut}
    (hc : m.centerPerm e c = c) (hi : m.ligandPermAt e c i = j)
    (domain : (∀ v : input.Atom, v ∈ AcyclicCutBranchAutomorphism.CutBranch
        input.moleculeGraph c.1 (m.ligandAtomAt c i) →
          ¬ PhysicalBranchMarked input m c v) ∨
      ∃ (center : input.Atom) (distance : Nat),
        PhysicalBranchUniqueNearest input m c (m.ligandAtomAt c i) center distance) :
    (∀ a : input.Atom, a ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph c.1
        (m.ligandAtomAt c j) → ¬ PhysicalBranchMarked input m c a) ∨
      ∃ (center : input.Atom) (distance : Nat),
        PhysicalBranchUniqueNearest input m c (m.ligandAtomAt c j) center distance := by
  rcases domain with unmarked | ⟨center, distance, data⟩
  · exact Or.inl (physicalBranchUnmarked_transport input m graphEq hc hi unmarked)
  · exact Or.inr ⟨(e : Equiv.Perm input.Atom) center, distance,
      physicalBranchUniqueNearest_transport input m graphEq hc hi data⟩










theorem physicalBranchMarked_iff_physicalMarkedAtom
    (input : LocalizedUniversalReference.Input)
    (root : input.certified.TetrahedralCenter) (atom : input.certified.Atom) :
    PhysicalBranchMarked input.certified input.certified.detectedMultiCenterMolecule
        ⟨root.1, root.2⟩ atom ↔
      PhysicalMarkedAtom input root atom :=
  Iff.rfl


theorem physicalBranchUniqueNearest_transport_detected
    (input : LocalizedUniversalReference.Input)
    {c : input.certified.detectedMultiCenterMolecule.Center} {i j : Fin 4}
    {e : input.certified.detectedMultiCenterMolecule.Aut}
    (hc : input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (hi : input.certified.detectedMultiCenterMolecule.ligandPermAt e c i = j)
    {center : input.certified.Atom} {distance : Nat}
    (data : TetraStereo.OneCenter.PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) center distance) :
    TetraStereo.OneCenter.PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c j)
      ((e : Equiv.Perm input.certified.Atom) center) distance :=
  physicalBranchUniqueNearest_transport input.certified
    input.certified.detectedMultiCenterMolecule rfl hc hi data


theorem physicalBranchDomain_transport_detected
    (input : LocalizedUniversalReference.Input)
    {c : input.certified.detectedMultiCenterMolecule.Center} {i j : Fin 4}
    {e : input.certified.detectedMultiCenterMolecule.Aut}
    (hc : input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (hi : input.certified.detectedMultiCenterMolecule.ligandPermAt e c i = j)
    (domain : TetraStereo.OneCenter.PhysicalBranchDomain input ⟨c.1, c.2⟩
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i)) :
    TetraStereo.OneCenter.PhysicalBranchDomain input ⟨c.1, c.2⟩
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c j) :=
  physicalBranchDomain_transport input.certified
    input.certified.detectedMultiCenterMolecule rfl hc hi domain

/-- Two reader-free unique-nearest data of the same physical branch determine the same centre and
the same distance.  This identifies the transported nearest centre with any other nearest centre
found by the actual selector. -/
theorem physicalBranchUniqueNearest_center_unique
    {input : CertifiedLocalizedCIPInput} {m : MultiCenterMolecule input.Atom}
    {root : m.Center} {attachment center₁ center₂ : input.Atom} {distance₁ distance₂ : Nat}
    (data₁ : PhysicalBranchUniqueNearest input m root attachment center₁ distance₁)
    (data₂ : PhysicalBranchUniqueNearest input m root attachment center₂ distance₂) :
    center₁ = center₂ ∧ distance₁ = distance₂ := by
  obtain ⟨mem₁, marked₁, sphere₁, earlier₁, unique₁⟩ := data₁
  obtain ⟨mem₂, marked₂, sphere₂, earlier₂, unique₂⟩ := data₂
  obtain ⟨walk₁, path₁, length₁⟩ := sphere₁
  obtain ⟨walk₂, path₂, length₂⟩ := sphere₂
  have le₁ : distance₁ ≤ distance₂ := by
    by_contra h
    exact earlier₁ center₂ mem₂ marked₂ walk₂ path₂
      (by rw [length₂]; exact Nat.lt_of_not_le h)
  have le₂ : distance₂ ≤ distance₁ := by
    by_contra h
    exact earlier₂ center₁ mem₁ marked₁ walk₁ path₁
      (by rw [length₁]; exact Nat.lt_of_not_le h)
  have distances : distance₁ = distance₂ := Nat.le_antisymm le₁ le₂
  have centers : center₂ = center₁ :=
    unique₁ center₂ mem₂ marked₂ walk₂ path₂ (length₂.trans distances.symm)
  exact ⟨centers.symm, distances⟩



theorem physicalBranchUniqueNearest_center_unique_detected
    (input : LocalizedUniversalReference.Input)
    {root : input.certified.TetrahedralCenter} {attachment center₁ center₂ : input.certified.Atom}
    {distance₁ distance₂ : Nat}
    (data₁ : TetraStereo.OneCenter.PhysicalBranchUniqueNearest input root attachment center₁
      distance₁)
    (data₂ : TetraStereo.OneCenter.PhysicalBranchUniqueNearest input root attachment center₂
      distance₂) :
    center₁ = center₂ ∧ distance₁ = distance₂ :=
  physicalBranchUniqueNearest_center_unique
    (input := input.certified)
    (m := input.certified.detectedMultiCenterMolecule)
    (root := ⟨root.1, root.2⟩) data₁ data₂

/-! ## Actual descriptor covariance

The reference state at the image occurrence is the uppercase reflection of the state at the source
occurrence (`referenceState_transport_of_atoms`).  Reading an upper-case descriptor through this
reflection is the `R/S` swap in the mirror case and the identity otherwise; this is the selected
reference correlation itself, and it is derived, never assumed. -/

/-- Reading an upper-case descriptor label commutes with the mirror reflection of the label. -/
theorem chiralDescriptorOfLabel_reflect (mirror : Bool)
    (label : Option LocalizedAuxiliaryLabel) :
    chiralDescriptorOfLabel
        ((if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id) label) =
      (chiralDescriptorOfLabel label).map (mirrorReference mirror) := by
  cases mirror with
  | false =>
      cases label with
      | none => rfl
      | some label =>
          cases label with
          | chiral descriptor => rfl
          | pseudoasymmetric descriptor => rfl
  | true =>
      cases label with
      | none => rfl
      | some label =>
          cases label with
          | chiral descriptor => rfl
          | pseudoasymmetric descriptor => rfl

/-- **Actual descriptor covariance.**  If the actual label at the image occurrence is the uppercase
reflection of the actual label at the source occurrence, then the descriptor read at the image is
the mirror image of the descriptor read at the source. -/
theorem chiralDescriptor_state_covariance (mirror : Bool)
    {source image : Option LocalizedAuxiliaryLabel}
    (covariance : image =
      (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id) source) :
    chiralDescriptorOfLabel image =
      (chiralDescriptorOfLabel source).map (mirrorReference mirror) := by
  rw [covariance, chiralDescriptorOfLabel_reflect]

/-- **Selected-reference correlation.**  From the actual state covariance and the two actual
chiral labels, the image descriptor is exactly the mirror image of the source descriptor. -/
theorem descriptor_eq_mirrorReference_of_state_covariance (mirror : Bool)
    {source image : Option LocalizedAuxiliaryLabel}
    (covariance : image =
      (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id) source)
    {descriptorSource descriptorImage : RS}
    (sourceChiral : source = some (.chiral descriptorSource))
    (imageChiral : image = some (.chiral descriptorImage)) :
    descriptorImage = mirrorReference mirror descriptorSource := by
  have mapped := chiralDescriptor_state_covariance mirror covariance
  rw [imageChiral, sourceChiral] at mapped
  have reduced : some descriptorImage = some (mirrorReference mirror descriptorSource) := by
    simpa [chiralDescriptorOfLabel] using mapped
  exact Option.some.inj reduced

/-- **Actual descriptor covariance at corresponding branch atoms.** -/
theorem referenceState_descriptor_covariance_of_atoms
    (input : LocalizedUniversalReference.Input)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration) (root : m.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg root)
    (coverage : m.centers = input.certified.tetrahedralCenterSet)
    (e : m.Aut) (mirror : Bool) {i : Fin 4}
    (signLaw : ∀ d : m.Center, LigandBranchReaches m root i d.1 →
      ActualLocalSignLaw m cfg e mirror d)
    (centerFixed : m.centerPerm e root = root)
    {y a : input.certified.Atom}
    (imageEq : (e : Equiv.Perm input.certified.Atom) y = a)
    (branchMem : y ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph
      root.1 (m.ligandAtomAt root i))
    (t u : LocalizedUniversalReference.Occurrence input)
    (tCurrent : t.1.node.current? = some y)
    (uCurrent : u.1.node.current? = some a)
    (tRoot : input.certified.moleculeGraph.IsTetrahedralCenter t.1.root)
    (uRoot : input.certified.moleculeGraph.IsTetrahedralCenter u.1.root) :
    chiralDescriptorOfLabel (LocalizedUniversalReference.referenceState input u) =
      (chiralDescriptorOfLabel
        (LocalizedUniversalReference.referenceState input t)).map (mirrorReference mirror) :=
  chiralDescriptor_state_covariance mirror
    (referenceState_transport_of_atoms input noDouble singleBonded acyclic m cfg root domain
      coverage e mirror signLaw centerFixed imageEq branchMem t u tCurrent uCurrent tRoot uRoot)

/-- **Selected-reference correlation at corresponding branch atoms.**  The image descriptor is the
mirror image of the source descriptor whenever both actual states are chiral. -/
theorem descriptor_covariance_of_atoms
    (input : LocalizedUniversalReference.Input)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration) (root : m.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg root)
    (coverage : m.centers = input.certified.tetrahedralCenterSet)
    (e : m.Aut) (mirror : Bool) {i : Fin 4}
    (signLaw : ∀ d : m.Center, LigandBranchReaches m root i d.1 →
      ActualLocalSignLaw m cfg e mirror d)
    (centerFixed : m.centerPerm e root = root)
    {y a : input.certified.Atom}
    (imageEq : (e : Equiv.Perm input.certified.Atom) y = a)
    (branchMem : y ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph
      root.1 (m.ligandAtomAt root i))
    (t u : LocalizedUniversalReference.Occurrence input)
    (tCurrent : t.1.node.current? = some y)
    (uCurrent : u.1.node.current? = some a)
    (tRoot : input.certified.moleculeGraph.IsTetrahedralCenter t.1.root)
    (uRoot : input.certified.moleculeGraph.IsTetrahedralCenter u.1.root)
    {descriptorSource descriptorImage : RS}
    (sourceChiral : LocalizedUniversalReference.referenceState input t =
      some (.chiral descriptorSource))
    (imageChiral : LocalizedUniversalReference.referenceState input u =
      some (.chiral descriptorImage)) :
    descriptorImage = mirrorReference mirror descriptorSource :=
  descriptor_eq_mirrorReference_of_state_covariance mirror
    (referenceState_transport_of_atoms input noDouble singleBonded acyclic m cfg root domain
      coverage e mirror signLaw centerFixed imageEq branchMem t u tCurrent uCurrent tRoot uRoot)
    sourceChiral imageChiral








/-- **Actual physical-mark covariance at corresponding branch atoms.**  Let two actual production
frame slots have observed attachment atoms which are the physical ligand atoms of slots `i` and `j`,
and let `e` be the physical branch transport witness carrying slot `i` to slot `j`.  For branch
atoms `centerLeft` and `centerRight` with `e centerLeft = centerRight`, the actual physical mark of
the image atom is the mirror image of the actual physical mark of the source atom. -/
theorem branchMarkedDescriptor_covariance
    (input : LocalizedUniversalReference.Input)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    {i j : Fin 4} {e : input.certified.detectedMultiCenterMolecule.Aut}
    (hc : input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (hi : input.certified.detectedMultiCenterMolecule.ligandPermAt e c i = j)
    (mirror : Bool)
    (signLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.certified.detectedMultiCenterMolecule c i d.1 →
        ActualLocalSignLaw input.certified.detectedMultiCenterMolecule cfg e mirror d)
    (frameLeft frameRight : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputedLeft : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frameLeft)
    (frameComputedRight : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frameRight)
    (slotLeft slotRight : Fin 4)
    (oAtomLeft oAtomRight : input.certified.Atom)
    (oObservedLeft : (frameLeft.cursorAt slotLeft).occurrence.1.node.current? = some oAtomLeft)
    (oObservedRight : (frameRight.cursorAt slotRight).occurrence.1.node.current? = some oAtomRight)
    (attachLeft : oAtomLeft =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt c i)
    (attachRight : oAtomRight =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt c j)
    {centerLeft centerRight : input.certified.Atom}
    (imageEq : (e : Equiv.Perm input.certified.Atom) centerLeft = centerRight)
    (memLeft : centerLeft ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtomLeft)
    (memRight : centerRight ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtomRight) :
    branchMarkedDescriptor input c frameRight frameComputedRight slotRight singleBonded acyclic
        oAtomRight oObservedRight centerRight =
      (branchMarkedDescriptor input c frameLeft frameComputedLeft slotLeft singleBonded acyclic
        oAtomLeft oObservedLeft centerLeft).map (mirrorReference mirror) := by
  let pLeft : Position (actualSlotTree input c frameLeft frameComputedLeft slotLeft) :=
    (actualSlotCutEquiv input c frameLeft frameComputedLeft slotLeft singleBonded acyclic
      oAtomLeft oObservedLeft).symm ⟨centerLeft, memLeft⟩
  let pRight : Position (actualSlotTree input c frameRight frameComputedRight slotRight) :=
    (actualSlotCutEquiv input c frameRight frameComputedRight slotRight singleBonded acyclic
      oAtomRight oObservedRight).symm ⟨centerRight, memRight⟩
  let leftOcc : LocalizedUniversalReference.Occurrence input :=
    (positionSource pLeft).occurrence
  let rightOcc : LocalizedUniversalReference.Occurrence input :=
    (positionSource pRight).occurrence
  have leftCurrent : leftOcc.1.node.current? = some centerLeft := by
    dsimp only [leftOcc]
    rw [positionAtom_spec singleBonded acyclic pLeft]
    dsimp only [pLeft]
    rw [actualSlotCutEquiv_symm_apply input c frameLeft frameComputedLeft slotLeft
      singleBonded acyclic oAtomLeft oObservedLeft memLeft]
  have rightCurrent : rightOcc.1.node.current? = some centerRight := by
    dsimp only [rightOcc]
    rw [positionAtom_spec singleBonded acyclic pRight]
    dsimp only [pRight]
    rw [actualSlotCutEquiv_symm_apply input c frameRight frameComputedRight slotRight
      singleBonded acyclic oAtomRight oObservedRight memRight]
  have leftRoot : input.certified.moleculeGraph.IsTetrahedralCenter leftOcc.1.root := by
    have hroot : leftOcc.1.root = c.1 := by
      dsimp only [leftOcc, pLeft]
      rw [positionSource_root_eq_of_realized
        (actualSlotTree_realizes input c frameLeft frameComputedLeft slotLeft)]
      rw [actualSlotTree_sameRoot, ActualReaderPhysicalBranchInverse.topTarget_root]
    rw [hroot]
    exact (input.certified.moleculeGraph.mem_tetrahedralCenterSet c.1).1 c.2
  have rightRoot : input.certified.moleculeGraph.IsTetrahedralCenter rightOcc.1.root := by
    have hroot : rightOcc.1.root = c.1 := by
      dsimp only [rightOcc, pRight]
      rw [positionSource_root_eq_of_realized
        (actualSlotTree_realizes input c frameRight frameComputedRight slotRight)]
      rw [actualSlotTree_sameRoot, ActualReaderPhysicalBranchInverse.topTarget_root]
    rw [hroot]
    exact (input.certified.moleculeGraph.mem_tetrahedralCenterSet c.1).1 c.2
  have memLeft' : centerLeft ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) := by
    rw [← attachLeft]
    exact memLeft
  have covariance :=
    referenceState_transport_of_atoms input noDouble singleBonded acyclic
      input.certified.detectedMultiCenterMolecule cfg c domain rfl e mirror signLaw hc
      imageEq memLeft' leftOcc rightOcc leftCurrent rightCurrent leftRoot rightRoot
  have mapped := chiralDescriptor_state_covariance mirror covariance
  dsimp only [leftOcc, rightOcc] at mapped
  unfold branchMarkedDescriptor
  rw [dif_pos memRight, dif_pos memLeft]
  exact mapped






theorem localizedPhysicalCompoundSelectorShape_of_covariant_selections
    (left right : List RS) (mirror : Bool)
    (emptyIff : left = [] ↔ right = [])
    (leftZeroOrOne : left = [] ∨ ∃ reference : RS, left = [reference])
    (correspond : ∀ reference : RS, left = [reference] →
      right = [mirrorReference mirror reference]) :
    LocalizedPhysicalCompoundSelectorShape left right mirror := by
  rcases leftZeroOrOne with rfl | ⟨reference, rfl⟩
  · exact Or.inl ⟨rfl, emptyIff.mp rfl⟩
  · have rightEq := correspond reference rfl
    refine Or.inr ⟨reference, rfl, ?_⟩
    rw [rightEq]
    rfl




theorem localizedPhysicalCompoundSelectorShape_of_zeroOrOne_correspondence
    (left right : List RS) (mirror : Bool)
    (leftZeroOrOne : left = [] ∨ ∃ reference : RS, left = [reference])
    (rightZeroOrOne : right = [] ∨ ∃ reference : RS, right = [reference])
    (emptyIff : left = [] ↔ right = [])
    (correspond : ∀ referenceLeft : RS, left = [referenceLeft] →
      ∀ referenceRight : RS, right = [referenceRight] →
        referenceRight = mirrorReference mirror referenceLeft) :
    LocalizedPhysicalCompoundSelectorShape left right mirror := by
  rcases leftZeroOrOne with rfl | ⟨referenceLeft, rfl⟩
  · exact Or.inl ⟨rfl, emptyIff.mp rfl⟩
  · have notNil : ([referenceLeft] : List RS) ≠ [] := by simp
    have rightNotNil : right ≠ [] := fun h => notNil (emptyIff.mpr h)
    rcases rightZeroOrOne with rfl | ⟨referenceRight, rightEq⟩
    · exact absurd rfl rightNotNil
    · have correlation := correspond referenceLeft rfl referenceRight rightEq
      refine Or.inr ⟨referenceLeft, rfl, ?_⟩
      rw [rightEq, correlation]
      rfl



theorem physicalBranchUnmarked_transport_detected
    (input : LocalizedUniversalReference.Input)
    {c : input.certified.detectedMultiCenterMolecule.Center} {i j : Fin 4}
    {e : input.certified.detectedMultiCenterMolecule.Aut}
    (hc : input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (hi : input.certified.detectedMultiCenterMolecule.ligandPermAt e c i = j)
    (unmarked : ∀ v : input.certified.Atom, v ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) →
      ¬ PhysicalMarkedAtom input ⟨c.1, c.2⟩ v) :
    ∀ a : input.certified.Atom, a ∈ AcyclicCutBranchAutomorphism.CutBranch
        input.certified.moleculeGraph c.1
          (input.certified.detectedMultiCenterMolecule.ligandAtomAt c j) →
      ¬ PhysicalMarkedAtom input ⟨c.1, c.2⟩ a :=
  physicalBranchUnmarked_transport input.certified
    input.certified.detectedMultiCenterMolecule rfl hc hi unmarked













theorem localizedPhysicalCompoundSelectorShape_of_physicalBranchTransport
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (calibratedDomain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotLeft slotRight : Fin 4)
    (oAtomLeft oAtomRight : input.certified.Atom)
    (oObservedLeft : (frame.cursorAt slotLeft).occurrence.1.node.current? = some oAtomLeft)
    (oObservedRight : (frame.cursorAt slotRight).occurrence.1.node.current? = some oAtomRight)
    {i j : Fin 4} {e : input.certified.detectedMultiCenterMolecule.Aut}
    (hc : input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (hi : input.certified.detectedMultiCenterMolecule.ligandPermAt e c i = j)
    (mirror : Bool)
    (signLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.certified.detectedMultiCenterMolecule c i d.1 →
        ActualLocalSignLaw input.certified.detectedMultiCenterMolecule cfg e mirror d)
    (attachLeft : oAtomLeft =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt c i)
    (attachRight : oAtomRight =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt c j)
    (leftDomain : PhysicalBranchDomain input ⟨c.1, c.2⟩ oAtomLeft) :
    LocalizedPhysicalCompoundSelectorShape
      (localizedRule4bReferencesFromRankedLabels
        (actualSlotCompoundKey input c frame frameComputed slotLeft).prior.rule4aKey.rankedLabels)
      (localizedRule4bReferencesFromRankedLabels
        (actualSlotCompoundKey input c frame frameComputed slotRight).prior.rule4aKey.rankedLabels)
      mirror := by
  have physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c :=
    actualGeneralRigidPhysicalDomain_of_physicalCalibratedDomain input.certified cfg c
      calibratedDomain
  have globalDomain : ActualGeneralRigidGlobalPhysicalDomain input.certified
      (input.certified.canonicalReindexConfiguration cfg) ⟨c.1, c.2⟩ :=
    actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
      input.certified cfg ⟨c.1, c.2⟩ physicalDomain
  rcases leftDomain with unmarkedLeft | ⟨centerLeft, distanceLeft, uniqueLeft⟩
  · -- Empty source branch: the image branch is empty as well, so both selections vanish.
    have unmarkedLeft' : ∀ v : input.certified.Atom,
        v ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1
          (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) →
        ¬ PhysicalMarkedAtom input ⟨c.1, c.2⟩ v := by
      intro v mem
      have memLeft : v ∈ AcyclicCutBranchAutomorphism.CutBranch
          input.certified.moleculeGraph c.1 oAtomLeft := by
        rw [← attachLeft] at mem
        exact mem
      exact unmarkedLeft v memLeft
    have unmarkedRight' :=
      physicalBranchUnmarked_transport_detected input hc hi unmarkedLeft'
    have unmarkedRight : ∀ v : input.certified.Atom,
        v ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1 oAtomRight →
        ¬ PhysicalMarkedAtom input ⟨c.1, c.2⟩ v := by
      intro v mem
      have memRight : v ∈ AcyclicCutBranchAutomorphism.CutBranch
          input.certified.moleculeGraph c.1
            (input.certified.detectedMultiCenterMolecule.ligandAtomAt c j) := by
        rw [attachRight] at mem
        exact mem
      exact unmarkedRight' v memRight
    have leftNil := actualSlot_physicalBranchUnmarked_references_nil input c frame frameComputed
      slotLeft singleBonded acyclic hcharge noDouble
      (input.certified.canonicalReindexConfiguration cfg) globalDomain oAtomLeft oObservedLeft
      unmarkedLeft
    have rightNil := actualSlot_physicalBranchUnmarked_references_nil input c frame frameComputed
      slotRight singleBonded acyclic hcharge noDouble
      (input.certified.canonicalReindexConfiguration cfg) globalDomain oAtomRight oObservedRight
      unmarkedRight
    exact Or.inl ⟨leftNil.1, rightNil.1⟩
  · -- Unique nearest source mark: transport the same centre and distance to the image branch.
    obtain ⟨descriptorLeft, markedLeft⟩ :=
      exists_markedBranchUniqueNearest_of_physicalBranchUniqueNearest input c frame frameComputed
        slotLeft singleBonded acyclic hcharge noDouble
        (input.certified.canonicalReindexConfiguration cfg) globalDomain oAtomLeft oObservedLeft
        uniqueLeft
    obtain ⟨leftSelection, _leftReferences, _leftReading, _leftReadings, _leftReference⟩ :=
      actualSlot_markedBranchUniqueNearest_references_singleton input c frame frameComputed
        slotLeft singleBonded acyclic hcharge noDouble
        (input.certified.canonicalReindexConfiguration cfg) globalDomain oAtomLeft oObservedLeft
        markedLeft
    have uniqueLeft' : TetraStereo.OneCenter.PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i)
          centerLeft distanceLeft := by
      rw [← attachLeft]
      exact uniqueLeft
    have uniqueRight' := physicalBranchUniqueNearest_transport_detected input hc hi uniqueLeft'
    have uniqueRight : TetraStereo.OneCenter.PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩
        oAtomRight ((e : Equiv.Perm input.certified.Atom) centerLeft) distanceLeft := by
      rw [attachRight]
      exact uniqueRight'
    obtain ⟨descriptorRight, markedRight⟩ :=
      exists_markedBranchUniqueNearest_of_physicalBranchUniqueNearest input c frame frameComputed
        slotRight singleBonded acyclic hcharge noDouble
        (input.certified.canonicalReindexConfiguration cfg) globalDomain oAtomRight oObservedRight
        uniqueRight
    obtain ⟨rightSelection, _rightReferences, _rightReading, _rightReadings, _rightReference⟩ :=
      actualSlot_markedBranchUniqueNearest_references_singleton input c frame frameComputed
        slotRight singleBonded acyclic hcharge noDouble
        (input.certified.canonicalReindexConfiguration cfg) globalDomain oAtomRight oObservedRight
        markedRight
    -- Actual physical-mark covariance at the two transported occurrences.
    have covariance :=
      branchMarkedDescriptor_covariance input noDouble singleBonded acyclic c cfg calibratedDomain
        hc hi mirror signLaw frame frame frameComputed frameComputed slotLeft slotRight
        oAtomLeft oAtomRight oObservedLeft oObservedRight attachLeft attachRight
        (centerLeft := centerLeft)
        (centerRight := (e : Equiv.Perm input.certified.Atom) centerLeft) rfl
        uniqueLeft.1 markedRight.1
    have correlation : descriptorRight = mirrorReference mirror descriptorLeft := by
      have reduced : some descriptorRight =
          (branchMarkedDescriptor input c frame frameComputed slotLeft singleBonded acyclic
            oAtomLeft oObservedLeft centerLeft).map (mirrorReference mirror) := by
        rw [← markedRight.2.1]
        exact covariance
      rw [markedLeft.2.1] at reduced
      have pair : some descriptorRight = some (mirrorReference mirror descriptorLeft) := by
        simpa using reduced
      exact Option.some.inj pair
    refine localizedPhysicalCompoundSelectorShape_of_covariant_selections
      (left := localizedRule4bReferencesFromRankedLabels
        (actualSlotCompoundKey input c frame frameComputed slotLeft).prior.rule4aKey.rankedLabels)
      (right := localizedRule4bReferencesFromRankedLabels
        (actualSlotCompoundKey input c frame frameComputed slotRight).prior.rule4aKey.rankedLabels)
      (mirror := mirror) ?emptyIff (Or.inr ⟨descriptorLeft, leftSelection⟩) ?correspond
    · constructor
      · intro h
        rw [leftSelection] at h
        exact absurd h (by simp)
      · intro h
        rw [rightSelection] at h
        exact absurd h (by simp)
    · intro reference hreference
      rw [rightSelection, correlation]
      have hleft : ([descriptorLeft] : List RS) = [reference] :=
        leftSelection.symm.trans hreference
      exact congrArg (List.map (mirrorReference mirror)) hleft












theorem referenceState_transport_of_centers_of_physicalDomain
    (input : LocalizedUniversalReference.Input)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    {i : Fin 4} {e : input.certified.detectedMultiCenterMolecule.Aut}
    (hc : input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (mirror : Bool)
    (signLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.certified.detectedMultiCenterMolecule c i d.1 →
        ActualLocalSignLaw input.certified.detectedMultiCenterMolecule cfg e mirror d)
    (d : input.certified.detectedMultiCenterMolecule.Center) (d_ne_root : d ≠ c)
    (image_ne_root :
      input.certified.detectedMultiCenterMolecule.centerPerm e d ≠ c)
    (t u : LocalizedUniversalReference.Occurrence input)
    (tCurrent : t.1.node.current? = some d.1)
    (uCurrent : u.1.node.current? =
      some (input.certified.detectedMultiCenterMolecule.centerPerm e d).1)
    (tRoot : t.1.root = c.1)
    (uRoot : u.1.root = c.1)
    (branchMem : LigandBranchReaches
      input.certified.detectedMultiCenterMolecule c i d.1) :
    LocalizedUniversalReference.referenceState input u =
      (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input t) := by
  have rootFixed : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
    congrArg Subtype.val hc
  have centerRoot : input.certified.moleculeGraph.IsTetrahedralCenter c.1 :=
    (input.certified.moleculeGraph.mem_tetrahedralCenterSet c.1).1 c.2
  by_cases twin : ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule d
  · have imageTwin : ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule
        (input.certified.detectedMultiCenterMolecule.centerPerm e d) :=
      (actualPhysicalTerminalTwinCenter_centerPerm_iff input.certified
        input.certified.detectedMultiCenterMolecule e d).mpr twin
    have tNone := referenceState_eq_none_of_globalTwinCenter input singleBonded acyclic
      noDouble input.certified.detectedMultiCenterMolecule domain.graphEq d t tCurrent
      (by rw [tRoot]; exact centerRoot) twin
    have uNone := referenceState_eq_none_of_globalTwinCenter input singleBonded acyclic
      noDouble input.certified.detectedMultiCenterMolecule domain.graphEq
      (input.certified.detectedMultiCenterMolecule.centerPerm e d) u uCurrent
      (by rw [uRoot]; exact centerRoot) imageTwin
    rw [tNone, uNone]
    cases mirror <;> rfl
  · have imageNotTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule
        (input.certified.detectedMultiCenterMolecule.centerPerm e d) :=
      fun h => twin ((actualPhysicalTerminalTwinCenter_centerPerm_iff input.certified
        input.certified.detectedMultiCenterMolecule e d).mp h)
    exact (referenceState_generalRigidAutomorphism_label_sign_iff_of_physicalDomain input
      noDouble singleBonded acyclic hcharge cfg c domain c.1 e mirror rootFixed d t u
      d_ne_root image_ne_root twin imageNotTwin tRoot uRoot tCurrent uCurrent).mpr
      (signLaw d branchMem)

/-- **Actual reference-state reflection at branch atoms, general domain.**  The same reflection
statement at an arbitrary pair of corresponding cut-branch atoms.  A current atom which is not a
global center reads `none` on both sides; a global non-root center is handled by the center form
above, using the coverage of the detected candidate set. -/
theorem referenceState_transport_of_atoms_of_physicalDomain
    (input : LocalizedUniversalReference.Input)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    {i : Fin 4} {e : input.certified.detectedMultiCenterMolecule.Aut}
    (hc : input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (mirror : Bool)
    (signLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.certified.detectedMultiCenterMolecule c i d.1 →
        ActualLocalSignLaw input.certified.detectedMultiCenterMolecule cfg e mirror d)
    {y a : input.certified.Atom}
    (imageEq : (e : Equiv.Perm input.certified.Atom) y = a)
    (branchMem : y ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph
      c.1 (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i))
    (t u : LocalizedUniversalReference.Occurrence input)
    (tCurrent : t.1.node.current? = some y)
    (uCurrent : u.1.node.current? = some a)
    (tRoot : t.1.root = c.1)
    (uRoot : u.1.root = c.1) :
    LocalizedUniversalReference.referenceState input u =
      (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input t) := by
  let m : MultiCenterMolecule input.certified.Atom :=
    input.certified.detectedMultiCenterMolecule
  by_cases candidate : y ∈ m.centers
  · let d : m.Center := ⟨y, candidate⟩
    have rootFixed : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
      congrArg Subtype.val hc
    have branchNe : y ≠ c.1 :=
      AcyclicCutBranchAutomorphism.cutBranch_ne_center input.certified.moleculeGraph
        branchMem
    have dNe : d ≠ c := fun h => branchNe (congrArg Subtype.val h)
    have imageNe : a ≠ c.1 := by
      intro h
      have same : (e : Equiv.Perm input.certified.Atom) y =
          (e : Equiv.Perm input.certified.Atom) c.1 := by
        rw [imageEq, h, rootFixed]
      exact branchNe ((e : Equiv.Perm input.certified.Atom).injective same)
    have imageCenterNe : m.centerPerm e d ≠ c := by
      intro h
      apply imageNe
      have value : (m.centerPerm e d).1 = c.1 := congrArg Subtype.val h
      rw [← imageEq]
      exact value
    have tCurrent' : t.1.node.current? = some d.1 := tCurrent
    have uCurrent' : u.1.node.current? = some (m.centerPerm e d).1 := by
      have value : (m.centerPerm e d).1 = (e : Equiv.Perm input.certified.Atom) y := rfl
      rw [value, imageEq]
      exact uCurrent
    have reaches : LigandBranchReaches m c i d.1 := by
      have mem := branchMem
      rw [← domain.graphEq] at mem
      exact (AcyclicCutBranchAutomorphism.ligandBranchReaches_iff_cutBranchReaches
        m c i d.1).mpr mem
    exact referenceState_transport_of_centers_of_physicalDomain input noDouble singleBonded
      acyclic hcharge cfg c domain hc mirror signLaw d dNe imageCenterNe t u tCurrent'
      uCurrent' tRoot uRoot reaches
  · have notMem : y ∉ input.certified.tetrahedralCenterSet := candidate
    have notMemImage : a ∉ input.certified.tetrahedralCenterSet := by
      intro imageMem
      exact candidate (by
        have preimage : ((e⁻¹ : m.Aut) : Equiv.Perm input.certified.Atom) a ∈ m.centers :=
          (MultiCenterMolecule.Aut.apply_mem_centers_iff (m := m) (e := e⁻¹) a).mpr imageMem
        simpa [← imageEq] using preimage)
    have tNone := referenceState_eq_none_of_actualPhysicalNoncandidate input noDouble t
      ⟨y, tCurrent, notMem⟩
    have uNone := referenceState_eq_none_of_actualPhysicalNoncandidate input noDouble u
      ⟨a, uCurrent, notMemImage⟩
    rw [tNone, uNone]
    cases mirror <;> rfl

/-- **Actual physical-mark covariance at corresponding branch atoms, general domain.** -/
theorem branchMarkedDescriptor_covariance_of_physicalDomain
    (input : LocalizedUniversalReference.Input)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    {i j : Fin 4} {e : input.certified.detectedMultiCenterMolecule.Aut}
    (hc : input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (hi : input.certified.detectedMultiCenterMolecule.ligandPermAt e c i = j)
    (mirror : Bool)
    (signLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.certified.detectedMultiCenterMolecule c i d.1 →
        ActualLocalSignLaw input.certified.detectedMultiCenterMolecule cfg e mirror d)
    (frameLeft frameRight : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputedLeft : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frameLeft)
    (frameComputedRight : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frameRight)
    (slotLeft slotRight : Fin 4)
    (oAtomLeft oAtomRight : input.certified.Atom)
    (oObservedLeft : (frameLeft.cursorAt slotLeft).occurrence.1.node.current? = some oAtomLeft)
    (oObservedRight : (frameRight.cursorAt slotRight).occurrence.1.node.current? = some oAtomRight)
    (attachLeft : oAtomLeft =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt c i)
    (attachRight : oAtomRight =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt c j)
    {centerLeft centerRight : input.certified.Atom}
    (imageEq : (e : Equiv.Perm input.certified.Atom) centerLeft = centerRight)
    (memLeft : centerLeft ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtomLeft)
    (memRight : centerRight ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtomRight) :
    branchMarkedDescriptor input c frameRight frameComputedRight slotRight singleBonded acyclic
        oAtomRight oObservedRight centerRight =
      (branchMarkedDescriptor input c frameLeft frameComputedLeft slotLeft singleBonded acyclic
        oAtomLeft oObservedLeft centerLeft).map (mirrorReference mirror) := by
  let pLeft : Position (actualSlotTree input c frameLeft frameComputedLeft slotLeft) :=
    (actualSlotCutEquiv input c frameLeft frameComputedLeft slotLeft singleBonded acyclic
      oAtomLeft oObservedLeft).symm ⟨centerLeft, memLeft⟩
  let pRight : Position (actualSlotTree input c frameRight frameComputedRight slotRight) :=
    (actualSlotCutEquiv input c frameRight frameComputedRight slotRight singleBonded acyclic
      oAtomRight oObservedRight).symm ⟨centerRight, memRight⟩
  let leftOcc : LocalizedUniversalReference.Occurrence input :=
    (positionSource pLeft).occurrence
  let rightOcc : LocalizedUniversalReference.Occurrence input :=
    (positionSource pRight).occurrence
  have leftCurrent : leftOcc.1.node.current? = some centerLeft := by
    dsimp only [leftOcc]
    rw [positionAtom_spec singleBonded acyclic pLeft]
    dsimp only [pLeft]
    rw [actualSlotCutEquiv_symm_apply input c frameLeft frameComputedLeft slotLeft
      singleBonded acyclic oAtomLeft oObservedLeft memLeft]
  have rightCurrent : rightOcc.1.node.current? = some centerRight := by
    dsimp only [rightOcc]
    rw [positionAtom_spec singleBonded acyclic pRight]
    dsimp only [pRight]
    rw [actualSlotCutEquiv_symm_apply input c frameRight frameComputedRight slotRight
      singleBonded acyclic oAtomRight oObservedRight memRight]
  have leftRoot : leftOcc.1.root = c.1 := by
    dsimp only [leftOcc, pLeft]
    rw [positionSource_root_eq_of_realized
      (actualSlotTree_realizes input c frameLeft frameComputedLeft slotLeft)]
    rw [actualSlotTree_sameRoot, ActualReaderPhysicalBranchInverse.topTarget_root]
  have rightRoot : rightOcc.1.root = c.1 := by
    dsimp only [rightOcc, pRight]
    rw [positionSource_root_eq_of_realized
      (actualSlotTree_realizes input c frameRight frameComputedRight slotRight)]
    rw [actualSlotTree_sameRoot, ActualReaderPhysicalBranchInverse.topTarget_root]
  have memLeft' : centerLeft ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) := by
    rw [← attachLeft]
    exact memLeft
  have covariance :=
    referenceState_transport_of_atoms_of_physicalDomain input noDouble singleBonded acyclic
      hcharge cfg c domain hc mirror signLaw imageEq memLeft' leftOcc rightOcc
      leftCurrent rightCurrent leftRoot rightRoot
  have mapped := chiralDescriptor_state_covariance mirror covariance
  dsimp only [leftOcc, rightOcc] at mapped
  unfold branchMarkedDescriptor
  rw [dif_pos memRight, dif_pos memLeft]
  exact mapped






theorem localizedPhysicalCompoundSelectorShape_of_physicalBranchTransport_of_physicalDomain
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotLeft slotRight : Fin 4)
    (oAtomLeft oAtomRight : input.certified.Atom)
    (oObservedLeft : (frame.cursorAt slotLeft).occurrence.1.node.current? = some oAtomLeft)
    (oObservedRight : (frame.cursorAt slotRight).occurrence.1.node.current? = some oAtomRight)
    {i j : Fin 4} {e : input.certified.detectedMultiCenterMolecule.Aut}
    (hc : input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (hi : input.certified.detectedMultiCenterMolecule.ligandPermAt e c i = j)
    (mirror : Bool)
    (signLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.certified.detectedMultiCenterMolecule c i d.1 →
        ActualLocalSignLaw input.certified.detectedMultiCenterMolecule cfg e mirror d)
    (attachLeft : oAtomLeft =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt c i)
    (attachRight : oAtomRight =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt c j)
    (leftDomain : PhysicalBranchDomain input ⟨c.1, c.2⟩ oAtomLeft) :
    LocalizedPhysicalCompoundSelectorShape
      (localizedRule4bReferencesFromRankedLabels
        (actualSlotCompoundKey input c frame frameComputed slotLeft).prior.rule4aKey.rankedLabels)
      (localizedRule4bReferencesFromRankedLabels
        (actualSlotCompoundKey input c frame frameComputed slotRight).prior.rule4aKey.rankedLabels)
      mirror := by
  have globalDomain : ActualGeneralRigidGlobalPhysicalDomain input.certified
      (input.certified.canonicalReindexConfiguration cfg) ⟨c.1, c.2⟩ :=
    actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
      input.certified cfg ⟨c.1, c.2⟩ domain
  rcases leftDomain with unmarkedLeft | ⟨centerLeft, distanceLeft, uniqueLeft⟩
  · -- Empty source branch: the image branch is empty as well, so both selections vanish.
    have unmarkedLeft' : ∀ v : input.certified.Atom,
        v ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1
          (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) →
        ¬ PhysicalMarkedAtom input ⟨c.1, c.2⟩ v := by
      intro v mem
      have memLeft : v ∈ AcyclicCutBranchAutomorphism.CutBranch
          input.certified.moleculeGraph c.1 oAtomLeft := by
        rw [← attachLeft] at mem
        exact mem
      exact unmarkedLeft v memLeft
    have unmarkedRight' :=
      physicalBranchUnmarked_transport_detected input hc hi unmarkedLeft'
    have unmarkedRight : ∀ v : input.certified.Atom,
        v ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1 oAtomRight →
        ¬ PhysicalMarkedAtom input ⟨c.1, c.2⟩ v := by
      intro v mem
      have memRight : v ∈ AcyclicCutBranchAutomorphism.CutBranch
          input.certified.moleculeGraph c.1
            (input.certified.detectedMultiCenterMolecule.ligandAtomAt c j) := by
        rw [attachRight] at mem
        exact mem
      exact unmarkedRight' v memRight
    have leftNil := actualSlot_physicalBranchUnmarked_references_nil input c frame frameComputed
      slotLeft singleBonded acyclic hcharge noDouble
      (input.certified.canonicalReindexConfiguration cfg) globalDomain oAtomLeft oObservedLeft
      unmarkedLeft
    have rightNil := actualSlot_physicalBranchUnmarked_references_nil input c frame frameComputed
      slotRight singleBonded acyclic hcharge noDouble
      (input.certified.canonicalReindexConfiguration cfg) globalDomain oAtomRight oObservedRight
      unmarkedRight
    exact Or.inl ⟨leftNil.1, rightNil.1⟩
  · -- Unique nearest source mark: transport the same centre and distance to the image branch.
    obtain ⟨descriptorLeft, markedLeft⟩ :=
      exists_markedBranchUniqueNearest_of_physicalBranchUniqueNearest input c frame frameComputed
        slotLeft singleBonded acyclic hcharge noDouble
        (input.certified.canonicalReindexConfiguration cfg) globalDomain oAtomLeft oObservedLeft
        uniqueLeft
    obtain ⟨leftSelection, _leftReferences, _leftReading, _leftReadings, _leftReference⟩ :=
      actualSlot_markedBranchUniqueNearest_references_singleton input c frame frameComputed
        slotLeft singleBonded acyclic hcharge noDouble
        (input.certified.canonicalReindexConfiguration cfg) globalDomain oAtomLeft oObservedLeft
        markedLeft
    have uniqueLeft' : TetraStereo.OneCenter.PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i)
          centerLeft distanceLeft := by
      rw [← attachLeft]
      exact uniqueLeft
    have uniqueRight' := physicalBranchUniqueNearest_transport_detected input hc hi uniqueLeft'
    have uniqueRight : TetraStereo.OneCenter.PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩
        oAtomRight ((e : Equiv.Perm input.certified.Atom) centerLeft) distanceLeft := by
      rw [attachRight]
      exact uniqueRight'
    obtain ⟨descriptorRight, markedRight⟩ :=
      exists_markedBranchUniqueNearest_of_physicalBranchUniqueNearest input c frame frameComputed
        slotRight singleBonded acyclic hcharge noDouble
        (input.certified.canonicalReindexConfiguration cfg) globalDomain oAtomRight oObservedRight
        uniqueRight
    obtain ⟨rightSelection, _rightReferences, _rightReading, _rightReadings, _rightReference⟩ :=
      actualSlot_markedBranchUniqueNearest_references_singleton input c frame frameComputed
        slotRight singleBonded acyclic hcharge noDouble
        (input.certified.canonicalReindexConfiguration cfg) globalDomain oAtomRight oObservedRight
        markedRight
    -- Actual physical-mark covariance at the two transported occurrences.
    have covariance :=
      branchMarkedDescriptor_covariance_of_physicalDomain input noDouble singleBonded acyclic
        hcharge c cfg domain hc hi mirror signLaw frame frame frameComputed frameComputed
        slotLeft slotRight oAtomLeft oAtomRight oObservedLeft oObservedRight attachLeft
        attachRight (centerLeft := centerLeft)
        (centerRight := (e : Equiv.Perm input.certified.Atom) centerLeft) rfl
        uniqueLeft.1 markedRight.1
    have correlation : descriptorRight = mirrorReference mirror descriptorLeft := by
      have reduced : some descriptorRight =
          (branchMarkedDescriptor input c frame frameComputed slotLeft singleBonded acyclic
            oAtomLeft oObservedLeft centerLeft).map (mirrorReference mirror) := by
        rw [← markedRight.2.1]
        exact covariance
      rw [markedLeft.2.1] at reduced
      have pair : some descriptorRight = some (mirrorReference mirror descriptorLeft) := by
        simpa using reduced
      exact Option.some.inj pair
    refine localizedPhysicalCompoundSelectorShape_of_covariant_selections
      (left := localizedRule4bReferencesFromRankedLabels
        (actualSlotCompoundKey input c frame frameComputed slotLeft).prior.rule4aKey.rankedLabels)
      (right := localizedRule4bReferencesFromRankedLabels
        (actualSlotCompoundKey input c frame frameComputed slotRight).prior.rule4aKey.rankedLabels)
      (mirror := mirror) ?emptyIff (Or.inr ⟨descriptorLeft, leftSelection⟩) ?correspond
    · constructor
      · intro h
        rw [leftSelection] at h
        exact absurd h (by simp)
      · intro h
        rw [rightSelection] at h
        exact absurd h (by simp)
    · intro reference hreference
      rw [rightSelection, correlation]
      have hleft : ([descriptorLeft] : List RS) = [reference] :=
        leftSelection.symm.trans hreference
      exact congrArg (List.map (mirrorReference mirror)) hleft

/-! ## The retained reference lists of the actual slot keys -/

/-- **The actual slot key retains the executable selector.**  For the production slot key the
Rules-4b/4c reference list is exactly the executable selector applied to the retained Rule-4a
ranked labels, by the actual production compound builder. -/
theorem actualSlotCompoundKey_references_eq
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) :
    (actualSlotCompoundKey input c frame frameComputed slot).prior.references =
      localizedRule4bReferencesFromRankedLabels
        (actualSlotCompoundKey input c frame frameComputed slot).prior.rule4aKey.rankedLabels :=
  buildLocalizedRerootCompoundRule4bcKey?_references_eq input.certified
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (referenceDependencyView input c)
    (localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input))
    (frame.cursorAt slot)
    (actualSlotCompoundKey input c frame frameComputed slot).prior
    (actualSlotPriorBuilt input c frame frameComputed slot)




theorem localizedPhysicalCompoundSelectorShape_references_of_physicalBranchTransport
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (calibratedDomain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotLeft slotRight : Fin 4)
    (oAtomLeft oAtomRight : input.certified.Atom)
    (oObservedLeft : (frame.cursorAt slotLeft).occurrence.1.node.current? = some oAtomLeft)
    (oObservedRight : (frame.cursorAt slotRight).occurrence.1.node.current? = some oAtomRight)
    {i j : Fin 4} {e : input.certified.detectedMultiCenterMolecule.Aut}
    (hc : input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (hi : input.certified.detectedMultiCenterMolecule.ligandPermAt e c i = j)
    (mirror : Bool)
    (signLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.certified.detectedMultiCenterMolecule c i d.1 →
        ActualLocalSignLaw input.certified.detectedMultiCenterMolecule cfg e mirror d)
    (attachLeft : oAtomLeft =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt c i)
    (attachRight : oAtomRight =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt c j)
    (leftDomain : PhysicalBranchDomain input ⟨c.1, c.2⟩ oAtomLeft) :
    LocalizedPhysicalCompoundSelectorShape
      (actualSlotCompoundKey input c frame frameComputed slotLeft).prior.references
      (actualSlotCompoundKey input c frame frameComputed slotRight).prior.references
      mirror := by
  rw [actualSlotCompoundKey_references_eq input c frame frameComputed slotLeft,
    actualSlotCompoundKey_references_eq input c frame frameComputed slotRight]
  exact localizedPhysicalCompoundSelectorShape_of_physicalBranchTransport input singleBonded
    acyclic hcharge noDouble c cfg calibratedDomain frame frameComputed slotLeft slotRight
    oAtomLeft oAtomRight oObservedLeft oObservedRight hc hi mirror signLaw attachLeft
    attachRight leftDomain





theorem localizedPhysicalCompoundSelectorShape_references_of_physicalBranchTransport_of_physicalDomain
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotLeft slotRight : Fin 4)
    (oAtomLeft oAtomRight : input.certified.Atom)
    (oObservedLeft : (frame.cursorAt slotLeft).occurrence.1.node.current? = some oAtomLeft)
    (oObservedRight : (frame.cursorAt slotRight).occurrence.1.node.current? = some oAtomRight)
    {i j : Fin 4} {e : input.certified.detectedMultiCenterMolecule.Aut}
    (hc : input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (hi : input.certified.detectedMultiCenterMolecule.ligandPermAt e c i = j)
    (mirror : Bool)
    (signLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.certified.detectedMultiCenterMolecule c i d.1 →
        ActualLocalSignLaw input.certified.detectedMultiCenterMolecule cfg e mirror d)
    (attachLeft : oAtomLeft =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt c i)
    (attachRight : oAtomRight =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt c j)
    (leftDomain : PhysicalBranchDomain input ⟨c.1, c.2⟩ oAtomLeft) :
    LocalizedPhysicalCompoundSelectorShape
      (actualSlotCompoundKey input c frame frameComputed slotLeft).prior.references
      (actualSlotCompoundKey input c frame frameComputed slotRight).prior.references
      mirror := by
  rw [actualSlotCompoundKey_references_eq input c frame frameComputed slotLeft,
    actualSlotCompoundKey_references_eq input c frame frameComputed slotRight]
  exact localizedPhysicalCompoundSelectorShape_of_physicalBranchTransport_of_physicalDomain
    input singleBonded acyclic hcharge noDouble c cfg domain frame frameComputed slotLeft
    slotRight oAtomLeft oAtomRight oObservedLeft oObservedRight hc hi mirror signLaw
    attachLeft attachRight leftDomain

end LocalizedPhysicalReferenceCovariance

end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.graphHomOfAut
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.graphHomOfAut_apply
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.walk_isPath_copy
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.ligandBranchReaches_map_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.cutBranch_mem_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.physicalSimpleSphere_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.mirrorReference
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.mirrorReference_true
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.mirrorReference_false
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.reflectUppercaseOptionalLabel_chiral_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.referenceState_transport_of_centers
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.referenceState_transport_of_atoms
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.exists_walk_image
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.exists_walk_preimage
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.walk_congr_graph
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.PhysicalBranchMarked
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.physicalBranchMarked_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.PhysicalBranchUniqueNearest
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.physicalBranchUniqueNearest_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.physicalBranchUnmarked_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.physicalBranchDomain_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.physicalBranchMarked_iff_physicalMarkedAtom
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.physicalBranchUniqueNearest_transport_detected
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.physicalBranchDomain_transport_detected
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.physicalBranchUniqueNearest_center_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.physicalBranchUniqueNearest_center_unique_detected
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.chiralDescriptorOfLabel_reflect
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.chiralDescriptor_state_covariance
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.descriptor_eq_mirrorReference_of_state_covariance
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.referenceState_descriptor_covariance_of_atoms
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.descriptor_covariance_of_atoms
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.branchMarkedDescriptor_covariance
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.localizedPhysicalCompoundSelectorShape_of_covariant_selections
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.localizedPhysicalCompoundSelectorShape_of_zeroOrOne_correspondence
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.physicalBranchUnmarked_transport_detected
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.localizedPhysicalCompoundSelectorShape_of_physicalBranchTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.referenceState_transport_of_centers_of_physicalDomain
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.referenceState_transport_of_atoms_of_physicalDomain
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.branchMarkedDescriptor_covariance_of_physicalDomain
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.localizedPhysicalCompoundSelectorShape_of_physicalBranchTransport_of_physicalDomain
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.actualSlotCompoundKey_references_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.localizedPhysicalCompoundSelectorShape_references_of_physicalBranchTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance.localizedPhysicalCompoundSelectorShape_references_of_physicalBranchTransport_of_physicalDomain
