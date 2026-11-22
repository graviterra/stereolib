import TetraStereo.Engine.LocalizedChemicalRingPhysicalCertificate
import TetraStereo.OneCenter.TerminalTwinConfigurationGauge

set_option autoImplicit false

namespace TetraStereo.Engine.RingLocalInversion

open OneCenter FinitePhysicalBranchTransport LocalizedActualPhysicalBranchDecision
open LocalizedChemicalRingPhysicalAdmission LocalizedRecursiveAuxiliaryPhysicalDomain

variable {V L : Type*} [Fintype V] [DecidableEq V] [DecidableEq L]
variable (m : MultiCenterMolecule V) (atom : V → L) (cfg : m.Configuration) (target : m.Center)

/-- A single physical witness for the whole sign pattern. A graph
automorphism may move other centers provided their signs are transported.
The inversion concerns handedness, not the choice of an even local frame. -/
def Witness (e : m.Aut) : Prop :=
  m.centerPerm e target = target ∧ (∀ v, atom ((e : Equiv.Perm V) v) = atom v) ∧
    ∀ d, m.configurationSign (e • cfg) d =
      if d = target then -m.configurationSign cfg d else m.configurationSign cfg d

/-- Check one proposed atom permutation at every center before accepting it.
The existing graph test preserves atomic number, mass, charge, every bond
order, and center membership. The additional atom projection refines it. -/
def candidate (e : Equiv.Perm V) : Bool :=
  decide (e target.val = target.val) &&
    decide (∀ v, atom (e v) = atom v) && isAutCheck m e &&
    decide (∀ d : m.Center, signOK m cfg (decide (d = target)) e d = true)

private theorem signOK_action (e : m.Aut) (d : m.Center) (flip : Bool) :
    signOK m cfg flip e d = true ↔
      m.configurationSign (e • cfg) (m.centerPerm e d) =
        (if flip then -1 else 1) * m.configurationSign cfg (m.centerPerm e d) := by
  have h : (e : Equiv.Perm V) d.val ∈ m.centers := (m.centerPerm e d).property
  have eqn : (⟨(e : Equiv.Perm V) d.val,h⟩ : m.Center) = m.centerPerm e d := Subtype.ext rfl
  rw [signOK,dif_pos h,decide_eq_true_iff,eqn,localFun_eq m e d,funSign_perm,
    ← sign_equation_iff, m.configurationSign_smul]
  have undo : (m.centerPerm e)⁻¹ ((m.centerPerm e) d) = d := (m.centerPerm e).symm_apply_apply d
  rw [undo]
  rfl

theorem candidate_iff (e : Equiv.Perm V) :
    candidate m atom cfg target e = true ↔ ∃ E : m.Aut, (E : Equiv.Perm V) = e ∧ Witness m atom cfg target E := by
  simp only [candidate,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨fix,labels⟩,aut⟩,checks⟩
    let E : m.Aut := ⟨e,(isAutCheck_iff m e).mp aut⟩
    have fixed : m.centerPerm E target = target := Subtype.ext fix
    refine ⟨E,rfl,fixed,labels,?_⟩
    intro d
    obtain ⟨u,rfl⟩ := (m.centerPerm E).surjective d
    have signs := (signOK_action m cfg E u (decide (u = target))).mp (checks u)
    have image : m.centerPerm E u = target ↔ u = target := by
      nth_rw 1 [← fixed]
      exact (m.centerPerm E).injective.eq_iff
    by_cases isTarget : u = target
    · subst u
      simpa [fixed] using signs
    · have preserved := mt image.mp isTarget
      simpa [isTarget,preserved] using signs
  · rintro ⟨E,rfl,fixed,labels,signs⟩
    refine ⟨⟨⟨congrArg Subtype.val fixed,labels⟩,(isAutCheck_iff m E).mpr E.property⟩,?_⟩
    intro d
    apply (signOK_action m cfg E d _).mpr
    have image : m.centerPerm E d = target ↔ d = target := by
      nth_rw 1 [← fixed]
      exact (m.centerPerm E).injective.eq_iff
    have transported := signs (m.centerPerm E d)
    by_cases isTarget : d = target
    · subst d
      simpa [fixed] using transported
    · have preserved := mt image.mp isTarget
      simpa [isTarget,preserved] using transported

/-- Finite reference search over atom permutations. This determines a
whole-molecule sign-pattern equivalence; a CIP priority order is separate. -/
def equivalent : Bool :=
  decide (∃ e : Equiv.Perm V, candidate m atom cfg target e = true)

theorem equivalent_iff : equivalent m atom cfg target = true ↔ ∃ E, Witness m atom cfg target E := by
  rw [equivalent,decide_eq_true_iff]
  constructor
  · rintro ⟨e,hit⟩
    obtain ⟨E,_,witness⟩ := (candidate_iff m atom cfg target e).mp hit
    exact ⟨E,witness⟩
  · rintro ⟨E,witness⟩
    exact ⟨E,(candidate_iff m atom cfg target E).mpr ⟨E,rfl,witness⟩⟩

theorem inequivalent_iff : equivalent m atom cfg target = false ↔ ∀ E, ¬Witness m atom cfg target E := by
  rw [← not_exists,equivalent_iff m atom cfg target |>.not.symm]
  cases equivalent m atom cfg target <;> decide

/-- The explicit swap establishes equivalence without enumerating any atom
permutations when a pair of identical terminal atoms is already known. -/
theorem equivalent_of_terminal_twins {a b : V}
    (twins : TerminalTwinConfigurationGauge.TerminalTwinPair m target a b) (same : atom a = atom b) :
    equivalent m atom cfg target = true := by
  apply (equivalent_iff ..).mpr
  refine ⟨twins.swapAut,twins.centerPerm_swapAut_apply target,?_,?_⟩
  · intro v
    change atom (Equiv.swap a b v) = atom v
    by_cases ha : v = a
    · simpa [ha] using same.symm
    by_cases hb : v = b
    · simpa [hb] using same
    rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  · intro d
    by_cases hd : d = target <;> simpa [hd] using twins.configurationSign_swapAut_apply cfg d

/-- For a coordinate-only observation the input's written '@' parity is a
neighbor-order annotation. All other atom-record fields remain fixed. -/
def coordinateAtom (input : LocalizedChemicalRing.Input) (v : input.certified.Atom) : Option AtomSpec :=
  input.molecule.atoms[v.val]?.map fun a => { a with tetrahedral? := none }

/-- Total on the coordinate-admitted inputs, with every local handedness
read directly in the certified graph's canonical neighbor frame. -/
def fromCoordinates (input : LocalizedChemicalRing.Input)
    (_accepted : LocalizedChemicalRing.coordinatesAdmitted input = true)
    (target : (actualCanonicalMolecule input.certified).Center) : Bool :=
  equivalent (actualCanonicalMolecule input.certified) (coordinateAtom input) (coordinateCfg input.certified) target

theorem fromCoordinates_spec (input : LocalizedChemicalRing.Input)
    (accepted : LocalizedChemicalRing.coordinatesAdmitted input = true)
    (target : (actualCanonicalMolecule input.certified).Center) :
    (∀ d, ActualPhysicalCalibratedCoordinates input.certified (actualCanonicalMolecule input.certified)
      (coordinateCfg input.certified) d) ∧
    (fromCoordinates input accepted target = true ↔
      ∃ E, Witness (actualCanonicalMolecule input.certified) (coordinateAtom input)
        (coordinateCfg input.certified) target E) ∧
    (fromCoordinates input accepted target = false ↔
      ∀ E, ¬Witness (actualCanonicalMolecule input.certified) (coordinateAtom input)
        (coordinateCfg input.certified) target E) :=
  ⟨canonical_all_calibrated input.certified accepted,equivalent_iff ..,inequivalent_iff ..⟩

/-- Optional stricter test for literal equality of raw atom records,
including the neighbor-order-dependent input parity field. -/
def fromRawRecords (input : LocalizedChemicalRing.Input)
    (_accepted : LocalizedChemicalRing.coordinatesAdmitted input = true)
    (target : (actualCanonicalMolecule input.certified).Center) : Bool :=
  equivalent (actualCanonicalMolecule input.certified) (fun v => input.molecule.atoms[v.val]?)
    (coordinateCfg input.certified) target

theorem fromRawRecords_iff (input : LocalizedChemicalRing.Input)
    (accepted : LocalizedChemicalRing.coordinatesAdmitted input = true)
    (target : (actualCanonicalMolecule input.certified).Center) :
    fromRawRecords input accepted target = true ↔
      ∃ E, Witness (actualCanonicalMolecule input.certified)
        (fun v => input.molecule.atoms[v.val]?) (coordinateCfg input.certified) target E :=
  equivalent_iff ..

end TetraStereo.Engine.RingLocalInversion

assert_kernel_only TetraStereo.Engine.RingLocalInversion.candidate_iff
assert_kernel_only TetraStereo.Engine.RingLocalInversion.equivalent_iff
assert_kernel_only TetraStereo.Engine.RingLocalInversion.inequivalent_iff
assert_kernel_only TetraStereo.Engine.RingLocalInversion.equivalent_of_terminal_twins
assert_kernel_only TetraStereo.Engine.RingLocalInversion.fromCoordinates_spec
assert_kernel_only TetraStereo.Engine.RingLocalInversion.fromRawRecords_iff
