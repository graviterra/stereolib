import TetraStereo.OneCenter.LocalizedOccurrenceFixedPoint

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Executable root records for the localized occurrence carrier

`localizedAtomRootOccurrence` and `localizedFinalOccurrence` construct the distinguished root
occurrence of an atom-rooted official subtree with `classical` in scope, so the carrier file marks
them `noncomputable`.  The record each one packages is nevertheless plain data: the selected root
atom, the empty sibling address, the official root node, and remaining depth `fuel + 1`.

This module restates that record as a direct computable definition, proves membership through
`mem_localizedOccurrences_iff` together with the independent bounded-reachability constructor
`DeclarativeLocalizedOccurrenceSubtree.subtreeRoot`, and proves that the twin is equal to the
existing occurrence.  It then builds a plain occurrence system whose only change with respect to
the fixed-point interface is the executable final-center root, and shows that system equal to the
one built from the existing noncomputable root.

The executable evaluator is a parameter of that system: this module asserts no chemical rule
semantics, and the fixed-point existence results remain in `LocalizedOccurrenceFixedPoint`.
-/

namespace CertifiedLocalizedCIPInput

open DeclarativeCIP

/-! ## Direct root records -/

/-- Direct root frame record for an arbitrary atom: the selected root atom, the empty address, the
official root node, and remaining depth `fuel + 1`.  This is exactly the data packaged by the
carrier's noncomputable root occurrences. -/
def localizedAtomRootFrame (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (atom : input.Atom) : input.LocalizedCIPOccurrenceFrame :=
  { root := atom
    address := []
    node := OfficialCIPNode.root atom
    remaining := fuel + 1 }

/-- The direct root record is a member of the molecule-wide finite carrier, by the exact
enumeration theorem and the root constructor of the independent bounded-reachability relation. -/
def localizedAtomRootOccurrenceExecutable
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    input.LocalizedCIPOccurrence fuel :=
  ⟨input.localizedAtomRootFrame fuel atom,
    (input.mem_localizedOccurrences_iff fuel _).mpr
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [] (fuel + 1)
        (OfficialCIPNode.root atom))⟩

@[simp] theorem localizedAtomRootOccurrenceExecutable_root
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    (input.localizedAtomRootOccurrenceExecutable fuel atom).1.root = atom := rfl

@[simp] theorem localizedAtomRootOccurrenceExecutable_address
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    (input.localizedAtomRootOccurrenceExecutable fuel atom).1.address = [] := rfl

@[simp] theorem localizedAtomRootOccurrenceExecutable_node
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    (input.localizedAtomRootOccurrenceExecutable fuel atom).1.node =
      OfficialCIPNode.root atom := rfl

@[simp] theorem localizedAtomRootOccurrenceExecutable_remaining
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    (input.localizedAtomRootOccurrenceExecutable fuel atom).1.remaining = fuel + 1 := rfl

/-- The direct record twin is the carrier's existing atom-root occurrence. -/
theorem localizedAtomRootOccurrenceExecutable_eq_localizedAtomRootOccurrence
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    input.localizedAtomRootOccurrenceExecutable fuel atom =
      input.localizedAtomRootOccurrence fuel atom :=
  Subtype.ext rfl

/-- Direct final-center root frame: the same record at the detected center's atom. -/
def localizedFinalRootFrame (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter) : input.LocalizedCIPOccurrenceFrame :=
  { root := center.val
    address := []
    node := OfficialCIPNode.root center.val
    remaining := fuel + 1 }

/-- Executable final-center root occurrence, packaged in the molecule-wide carrier. -/
def localizedFinalOccurrenceExecutable
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (center : input.TetrahedralCenter) :
    input.LocalizedCIPOccurrence fuel :=
  ⟨input.localizedFinalRootFrame fuel center,
    (input.mem_localizedOccurrences_iff fuel _).mpr
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [] (fuel + 1)
        (OfficialCIPNode.root center.val))⟩

@[simp] theorem localizedFinalOccurrenceExecutable_root
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (center : input.TetrahedralCenter) :
    (input.localizedFinalOccurrenceExecutable fuel center).1.root = center.val := rfl

@[simp] theorem localizedFinalOccurrenceExecutable_address
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (center : input.TetrahedralCenter) :
    (input.localizedFinalOccurrenceExecutable fuel center).1.address = [] := rfl

@[simp] theorem localizedFinalOccurrenceExecutable_node
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (center : input.TetrahedralCenter) :
    (input.localizedFinalOccurrenceExecutable fuel center).1.node =
      OfficialCIPNode.root center.val := rfl

@[simp] theorem localizedFinalOccurrenceExecutable_remaining
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (center : input.TetrahedralCenter) :
    (input.localizedFinalOccurrenceExecutable fuel center).1.remaining = fuel + 1 := rfl

/-- The executable final-center root is the carrier's existing noncomputable final occurrence. -/
theorem localizedFinalOccurrenceExecutable_eq_localizedFinalOccurrence
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (center : input.TetrahedralCenter) :
    input.localizedFinalOccurrenceExecutable fuel center =
      input.localizedFinalOccurrence fuel center :=
  Subtype.ext rfl

/-! ## Plain occurrence system at the executable root -/

/-- A plain occurrence system over the localized carrier whose final occurrence is the direct
executable root record.  The derivation relation and the raw outcome evaluator are parameters, so
no chemical semantics is asserted here. -/
def localizedOccurrenceSystemWithExecutableRoot
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (derivation :
      OccurrenceState (input.LocalizedCIPOccurrence fuel) LocalizedAuxiliaryLabel →
        input.LocalizedCIPOccurrence fuel → Option LocalizedAuxiliaryLabel → Prop)
    (evaluator :
      OccurrenceState (input.LocalizedCIPOccurrence fuel) LocalizedAuxiliaryLabel →
        input.LocalizedCIPOccurrence fuel → Option LocalizedAuxiliaryLabel) :
    OccurrenceSystem input.TetrahedralCenter (input.LocalizedCIPOccurrence fuel)
      LocalizedAuxiliaryLabel where
  finalOccurrence := input.localizedFinalOccurrenceExecutable fuel
  descriptorOf := localizedAuxiliaryDescriptor
  DeclarativeDerivation := derivation
  executableStep := evaluator

@[simp] theorem localizedOccurrenceSystemWithExecutableRoot_finalOccurrence
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    {derivation :
      OccurrenceState (input.LocalizedCIPOccurrence fuel) LocalizedAuxiliaryLabel →
        input.LocalizedCIPOccurrence fuel → Option LocalizedAuxiliaryLabel → Prop}
    {evaluator :
      OccurrenceState (input.LocalizedCIPOccurrence fuel) LocalizedAuxiliaryLabel →
        input.LocalizedCIPOccurrence fuel → Option LocalizedAuxiliaryLabel} :
    (input.localizedOccurrenceSystemWithExecutableRoot fuel derivation evaluator).finalOccurrence =
      input.localizedFinalOccurrenceExecutable fuel := rfl

@[simp] theorem localizedOccurrenceSystemWithExecutableRoot_executableStep
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    {derivation :
      OccurrenceState (input.LocalizedCIPOccurrence fuel) LocalizedAuxiliaryLabel →
        input.LocalizedCIPOccurrence fuel → Option LocalizedAuxiliaryLabel → Prop}
    {evaluator :
      OccurrenceState (input.LocalizedCIPOccurrence fuel) LocalizedAuxiliaryLabel →
        input.LocalizedCIPOccurrence fuel → Option LocalizedAuxiliaryLabel} :
    (input.localizedOccurrenceSystemWithExecutableRoot fuel derivation evaluator).executableStep =
      evaluator := rfl

/-- The fixed-point interface's own fields at the direct executable root: the same declarative
relation, descriptor projection and restricted executable step as
`localizedAuxiliaryOccurrenceSystem`, with only the final occurrence replaced. -/
def localizedAuxiliaryOccurrenceSystemExecutableRoot
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    OccurrenceSystem input.TetrahedralCenter (input.LocalizedCIPOccurrence fuel)
      LocalizedAuxiliaryLabel :=
  input.localizedOccurrenceSystemWithExecutableRoot fuel
    semantics.DeclarativeDerivation
    (input.localizedExecutableStep semantics.executableRule)

/-- The plain executable-root system is the existing localized occurrence system: the root twins
agree by `Subtype.ext`, and every other field is shared unchanged. -/
theorem localizedAuxiliaryOccurrenceSystemExecutableRoot_eq_old
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    input.localizedAuxiliaryOccurrenceSystemExecutableRoot semantics =
      input.localizedAuxiliaryOccurrenceSystem semantics := by
  have rootEquality : input.localizedFinalOccurrenceExecutable fuel =
      input.localizedFinalOccurrence fuel :=
    funext fun center =>
      input.localizedFinalOccurrenceExecutable_eq_localizedFinalOccurrence fuel center
  unfold localizedAuxiliaryOccurrenceSystemExecutableRoot localizedOccurrenceSystemWithExecutableRoot
    localizedAuxiliaryOccurrenceSystem
  rw [rootEquality]

/-- The correspondence obligation of the fixed-point interface transfers to the plain
executable-root system along the proved system equality. -/
theorem localizedAuxiliaryOccurrenceSystemExecutableRoot_derivationStepCorrespondence
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    (input.localizedAuxiliaryOccurrenceSystemExecutableRoot semantics).DerivationStepCorrespondence := by
  rw [input.localizedAuxiliaryOccurrenceSystemExecutableRoot_eq_old semantics]
  exact input.localizedAuxiliaryDerivationStepCorrespondence semantics

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
