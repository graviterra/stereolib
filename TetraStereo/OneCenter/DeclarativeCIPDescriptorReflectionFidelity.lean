import TetraStereo.OneCenter.DeclarativeCIP
import TetraStereo.OneCenter.P91DescriptorSyntax
import TetraStereo.OneCenter.P92StereogenicUnitSemantics
import TetraStereo.OneCenter.CIPOfficialRules
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

/-!
# Source fidelity of `Descriptor.mirror`

`DeclarativeCIP.Descriptor.mirror` is a semantic reflection operation on **final**
stereodescriptors.  This module establishes its conformance with the independently transcribed
primary-source semantics instead of merely restating its table:

* `P91DescriptorSyntax.ReflectionResult` enumerates the reflection results stated in P-91.2.1.1:
  capital `R/S` and `M/P` exchange, lower-case `r/s` (and `m/p`, which this vocabulary does not
  use) are fixed.
* `P92StereogenicUnitSemantics.EnantiomorphicDoubleBondDescriptor.reflected` exchanges
  `seqCis`/`seqTrans`; P-92.6 states that these are the reflection-variant sequence descriptors
  of geometrically enantiomorphic double bonds.
* `P92StereogenicUnitSemantics.PseudoDescriptor.reflected` independently fixes the lower-case
  pseudoasymmetric descriptors.
* `P92StereogenicUnitSemantics.AxialDescriptor` and `PlanarDescriptor` name exactly the pairs
  `Ra/Sa` and `Rp/Sp`.  P-91.2.1.1 states that capitalised CIP stereodescriptors are
  reflection-variant, so on each two-symbol vocabulary the reflection partner is *forced* to be
  the exchange; `axial_reflection_partner_forced` and `planar_reflection_partner_forced` record
  that derivation rather than asserting the partner.

The `E`/`Z` pair is the one vocabulary element for which the primary sources supply an enum
representative but no independent reflection operation: P-91.2.1.2 lists `E`/`Z` under *non*-CIP
stereodescriptors describing diastereomorphic alkenes, outside the capitalised-CIP reflection
clause of P-91.2.1.1 (`E_Z_not_capitalizedCIPName`), and P-92.6 assigns reflection variance only
to the enantiomorphic double-bond descriptors `seqCis`/`seqTrans`.  The fixed values are therefore
exposed as an explicit exact-table clause (`mirror_fixes_E_Z`), not presented as a source-enumerated
reflection result.

The superseded pre-repair table is retained only as `legacyMirror`, a kernel-checked negative
guard.  It shows that the former involution argument was insufficient: an involution may be
falsely reflection-faithful, so source conformance needs the primary clauses, not just
`mirror (mirror d) = d`.

Rule-3 geometry is deliberately kept separate.  `OfficialRule3Geometry.seqcis`/`seqtrans` are
lower-case Rule-3 *geometry classes*; P-92.6's capital `seqCis`/`seqTrans` are Rule-5 final
stereodescriptors.  The Rule-3 reflection action is the identity, and
`no_reflection_equivariant_injection_from_rule5_sequence_to_rule3_geometry` proves that the two
vocabularies cannot be identified while preserving the source reflection actions.
-/

namespace Descriptor

/-! ## Translation into the independent P-91 descriptor vocabulary -/

/-- Explicit translation from the declarative final-descriptor vocabulary to the independent
P-91 vocabulary.  Every constructor has a named P-91 representative. -/
def toP91 : Descriptor → BlueBookP91.Descriptor
  | R => .capitalR
  | S => .capitalS
  | r => .lowercaseR
  | s => .lowercaseS
  | Ra => .axialR
  | Sa => .axialS
  | Rp => .planarR
  | Sp => .planarS
  | M => .capitalM
  | P => .capitalP
  | E => .capitalE
  | Z => .capitalZ
  | seqCis => .seqCis
  | seqTrans => .seqTrans

@[simp] theorem toP91_R : toP91 R = .capitalR := rfl
@[simp] theorem toP91_S : toP91 S = .capitalS := rfl
@[simp] theorem toP91_r : toP91 r = .lowercaseR := rfl
@[simp] theorem toP91_s : toP91 s = .lowercaseS := rfl
@[simp] theorem toP91_Ra : toP91 Ra = .axialR := rfl
@[simp] theorem toP91_Sa : toP91 Sa = .axialS := rfl
@[simp] theorem toP91_Rp : toP91 Rp = .planarR := rfl
@[simp] theorem toP91_Sp : toP91 Sp = .planarS := rfl
@[simp] theorem toP91_M : toP91 M = .capitalM := rfl
@[simp] theorem toP91_P : toP91 P = .capitalP := rfl
@[simp] theorem toP91_E : toP91 E = .capitalE := rfl
@[simp] theorem toP91_Z : toP91 Z = .capitalZ := rfl
@[simp] theorem toP91_seqCis : toP91 seqCis = .seqCis := rfl
@[simp] theorem toP91_seqTrans : toP91 seqTrans = .seqTrans := rfl

/-- The translation loses no descriptor: distinct final descriptors remain distinct source
symbols. -/
theorem toP91_injective : Function.Injective toP91 := by
  intro a b h
  cases a <;> cases b <;> simp_all [toP91]

/-! ## P-91: the enumerated reflection results -/

/-- The constructors whose reflection result is enumerated by P-91.2.1.1 itself.  The relation
`BlueBookP91.ReflectionResult` is deliberately partial, so conformance is claimed only on this
fragment. -/
def P91Enumerated : Descriptor → Prop
  | R => True
  | S => True
  | r => True
  | s => True
  | M => True
  | P => True
  | _ => False

/-- `Descriptor.mirror` agrees with every reflection result that P-91 states. -/
theorem p91_reflection_conformance (d : Descriptor) (enumerated : P91Enumerated d) :
    BlueBookP91.ReflectionResult (toP91 d) (toP91 (mirror d)) := by
  cases d <;> simp [P91Enumerated, mirror, BlueBookP91.ReflectionResult] at enumerated ⊢

/-- On the P-91-enumerated fragment, a reflection result determines a unique source symbol: the
one produced by `Descriptor.mirror`.  This is the bridge used by the uniqueness theorem below. -/
theorem reflectionResult_partner_unique (d : Descriptor) (e : BlueBookP91.Descriptor)
    (result : BlueBookP91.ReflectionResult (toP91 d) e) :
    e = toP91 (mirror d) := by
  cases d <;> cases e <;>
    simp [mirror, toP91, BlueBookP91.ReflectionResult] at result ⊢

/-! ## P-92: lower-case pseudoasymmetric descriptors -/

/-- Partial translation of the lower-case pseudoasymmetric fragment into the independent P-92
vocabulary. -/
def toP92Pseudo : Descriptor → Option BlueBookP92.PseudoDescriptor
  | r => some .r
  | s => some .s
  | _ => none

/-- `Descriptor.mirror` agrees with `PseudoDescriptor.reflected`, which P-92 defines as the
identity on lower-case descriptors. -/
theorem mirror_conforms_to_P92_pseudo (d : Descriptor)
    (source : BlueBookP92.PseudoDescriptor)
    (h : toP92Pseudo d = some source) :
    toP92Pseudo (mirror d) =
      some (BlueBookP92.PseudoDescriptor.reflected source) := by
  cases d <;> cases source <;>
    simp [toP92Pseudo, mirror, BlueBookP92.PseudoDescriptor.reflected] at h ⊢

/-- Independent P-92 statement of lower-case invariance, restated for use as a source witness. -/
theorem p92_pseudo_reflection_invariant (source : BlueBookP92.PseudoDescriptor) :
    BlueBookP92.PseudoDescriptor.reflected source = source :=
  BlueBookP92.PseudoDescriptor.reflected_invariant source

/-! ## P-92: enantiomorphic double-bond sequence descriptors -/

/-- Partial translation of the Rule-5 sequence fragment into the independent P-92 vocabulary. -/
def toP92Sequence :
    Descriptor → Option BlueBookP92.EnantiomorphicDoubleBondDescriptor
  | seqCis => some .seqCis
  | seqTrans => some .seqTrans
  | _ => none

/-- Exact recognition table for the partial translation. -/
theorem toP92Sequence_eq_some_iff (d : Descriptor)
    (s : BlueBookP92.EnantiomorphicDoubleBondDescriptor) :
    toP92Sequence d = some s ↔
      (d = seqCis ∧ s = .seqCis) ∨ (d = seqTrans ∧ s = .seqTrans) := by
  cases d <;> cases s <;> simp [toP92Sequence]

/-- `Descriptor.mirror` agrees with `EnantiomorphicDoubleBondDescriptor.reflected`, which
exchanges `seqCis`/`seqTrans`. -/
theorem mirror_conforms_to_P92_sequence (d : Descriptor)
    (s : BlueBookP92.EnantiomorphicDoubleBondDescriptor)
    (h : toP92Sequence d = some s) :
    toP92Sequence (mirror d) =
      some (BlueBookP92.EnantiomorphicDoubleBondDescriptor.reflected s) := by
  cases d <;> cases s <;>
    simp [toP92Sequence, mirror,
      BlueBookP92.EnantiomorphicDoubleBondDescriptor.reflected] at h ⊢

/-- P-92.6 states that the sequence descriptors are reflection-variant: every one of them moves
under the independent reflection operation. -/
theorem p92_sequence_reflection_changes
    (s : BlueBookP92.EnantiomorphicDoubleBondDescriptor) :
    BlueBookP92.EnantiomorphicDoubleBondDescriptor.reflected s ≠ s :=
  BlueBookP92.enantiomorphicDoubleBondDescriptor_reflection_changes s

/-- P-92's sequence reflection is an involution. -/
theorem p92_sequence_reflection_involutive
    (s : BlueBookP92.EnantiomorphicDoubleBondDescriptor) :
    BlueBookP92.EnantiomorphicDoubleBondDescriptor.reflected
        (BlueBookP92.EnantiomorphicDoubleBondDescriptor.reflected s) = s :=
  BlueBookP92.enantiomorphicDoubleBondDescriptor_reflection_involutive s

/-! ## P-92: axial and planar descriptor pairs -/

/-- The reflection table forced on the two-symbol P-92 axial vocabulary by the P-91.2.1.1
capitalised-variance clause.  P-92 supplies no transcribed reflection function on this type, so
the table is derived from variance plus constructor exhaustion rather than asserted. -/
def axialSwap : BlueBookP92.AxialDescriptor → BlueBookP92.AxialDescriptor
  | .Ra => .Sa
  | .Sa => .Ra

/-- Any fixed-point-free self-map of the two-symbol axial vocabulary is exactly `axialSwap`. -/
theorem axial_reflection_partner_forced
    (f : BlueBookP92.AxialDescriptor → BlueBookP92.AxialDescriptor)
    (variance : ∀ d, f d ≠ d) : f = axialSwap := by
  funext d
  cases d with
  | Ra =>
      cases hf : f .Ra with
      | Ra => exact absurd hf (variance .Ra)
      | Sa => rfl
  | Sa =>
      cases hf : f .Sa with
      | Ra => rfl
      | Sa => exact absurd hf (variance .Sa)

@[simp] theorem axialSwap_involutive (d : BlueBookP92.AxialDescriptor) :
    axialSwap (axialSwap d) = d := by
  cases d <;> rfl

@[simp] theorem axialSwap_changes (d : BlueBookP92.AxialDescriptor) :
    axialSwap d ≠ d := by
  cases d <;> decide

/-- The analogous forced table on the two-symbol planar vocabulary. -/
def planarSwap : BlueBookP92.PlanarDescriptor → BlueBookP92.PlanarDescriptor
  | .Rp => .Sp
  | .Sp => .Rp

/-- Any fixed-point-free self-map of the two-symbol planar vocabulary is exactly `planarSwap`. -/
theorem planar_reflection_partner_forced
    (f : BlueBookP92.PlanarDescriptor → BlueBookP92.PlanarDescriptor)
    (variance : ∀ d, f d ≠ d) : f = planarSwap := by
  funext d
  cases d with
  | Rp =>
      cases hf : f .Rp with
      | Rp => exact absurd hf (variance .Rp)
      | Sp => rfl
  | Sp =>
      cases hf : f .Sp with
      | Rp => rfl
      | Sp => exact absurd hf (variance .Sp)

@[simp] theorem planarSwap_involutive (d : BlueBookP92.PlanarDescriptor) :
    planarSwap (planarSwap d) = d := by
  cases d <;> rfl

@[simp] theorem planarSwap_changes (d : BlueBookP92.PlanarDescriptor) :
    planarSwap d ≠ d := by
  cases d <;> decide

/-- Partial translation of the axial fragment into the independent P-92 vocabulary. -/
def toP92Axial : Descriptor → Option BlueBookP92.AxialDescriptor
  | Ra => some .Ra
  | Sa => some .Sa
  | _ => none

/-- `Descriptor.mirror` realises the forced axial exchange. -/
theorem mirror_conforms_to_P92_axial (d : Descriptor)
    (s : BlueBookP92.AxialDescriptor)
    (h : toP92Axial d = some s) :
    toP92Axial (mirror d) = some (axialSwap s) := by
  cases d <;> cases s <;> simp [toP92Axial, mirror, axialSwap] at h ⊢

/-- Partial translation of the planar fragment into the independent P-92 vocabulary. -/
def toP92Planar : Descriptor → Option BlueBookP92.PlanarDescriptor
  | Rp => some .Rp
  | Sp => some .Sp
  | _ => none

/-- `Descriptor.mirror` realises the forced planar exchange. -/
theorem mirror_conforms_to_P92_planar (d : Descriptor)
    (s : BlueBookP92.PlanarDescriptor)
    (h : toP92Planar d = some s) :
    toP92Planar (mirror d) = some (planarSwap s) := by
  cases d <;> cases s <;> simp [toP92Planar, mirror, planarSwap] at h ⊢

/-- The two-symbol axial fragment of the declarative vocabulary. -/
def IsAxial : Descriptor → Prop
  | Ra | Sa => True
  | _ => False

/-- The two-symbol planar fragment of the declarative vocabulary. -/
def IsPlanar : Descriptor → Prop
  | Rp | Sp => True
  | _ => False

/-- Recognition form of the axial fragment. -/
theorem isAxial_iff (d : Descriptor) : IsAxial d ↔ d = Ra ∨ d = Sa := by
  cases d <;> simp [IsAxial]

/-- Recognition form of the planar fragment. -/
theorem isPlanar_iff (d : Descriptor) : IsPlanar d ↔ d = Rp ∨ d = Sp := by
  cases d <;> simp [IsPlanar]

/-- Closure in `{Ra, Sa}` plus variance forces `Ra ↦ Sa`. -/
theorem axial_component_forced_forward (f : Descriptor → Descriptor)
    (closure : ∀ d, IsAxial d → IsAxial (f d))
    (variance : ∀ d, IsAxial d → f d ≠ d) : f Ra = Sa := by
  rcases (isAxial_iff (f Ra)).1 (closure Ra (by simp [IsAxial])) with moved | moved
  · exact absurd moved (variance Ra (by simp [IsAxial]))
  · exact moved

/-- Closure in `{Ra, Sa}` plus variance forces `Sa ↦ Ra`. -/
theorem axial_component_forced_backward (f : Descriptor → Descriptor)
    (closure : ∀ d, IsAxial d → IsAxial (f d))
    (variance : ∀ d, IsAxial d → f d ≠ d) : f Sa = Ra := by
  rcases (isAxial_iff (f Sa)).1 (closure Sa (by simp [IsAxial])) with moved | moved
  · exact moved
  · exact absurd moved (variance Sa (by simp [IsAxial]))

/-- Closure in `{Rp, Sp}` plus variance forces `Rp ↦ Sp`. -/
theorem planar_component_forced_forward (f : Descriptor → Descriptor)
    (closure : ∀ d, IsPlanar d → IsPlanar (f d))
    (variance : ∀ d, IsPlanar d → f d ≠ d) : f Rp = Sp := by
  rcases (isPlanar_iff (f Rp)).1 (closure Rp (by simp [IsPlanar])) with moved | moved
  · exact absurd moved (variance Rp (by simp [IsPlanar]))
  · exact moved

/-- Closure in `{Rp, Sp}` plus variance forces `Sp ↦ Rp`. -/
theorem planar_component_forced_backward (f : Descriptor → Descriptor)
    (closure : ∀ d, IsPlanar d → IsPlanar (f d))
    (variance : ∀ d, IsPlanar d → f d ≠ d) : f Sp = Rp := by
  rcases (isPlanar_iff (f Sp)).1 (closure Sp (by simp [IsPlanar])) with moved | moved
  · exact moved
  · exact absurd moved (variance Sp (by simp [IsPlanar]))

/-! ## E/Z: exact table clause with the P-91 scope argument -/

/-- The capitalised symbols in the P-91.2.1.1 reflection clause: `R/S`, `M/P`, and the
general-nomenclature CIP symbols `Ra/Sa` and `Rp/Sp`.  `E`/`Z` are absent because P-91.2.1.2
classifies them as non-CIP stereodescriptors for diastereomorphic alkenes. -/
def P91CapitalizedCIPName : BlueBookP91.Descriptor → Prop
  | .capitalR | .capitalS | .capitalM | .capitalP
  | .axialR | .axialS | .planarR | .planarS => True
  | _ => False

/-- The exact fixed table recorded for `E` and `Z`. -/
theorem mirror_fixes_E_Z : mirror E = E ∧ mirror Z = Z := ⟨rfl, rfl⟩

/-- `E`/`Z` lie outside the P-91.2.1.1 capitalised-CIP reflection clause. -/
theorem E_Z_not_capitalizedCIPName :
    ¬ P91CapitalizedCIPName .capitalE ∧ ¬ P91CapitalizedCIPName .capitalZ :=
  ⟨fun h => h, fun h => h⟩

/-- Every capitalised reflection-variant constructor translates into the P-91 capitalised-CIP
scope.  `seqCis`/`seqTrans` are handled separately by P-92.6. -/
theorem capitalized_variant_translations_in_P91_scope :
    P91CapitalizedCIPName (toP91 R) ∧ P91CapitalizedCIPName (toP91 S) ∧
    P91CapitalizedCIPName (toP91 M) ∧ P91CapitalizedCIPName (toP91 P) ∧
    P91CapitalizedCIPName (toP91 Ra) ∧ P91CapitalizedCIPName (toP91 Sa) ∧
    P91CapitalizedCIPName (toP91 Rp) ∧ P91CapitalizedCIPName (toP91 Sp) := by
  simp [P91CapitalizedCIPName, toP91]

/-- P-91 states that `seqCis`/`seqTrans` describe enantiomorphic double bonds. -/
theorem seqCis_applies_enantiomorphicDoubleBond :
    BlueBookP91.DescriptorApplies (toP91 seqCis) .enantiomorphicDoubleBond :=
  trivial

/-- P-91 places `E`/`Z` with diastereomorphic two-ended unsaturation, not with enantiomorphic
double bonds. -/
theorem E_applies_diastereomorphic :
    BlueBookP91.DescriptorApplies (toP91 E) .diastereomorphicTwoEndedUnsaturation :=
  trivial

/-- The analogous P-91 applicability of `Z`. -/
theorem Z_applies_diastereomorphic :
    BlueBookP91.DescriptorApplies (toP91 Z) .diastereomorphicTwoEndedUnsaturation :=
  trivial

/-! ## The complete table and the invariant/variant classification -/

/-- Exact table of the source-faithful reflection action. -/
theorem mirror_table :
    mirror R = S ∧ mirror S = R ∧
    mirror r = r ∧ mirror s = s ∧
    mirror Ra = Sa ∧ mirror Sa = Ra ∧
    mirror Rp = Sp ∧ mirror Sp = Rp ∧
    mirror M = P ∧ mirror P = M ∧
    mirror E = E ∧ mirror Z = Z ∧
    mirror seqCis = seqTrans ∧ mirror seqTrans = seqCis := by
  decide

/-- The reflection-invariant descriptors are exactly the lower-case pseudoasymmetric symbols and
the diastereomorphic `E`/`Z` pair. -/
theorem mirror_fixed_iff (d : Descriptor) :
    mirror d = d ↔ d = r ∨ d = s ∨ d = E ∨ d = Z := by
  cases d <;> decide

/-! ## General source conformance and its uniqueness -/

/-- Source constraints on any candidate reflection action for the declarative descriptor
vocabulary.  Each field is either a result of an independent transcription (`P91` `ReflectionResult`,
`P92` `reflected`) or a clause whose partner is forced by the source vocabulary (axial/planar), or
the explicitly recorded exact `E`/`Z` clause. -/
structure SourceReflectionConformance (f : Descriptor → Descriptor) : Prop where
  /-- P-91's enumerated reflection results. -/
  p91 : ∀ d, P91Enumerated d →
    BlueBookP91.ReflectionResult (toP91 d) (toP91 (f d))
  /-- P-92's lower-case pseudoasymmetric reflection. -/
  pseudo : ∀ (d : Descriptor) (source : BlueBookP92.PseudoDescriptor),
    toP92Pseudo d = some source →
      toP92Pseudo (f d) =
        some (BlueBookP92.PseudoDescriptor.reflected source)
  /-- P-92's enantiomorphic double-bond reflection. -/
  sequence : ∀ (d : Descriptor)
      (s : BlueBookP92.EnantiomorphicDoubleBondDescriptor),
    toP92Sequence d = some s →
      toP92Sequence (f d) =
        some (BlueBookP92.EnantiomorphicDoubleBondDescriptor.reflected s)
  /-- An axial reflection action stays within the two-symbol axial vocabulary. -/
  axialClosure : ∀ d, IsAxial d → IsAxial (f d)
  /-- P-91.2.1.1: capitalised axial CIP descriptors are reflection-variant. -/
  axialVariance : ∀ d, IsAxial d → f d ≠ d
  /-- A planar reflection action stays within the two-symbol planar vocabulary. -/
  planarClosure : ∀ d, IsPlanar d → IsPlanar (f d)
  /-- P-91.2.1.1: capitalised planar CIP descriptors are reflection-variant. -/
  planarVariance : ∀ d, IsPlanar d → f d ≠ d
  /-- The documented exact `E`/`Z` clause (no independent source reflection operation exists). -/
  ezFixed : f E = E ∧ f Z = Z

/-- The corrected `Descriptor.mirror` satisfies every independent source constraint. -/
theorem mirror_sourceConformant : SourceReflectionConformance mirror where
  p91 := fun d enumerated => p91_reflection_conformance d enumerated
  pseudo := fun d source h => mirror_conforms_to_P92_pseudo d source h
  sequence := fun d s h => mirror_conforms_to_P92_sequence d s h
  axialClosure := by
    intro d axial
    cases d <;> simp [IsAxial, mirror] at axial ⊢
  axialVariance := by
    intro d axial
    cases d <;> simp [IsAxial, mirror] at axial ⊢
  planarClosure := by
    intro d planar
    cases d <;> simp [IsPlanar, mirror] at planar ⊢
  planarVariance := by
    intro d planar
    cases d <;> simp [IsPlanar, mirror] at planar ⊢
  ezFixed := mirror_fixes_E_Z

/-- The source constraints determine the reflection action uniquely.  In particular the
corrected table is not one arbitrary choice among several involutions. -/
theorem source_conformance_determines_mirror (f : Descriptor → Descriptor)
    (conformant : SourceReflectionConformance f) : f = mirror := by
  funext d
  cases d with
  | R =>
      exact toP91_injective
        (reflectionResult_partner_unique R (toP91 (f R))
          (conformant.p91 R (by simp [P91Enumerated])))
  | S =>
      exact toP91_injective
        (reflectionResult_partner_unique S (toP91 (f S))
          (conformant.p91 S (by simp [P91Enumerated])))
  | r =>
      exact toP91_injective
        (reflectionResult_partner_unique r (toP91 (f r))
          (conformant.p91 r (by simp [P91Enumerated])))
  | s =>
      exact toP91_injective
        (reflectionResult_partner_unique s (toP91 (f s))
          (conformant.p91 s (by simp [P91Enumerated])))
  | M =>
      exact toP91_injective
        (reflectionResult_partner_unique M (toP91 (f M))
          (conformant.p91 M (by simp [P91Enumerated])))
  | P =>
      exact toP91_injective
        (reflectionResult_partner_unique P (toP91 (f P))
          (conformant.p91 P (by simp [P91Enumerated])))
  | seqCis =>
      have step := conformant.sequence seqCis .seqCis rfl
      have moved : toP92Sequence (f seqCis) = some .seqTrans := by
        simpa [BlueBookP92.EnantiomorphicDoubleBondDescriptor.reflected] using step
      rcases (toP92Sequence_eq_some_iff (f seqCis) .seqTrans).1 moved with
        impossible | value
      · exact absurd impossible.2 (by decide)
      · exact value.1
  | seqTrans =>
      have step := conformant.sequence seqTrans .seqTrans rfl
      have moved : toP92Sequence (f seqTrans) = some .seqCis := by
        simpa [BlueBookP92.EnantiomorphicDoubleBondDescriptor.reflected] using step
      rcases (toP92Sequence_eq_some_iff (f seqTrans) .seqCis).1 moved with
        value | impossible
      · exact value.1
      · exact absurd impossible.2 (by decide)
  | Ra =>
      have forced : f Ra = Sa :=
        axial_component_forced_forward f conformant.axialClosure conformant.axialVariance
      simpa [mirror] using forced
  | Sa =>
      have forced : f Sa = Ra :=
        axial_component_forced_backward f conformant.axialClosure conformant.axialVariance
      simpa [mirror] using forced
  | Rp =>
      have forced : f Rp = Sp :=
        planar_component_forced_forward f conformant.planarClosure conformant.planarVariance
      simpa [mirror] using forced
  | Sp =>
      have forced : f Sp = Rp :=
        planar_component_forced_backward f conformant.planarClosure conformant.planarVariance
      simpa [mirror] using forced
  | E => simpa [mirror] using conformant.ezFixed.1
  | Z => simpa [mirror] using conformant.ezFixed.2

/-- A function is a source-faithful declarative reflection action exactly when it is
`Descriptor.mirror`. -/
theorem source_conformance_iff_eq_mirror (f : Descriptor → Descriptor) :
    SourceReflectionConformance f ↔ f = mirror :=
  ⟨source_conformance_determines_mirror f, by
    intro equal
    rw [equal]
    exact mirror_sourceConformant⟩

/-- The corrected operation is simultaneously involutive and source-conformant. -/
theorem involution_and_source_conformance_hold :
    (∀ d, mirror (mirror d) = d) ∧ SourceReflectionConformance mirror :=
  ⟨mirror_mirror, mirror_sourceConformant⟩

/-! ## Superseded table retained as a negative kernel guard -/

/-- The pre-repair reflection table.  This is **not** a source API and is used only to prove that
the old involution-based argument did not establish source fidelity. -/
def legacyMirror : Descriptor → Descriptor
  | R => S
  | S => R
  | r => s
  | s => r
  | Ra => Sa
  | Sa => Ra
  | Rp => Sp
  | Sp => Rp
  | M => P
  | P => M
  | E => E
  | Z => Z
  | seqCis => seqCis
  | seqTrans => seqTrans

/-- The superseded table was still an involution, which is why the old involution proof passed. -/
theorem legacyMirror_involutive (d : Descriptor) :
    legacyMirror (legacyMirror d) = d := by
  cases d <;> rfl

/-- P-91's partial relation rejects the former lower-case swap. -/
theorem p91_rejects_legacy_lowercase :
    ¬ BlueBookP91.ReflectionResult .lowercaseR .lowercaseS :=
  fun h => h

/-- The superseded table contradicts P-91 at `r`. -/
theorem legacyMirror_violates_P91 :
    ¬ BlueBookP91.ReflectionResult (toP91 r) (toP91 (legacyMirror r)) := by
  simpa [toP91, legacyMirror] using p91_rejects_legacy_lowercase

/-- The superseded table fails the independent source constraints. -/
theorem legacyMirror_not_source_conformant :
    ¬ SourceReflectionConformance legacyMirror := by
  intro conformant
  exact legacyMirror_violates_P91 (conformant.p91 r (by simp [P91Enumerated]))

/-- Involution alone is *not* source fidelity: the superseded table is involutive and yet fails
P-91. -/
theorem involution_alone_does_not_imply_source_conformance :
    (∀ d, legacyMirror (legacyMirror d) = d) ∧
      ¬ SourceReflectionConformance legacyMirror :=
  ⟨legacyMirror_involutive, legacyMirror_not_source_conformant⟩

/-- The corrected table differs from the superseded one exactly at the four repaired branches. -/
theorem legacyMirror_disagrees_only_on_repaired_branches :
    mirror r ≠ legacyMirror r ∧ mirror s ≠ legacyMirror s ∧
    mirror seqCis ≠ legacyMirror seqCis ∧
    mirror seqTrans ≠ legacyMirror seqTrans ∧
    mirror R = legacyMirror R ∧ mirror S = legacyMirror S ∧
    mirror Ra = legacyMirror Ra ∧ mirror Sa = legacyMirror Sa ∧
    mirror Rp = legacyMirror Rp ∧ mirror Sp = legacyMirror Sp ∧
    mirror M = legacyMirror M ∧ mirror P = legacyMirror P ∧
    mirror E = legacyMirror E ∧ mirror Z = legacyMirror Z := by
  simp [mirror, legacyMirror]

end Descriptor

/-! ## Rule-3 geometry versus Rule-5 sequence descriptors

P-92.6 distinguishes lower-case sequence *geometry* observations from the capital final
stereodescriptors `seqCis`/`seqTrans`.  `OfficialRule3Geometry.seqcis`/`seqtrans` are geometric
classes compared under Rule 3; mirroring a spatial arrangement does not exchange same-side with
opposite-side, so the Rule-3 reflection action is the identity.  The capital final descriptors are
reflection-variant.  The theorems below preserve that distinction and prove the two vocabularies
cannot be identified equivariantly. -/

/-- Reflection acts trivially on a Rule-3 geometric class. -/
def rule3GeometryReflection : OfficialRule3Geometry → OfficialRule3Geometry :=
  fun geometry => geometry

@[simp] theorem rule3GeometryReflection_fixed (geometry : OfficialRule3Geometry) :
    rule3GeometryReflection geometry = geometry := rfl

/-- The Rule-3 reflection action is the identity on all three geometry classes. -/
theorem rule3_geometry_reflection_identity :
    ∀ geometry : OfficialRule3Geometry, rule3GeometryReflection geometry = geometry :=
  fun _ => rfl

/-- Rule-3 geometry is reflection-invariant, while the P-92.6 enantiomorphic double-bond
descriptors are reflection-variant. -/
theorem rule3_geometry_invariant_but_rule5_sequence_variant :
    (∀ geometry : OfficialRule3Geometry,
      rule3GeometryReflection geometry = geometry) ∧
    (∀ descriptor : BlueBookP92.EnantiomorphicDoubleBondDescriptor,
      BlueBookP92.EnantiomorphicDoubleBondDescriptor.reflected descriptor ≠ descriptor) :=
  ⟨rule3_geometry_reflection_identity,
    BlueBookP92.enantiomorphicDoubleBondDescriptor_reflection_changes⟩

/-- The declarative capital sequence descriptors change under reflection, unlike the lower-case
Rule-3 geometry classes. -/
theorem rule5_capital_sequence_changes :
    Descriptor.mirror Descriptor.seqCis = Descriptor.seqTrans ∧
    Descriptor.mirror Descriptor.seqTrans = Descriptor.seqCis ∧
    Descriptor.mirror Descriptor.seqCis ≠ Descriptor.seqCis ∧
    Descriptor.mirror Descriptor.seqTrans ≠ Descriptor.seqTrans := by
  decide

/-- The lower-case Rule-3 classes are fixed while the capital Rule-5 final descriptors exchange. -/
theorem rule3_lowercase_geometry_not_rule5_descriptor :
    rule3GeometryReflection .seqcis = .seqcis ∧
    rule3GeometryReflection .seqtrans = .seqtrans ∧
    Descriptor.mirror Descriptor.seqCis = Descriptor.seqTrans ∧
    Descriptor.mirror Descriptor.seqTrans = Descriptor.seqCis := by
  simp [rule3GeometryReflection, Descriptor.mirror]

/-- No injective translation of the two capital Rule-5 sequence descriptors into Rule-3 geometry
can preserve both reflection actions: Rule-5 exchange and Rule-3 invariance would force the two
distinct final descriptors to have the same image. -/
theorem no_reflection_equivariant_injection_from_rule5_sequence_to_rule3_geometry
    (embed : DeclarativeCIP.Descriptor → OfficialRule3Geometry)
    (distinct : embed Descriptor.seqCis ≠ embed Descriptor.seqTrans)
    (equivariant : ∀ d : DeclarativeCIP.Descriptor,
      d = Descriptor.seqCis ∨ d = Descriptor.seqTrans →
        embed (Descriptor.mirror d) = rule3GeometryReflection (embed d)) :
    False := by
  have moved := equivariant Descriptor.seqCis (Or.inl rfl)
  simp [Descriptor.mirror, rule3GeometryReflection] at moved
  exact distinct moved.symm

/-- The corrected mirror is not the identity, so it cannot be confused with the Rule-3 geometry
action. -/
theorem descriptorMirror_ne_identity : Descriptor.mirror ≠ id := by
  intro equal
  have applied := congrFun equal Descriptor.seqCis
  simp [Descriptor.mirror] at applied

end DeclarativeCIP
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards for the load-bearing results -/

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.toP91_injective
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.p91_reflection_conformance
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.reflectionResult_partner_unique
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.mirror_conforms_to_P92_pseudo
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.p92_pseudo_reflection_invariant
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.toP92Sequence_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.mirror_conforms_to_P92_sequence
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.p92_sequence_reflection_changes
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.axial_reflection_partner_forced
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.planar_reflection_partner_forced
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.axial_component_forced_forward
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.axial_component_forced_backward
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.planar_component_forced_forward
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.planar_component_forced_backward
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.mirror_conforms_to_P92_axial
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.mirror_conforms_to_P92_planar
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.mirror_fixes_E_Z
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.E_Z_not_capitalizedCIPName
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.capitalized_variant_translations_in_P91_scope
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.mirror_table
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.mirror_fixed_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.mirror_sourceConformant
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.source_conformance_determines_mirror
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.source_conformance_iff_eq_mirror
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.involution_and_source_conformance_hold
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.legacyMirror_involutive
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.legacyMirror_violates_P91
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.legacyMirror_not_source_conformant
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.involution_alone_does_not_imply_source_conformance
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Descriptor.legacyMirror_disagrees_only_on_repaired_branches
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rule3_geometry_reflection_identity
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rule3_geometry_invariant_but_rule5_sequence_variant
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rule5_capital_sequence_changes
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rule3_lowercase_geometry_not_rule5_descriptor
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.no_reflection_equivariant_injection_from_rule5_sequence_to_rule3_geometry
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.descriptorMirror_ne_identity
