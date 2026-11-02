import TetraStereo.OneCenter.Basic

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent IUPAC P-91 stereodescriptor and naming semantics

This module transcribes the rule-shaped content of P-91 independently of the production analyzer.
It deliberately separates four matters which prose can otherwise blur:

* the configuration to which a descriptor may apply;
* whether a descriptor is preferred in a PIN or admitted only in general nomenclature;
* when a double-bond descriptor is required or recommended to be omitted; and
* where an already determined descriptor is placed in a name.

P-91.2.1.2.2 only lists natural-product descriptor families and delegates their chemical meanings
to P-101--P-104 (with `ambo` also treated in P-93).  The final section records those delegations as
open authority obligations rather than inventing definitions from the short P-91 list.
-/

namespace BlueBookP91

/-! ## P-91.1: graphical configuration -/

inductive DepictionBondStyle where
  | plain
  | solidWedge
  | hashedWedge
  | constantAmplitudeWavy
  deriving DecidableEq, Repr

inductive DrawingDepth where
  | approximatelyInPlane
  | abovePlane
  | belowPlane
  | unknown
  deriving DecidableEq, Repr

/-- P-91.1 interprets a stereowedge from its narrow endpoint. -/
structure DirectedDepictionBond (Atom : Type*) where
  narrowEndpoint : Atom
  otherEndpoint : Atom
  style : DepictionBondStyle

def representedDepth {Atom : Type*} (bond : DirectedDepictionBond Atom) : DrawingDepth :=
  match bond.style with
  | .plain => .approximatelyInPlane
  | .solidWedge => .abovePlane
  | .hashedWedge => .belowPlane
  | .constantAmplitudeWavy => .unknown

@[simp] theorem solidWedge_represents_above {Atom : Type*} (first second : Atom) :
    representedDepth
      ({ narrowEndpoint := first, otherEndpoint := second,
         style := .solidWedge } : DirectedDepictionBond Atom) = .abovePlane :=
  rfl

@[simp] theorem hashedWedge_represents_below {Atom : Type*} (first second : Atom) :
    representedDepth
      ({ narrowEndpoint := first, otherEndpoint := second,
         style := .hashedWedge } : DirectedDepictionBond Atom) = .belowPlane :=
  rfl

@[simp] theorem wavy_represents_unknown {Atom : Type*} (first second : Atom) :
    representedDepth
      ({ narrowEndpoint := first, otherEndpoint := second,
         style := .constantAmplitudeWavy } : DirectedDepictionBond Atom) = .unknown :=
  rfl

/-! ## P-91.2.1: descriptor vocabulary and applicability -/

/-- Descriptor tokens named in P-91.  Scope qualifiers (`rel` and `rac`) are kept in a separate
type because they do not denote one local stereogenic unit. -/
inductive Descriptor where
  | capitalR | capitalS
  | lowercaseR | lowercaseS
  | capitalM | capitalP
  | lowercaseM | lowercaseP
  | seqCis | seqTrans
  | axialR | axialS
  | planarR | planarS
  | pseudoAxialR | pseudoAxialS
  | pseudoPlanarR | pseudoPlanarS
  | capitalE | capitalZ
  | capitalA | capitalC
  | cis | trans
  | rctR | rctC | rctT
  | endo | exo | syn | anti
  deriving DecidableEq, Repr

namespace Descriptor

def symbol : Descriptor → String
  | .capitalR => "R" | .capitalS => "S"
  | .lowercaseR => "r" | .lowercaseS => "s"
  | .capitalM => "M" | .capitalP => "P"
  | .lowercaseM => "m" | .lowercaseP => "p"
  | .seqCis => "seqCis" | .seqTrans => "seqTrans"
  | .axialR => "Ra" | .axialS => "Sa"
  | .planarR => "Rp" | .planarS => "Sp"
  | .pseudoAxialR => "ra" | .pseudoAxialS => "sa"
  | .pseudoPlanarR => "rp" | .pseudoPlanarS => "sp"
  | .capitalE => "E" | .capitalZ => "Z"
  | .capitalA => "A" | .capitalC => "C"
  | .cis => "cis" | .trans => "trans"
  | .rctR => "r" | .rctC => "c" | .rctT => "t"
  | .endo => "endo" | .exo => "exo" | .syn => "syn" | .anti => "anti"

/-- The ten descriptors that P-91.2.1.1 itself calls preferred CIP descriptors. -/
def IsPreferredCIP : Descriptor → Prop
  | .capitalR | .capitalS | .lowercaseR | .lowercaseS
  | .capitalM | .capitalP | .lowercaseM | .lowercaseP
  | .seqCis | .seqTrans => True
  | _ => False

/-- Descriptor pairs explicitly recommended for general nomenclature rather than as the preferred
P-91.2.1.1 vocabulary. -/
def IsGeneralCIPForm : Descriptor → Prop
  | .axialR | .axialS | .planarR | .planarS
  | .pseudoAxialR | .pseudoAxialS | .pseudoPlanarR | .pseudoPlanarS => True
  | _ => False

end Descriptor

inductive ScopeQualifier where
  | relative
  | racemic
  deriving DecidableEq, Repr

inductive StereogenicUnitKind where
  | quadriligantChiralityCenter
  | pseudoasymmetricCenter
  | axialHelicityEntity
  | planarHelicityEntity
  | pseudoasymmetricAxialHelicityEntity
  | pseudoasymmetricPlanarHelicityEntity
  | enantiomorphicDoubleBond
  | chiralityAxis
  | chiralityPlane
  | pseudoasymmetricAxis
  | pseudoasymmetricPlane
  | diastereomorphicTwoEndedUnsaturation
  | pentaligantCenter
  | hexaligantCenter
  deriving DecidableEq, Repr

/-- Applicability stated in P-91.2.1.1 and P-91.2.1.2.1.  This is not a perception function: the
caller must independently establish the kind of stereogenic unit. -/
def DescriptorApplies : Descriptor → StereogenicUnitKind → Prop
  | .capitalR, .quadriligantChiralityCenter
  | .capitalS, .quadriligantChiralityCenter
  | .lowercaseR, .pseudoasymmetricCenter
  | .lowercaseS, .pseudoasymmetricCenter
  | .capitalM, .axialHelicityEntity
  | .capitalP, .axialHelicityEntity
  | .capitalM, .planarHelicityEntity
  | .capitalP, .planarHelicityEntity
  | .lowercaseM, .pseudoasymmetricAxialHelicityEntity
  | .lowercaseP, .pseudoasymmetricAxialHelicityEntity
  | .lowercaseM, .pseudoasymmetricPlanarHelicityEntity
  | .lowercaseP, .pseudoasymmetricPlanarHelicityEntity
  | .seqCis, .enantiomorphicDoubleBond
  | .seqTrans, .enantiomorphicDoubleBond
  | .axialR, .chiralityAxis
  | .axialS, .chiralityAxis
  | .planarR, .chiralityPlane
  | .planarS, .chiralityPlane
  | .pseudoAxialR, .pseudoasymmetricAxis
  | .pseudoAxialS, .pseudoasymmetricAxis
  | .pseudoPlanarR, .pseudoasymmetricPlane
  | .pseudoPlanarS, .pseudoasymmetricPlane
  | .capitalE, .diastereomorphicTwoEndedUnsaturation
  | .capitalZ, .diastereomorphicTwoEndedUnsaturation
  | .capitalA, .pentaligantCenter
  | .capitalC, .pentaligantCenter
  | .capitalA, .hexaligantCenter
  | .capitalC, .hexaligantCenter => True
  | _, _ => False

theorem preferredCIP_has_stated_applicability (descriptor : Descriptor)
    (preferred : descriptor.IsPreferredCIP) :
    ∃ kind, DescriptorApplies descriptor kind := by
  cases descriptor with
  | capitalR => exact ⟨.quadriligantChiralityCenter, trivial⟩
  | capitalS => exact ⟨.quadriligantChiralityCenter, trivial⟩
  | lowercaseR => exact ⟨.pseudoasymmetricCenter, trivial⟩
  | lowercaseS => exact ⟨.pseudoasymmetricCenter, trivial⟩
  | capitalM => exact ⟨.axialHelicityEntity, trivial⟩
  | capitalP => exact ⟨.axialHelicityEntity, trivial⟩
  | lowercaseM => exact ⟨.pseudoasymmetricAxialHelicityEntity, trivial⟩
  | lowercaseP => exact ⟨.pseudoasymmetricAxialHelicityEntity, trivial⟩
  | seqCis => exact ⟨.enantiomorphicDoubleBond, trivial⟩
  | seqTrans => exact ⟨.enantiomorphicDoubleBond, trivial⟩
  | axialR | axialS | planarR | planarS | pseudoAxialR | pseudoAxialS
  | pseudoPlanarR | pseudoPlanarS | capitalE | capitalZ | capitalA | capitalC
  | cis | trans | rctR | rctC | rctT | endo | exo | syn | anti =>
      simp [Descriptor.IsPreferredCIP] at preferred

/-! ## Reflection and uncertainty -/

/-- P-91 states these reflection results explicitly.  It does not license deriving the reflection
behaviour of every other token merely from typography, so this relation is intentionally partial. -/
def ReflectionResult : Descriptor → Descriptor → Prop
  | .capitalR, .capitalS | .capitalS, .capitalR
  | .capitalM, .capitalP | .capitalP, .capitalM
  | .lowercaseR, .lowercaseR | .lowercaseS, .lowercaseS
  | .lowercaseM, .lowercaseM | .lowercaseP, .lowercaseP => True
  | _, _ => False

theorem capital_descriptors_change_under_stated_reflection
    (descriptor reflected : Descriptor)
    (capital : descriptor = .capitalR ∨ descriptor = .capitalS ∨
      descriptor = .capitalM ∨ descriptor = .capitalP)
    (result : ReflectionResult descriptor reflected) :
    reflected ≠ descriptor := by
  rcases capital with rfl | rfl | rfl | rfl <;>
    cases reflected <;> simp_all [ReflectionResult]

theorem lowercase_descriptors_are_invariant_under_stated_reflection
    (descriptor : Descriptor)
    (lowercase : descriptor = .lowercaseR ∨ descriptor = .lowercaseS ∨
      descriptor = .lowercaseM ∨ descriptor = .lowercaseP) :
    ReflectionResult descriptor descriptor := by
  rcases lowercase with rfl | rfl | rfl | rfl <;> trivial

inductive UnknownConfigurationSymbol where
  | lowercaseXi
  | capitalXi
  deriving DecidableEq, Repr

/-- The examples explicitly enumerated in P-91 for replacement by `ξ` and `Ξ`.  The source says
“such as”, so this relation does not falsely assert that the examples exhaust every future or
delegated descriptor family. -/
def ExplicitUnknownReplacementExample :
    UnknownConfigurationSymbol → Descriptor → Prop
  | .lowercaseXi, .lowercaseR | .lowercaseXi, .lowercaseS
  | .lowercaseXi, .lowercaseM | .lowercaseXi, .lowercaseP
  | .capitalXi, .capitalR | .capitalXi, .capitalS
  | .capitalXi, .capitalM | .capitalXi, .capitalP
  | .capitalXi, .capitalE | .capitalXi, .capitalZ
  | .capitalXi, .seqCis | .capitalXi, .seqTrans => True
  | _, _ => False

theorem explicit_unknown_replacement_classes_disjoint
    (descriptor : Descriptor) :
    ¬(ExplicitUnknownReplacementExample .lowercaseXi descriptor ∧
      ExplicitUnknownReplacementExample .capitalXi descriptor) := by
  cases descriptor <;> simp [ExplicitUnknownReplacementExample]

/-! ## P-91.2.2: omission of double-bond descriptors -/

inductive RingSystemKind where
  | simpleAlicyclic
  | vonBaeyer
  | spiro
  | fused
  | cyclophane
  | identicalRingAssembly
  deriving DecidableEq, Repr

structure DoubleBondNamingContext where
  system : RingSystemKind
  ringSize : ℕ
  doubleBondCount : ℕ
  everyDoubleBondConfigurationFixed : Prop

inductive DescriptorDisposition where
  | omitRecommended
  | required
  deriving DecidableEq, Repr

/-- Exact P-91.2.2 decision relation.  It is relational because chemically inadmissible or
otherwise unmentioned combinations should not receive a fabricated answer. -/
def DoubleBondDescriptorDisposition
    (context : DoubleBondNamingContext) : DescriptorDisposition → Prop
  | .omitRecommended =>
      context.doubleBondCount > 0 ∧
      ((context.system = .simpleAlicyclic ∧
          ((3 ≤ context.ringSize ∧ context.ringSize ≤ 7 ∧
              context.everyDoubleBondConfigurationFixed) ∨
            (context.ringSize = 8 ∧ 2 ≤ context.doubleBondCount ∧
              context.doubleBondCount ≤ 4))) ∨
        context.system = .vonBaeyer ∨ context.system = .spiro ∨
        context.system = .fused ∨ context.system = .cyclophane ∨
        context.system = .identicalRingAssembly)
  | .required =>
      context.system = .simpleAlicyclic ∧ context.doubleBondCount > 0 ∧
      ((context.ringSize = 8 ∧ context.doubleBondCount = 1) ∨
        9 ≤ context.ringSize)

theorem simple_three_through_seven_fixed_omit
    (ringSize doubleBondCount : ℕ)
    (nonzero : doubleBondCount > 0)
    (lower : 3 ≤ ringSize) (upper : ringSize ≤ 7) :
    DoubleBondDescriptorDisposition
      { system := .simpleAlicyclic
        ringSize := ringSize
        doubleBondCount := doubleBondCount
        everyDoubleBondConfigurationFixed := True }
      .omitRecommended := by
  simp [DoubleBondDescriptorDisposition, nonzero, lower, upper]

theorem simple_eight_monoene_requires :
    DoubleBondDescriptorDisposition
      { system := .simpleAlicyclic
        ringSize := 8
        doubleBondCount := 1
        everyDoubleBondConfigurationFixed := False }
      .required := by
  simp [DoubleBondDescriptorDisposition]

theorem simple_eight_tetraene_omits :
    DoubleBondDescriptorDisposition
      { system := .simpleAlicyclic
        ringSize := 8
        doubleBondCount := 4
        everyDoubleBondConfigurationFixed := True }
      .omitRecommended := by
  simp [DoubleBondDescriptorDisposition]

theorem simple_nine_or_larger_requires (ringSize doubleBondCount : ℕ)
    (size : 9 ≤ ringSize) (nonzero : doubleBondCount > 0) :
    DoubleBondDescriptorDisposition
      { system := .simpleAlicyclic
        ringSize := ringSize
        doubleBondCount := doubleBondCount
        everyDoubleBondConfigurationFixed := False }
      .required := by
  simp [DoubleBondDescriptorDisposition, size, nonzero]

theorem omission_and_requirement_are_disjoint
    (context : DoubleBondNamingContext) :
    ¬(DoubleBondDescriptorDisposition context .omitRecommended ∧
      DoubleBondDescriptorDisposition context .required) := by
  rintro ⟨omission, requirement⟩
  rcases requirement with ⟨simpleSystem, _, eightMono | nineOrLarger⟩
  · have omissionSimple :
        context.doubleBondCount > 0 ∧
          ((3 ≤ context.ringSize ∧ context.ringSize ≤ 7 ∧
              context.everyDoubleBondConfigurationFixed) ∨
            (context.ringSize = 8 ∧ 2 ≤ context.doubleBondCount ∧
              context.doubleBondCount ≤ 4)) := by
      simpa [DoubleBondDescriptorDisposition, simpleSystem] using omission
    rcases eightMono with ⟨ringEight, oneBond⟩
    rcases omissionSimple.2 with smallFixed | eightPolyene
    · omega
    · omega
  · have omissionSimple :
        context.doubleBondCount > 0 ∧
          ((3 ≤ context.ringSize ∧ context.ringSize ≤ 7 ∧
              context.everyDoubleBondConfigurationFixed) ∨
            (context.ringSize = 8 ∧ 2 ≤ context.doubleBondCount ∧
              context.doubleBondCount ≤ 4)) := by
      simpa [DoubleBondDescriptorDisposition, simpleSystem] using omission
    rcases omissionSimple.2 with smallFixed | eightPolyene
    · omega
    · omega

/-! ## P-91.3: attachment to a pre-existing name and numbering -/

inductive NameTarget (Prefix : Type*) where
  | parent
  | substituent (component : Prefix)
  deriving DecidableEq, Repr

inductive CitationPosition (Prefix : Type*) where
  | frontOfCompleteName
  | frontOfPrefix (component : Prefix)
  deriving DecidableEq, Repr

structure DescriptorCitation (Locant Prefix : Type*) where
  descriptor : Descriptor
  locant : Option Locant
  target : NameTarget Prefix
  position : CitationPosition Prefix
  parenthesizedAndHyphenated : Bool
  deriving Repr

def CorrectCitationPlacement {Locant Prefix : Type*}
    (citation : DescriptorCitation Locant Prefix) : Prop :=
  match citation.target, citation.position with
  | .parent, .frontOfCompleteName => citation.parenthesizedAndHyphenated = true
  | .substituent targetPrefix, .frontOfPrefix actualPrefix =>
      targetPrefix = actualPrefix
  | _, _ => False

/-- The stereodescriptor layer is an annotation of a name and numbering constructed first. -/
structure AnnotatedName (BaseName Numbering Locant Prefix : Type*) where
  baseName : BaseName
  numbering : Numbering
  citations : List (DescriptorCitation Locant Prefix)

def AnnotatedName.withCitations {BaseName Numbering Locant Prefix : Type*}
    (name : AnnotatedName BaseName Numbering Locant Prefix)
    (citations : List (DescriptorCitation Locant Prefix)) :
    AnnotatedName BaseName Numbering Locant Prefix :=
  { name with citations := citations }

@[simp] theorem adding_descriptors_does_not_change_base_name
    {BaseName Numbering Locant Prefix : Type*}
    (name : AnnotatedName BaseName Numbering Locant Prefix)
    (citations : List (DescriptorCitation Locant Prefix)) :
    (name.withCitations citations).baseName = name.baseName :=
  rfl

@[simp] theorem adding_descriptors_does_not_change_numbering
    {BaseName Numbering Locant Prefix : Type*}
    (name : AnnotatedName BaseName Numbering Locant Prefix)
    (citations : List (DescriptorCitation Locant Prefix)) :
    (name.withCitations citations).numbering = name.numbering :=
  rfl

structure LocatedDescriptorCitation (Locant Prefix : Type*) where
  descriptor : Descriptor
  locant : Locant
  target : NameTarget Prefix
  deriving Repr

/-- P-91.3 requires increasing locant order within a multiple-descriptor group. -/
def InIncreasingLocantOrder {Locant Prefix : Type*} [LT Locant]
    (citations : List (LocatedDescriptorCitation Locant Prefix)) : Prop :=
  citations.Pairwise fun first second => first.locant < second.locant

theorem two_citations_in_increasing_order_iff
    {Locant Prefix : Type*} [LT Locant]
    (first second : LocatedDescriptorCitation Locant Prefix) :
    InIncreasingLocantOrder [first, second] ↔ first.locant < second.locant := by
  simp [InIncreasingLocantOrder]

/-- P-91/P-92 coverage condition: every perceived stereogenic unit either has a citation or has a
P-91.2.2 omission justification. -/
def EveryUnitSpecifiedUnlessOmitted {Unit : Type*}
    (units cited permissiblyOmitted : List Unit) : Prop :=
  ∀ unit ∈ units, unit ∈ cited ∨ unit ∈ permissiblyOmitted

/-! ## P-91.2.1.2.2: explicit cross-chapter authority obligations -/

inductive NaturalProductDescriptorFamily where
  | dAndL
  | carbohydrateConfigurationalStem
  | alphaBeta
  | carotenoidCisTransAndAll
  | meso
  | ambo
  deriving DecidableEq, Repr

inductive DelegatedAuthoritySection where
  | p101
  | p101_6
  | p102
  | p102_5_6_5_2
  | p102_5_6_6_5
  | p103
  | p103_3_4
  | p104
  | p93_1_4
  deriving DecidableEq, Repr

/-- This relation is what P-91 actually establishes for natural-product descriptors: which later
authority defines or applies the named family.  It intentionally does not define their chemistry. -/
def DelegatedTo : NaturalProductDescriptorFamily → DelegatedAuthoritySection → Prop
  | .dAndL, .p102 | .dAndL, .p103 | .dAndL, .p104
  | .carbohydrateConfigurationalStem, .p102
  | .alphaBeta, .p101
  | .carotenoidCisTransAndAll, .p101_6
  | .meso, .p102_5_6_5_2 | .meso, .p102_5_6_6_5
  | .ambo, .p93_1_4 | .ambo, .p103_3_4 => True
  | _, _ => False

def allNaturalProductFamilies : List NaturalProductDescriptorFamily :=
  [ .dAndL
  , .carbohydrateConfigurationalStem
  , .alphaBeta
  , .carotenoidCisTransAndAll
  , .meso
  , .ambo
  ]

@[simp] theorem every_natural_product_family_is_delegated
    (family : NaturalProductDescriptorFamily) :
    ∃ authority, DelegatedTo family authority := by
  cases family with
  | dAndL => exact ⟨.p102, trivial⟩
  | carbohydrateConfigurationalStem => exact ⟨.p102, trivial⟩
  | alphaBeta => exact ⟨.p101, trivial⟩
  | carotenoidCisTransAndAll => exact ⟨.p101_6, trivial⟩
  | meso => exact ⟨.p102_5_6_5_2, trivial⟩
  | ambo => exact ⟨.p93_1_4, trivial⟩

@[simp] theorem natural_product_family_list_exhaustive
    (family : NaturalProductDescriptorFamily) :
    family ∈ allNaturalProductFamilies := by
  cases family <;> simp [allNaturalProductFamilies]

theorem natural_product_family_list_nodup : allNaturalProductFamilies.Nodup := by
  decide

end BlueBookP91

end TetraStereo.OneCenter
