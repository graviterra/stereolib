import TetraStereo.OneCenter.CIPRules

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

section

/-!
  Official IUPAC CIP sequence-rule system.

  This module names the official rule slots from IUPAC Blue Book P-92 and gives
  compile-checked primitive comparators for the stereochemical rule layers that are not simple
  atomic-number or isotope comparisons.  It also wires those descriptor-rich rules into an
  optional ligand-context comparator: the graph key handles Rules 1 and 2, and Rules 3, 4a, 4b,
  4c, and 5 fire in official order when the graph key ties.
-/

/-- Official IUPAC CIP sequence-rule/subrule slots, in evaluation order. -/
inductive OfficialCIPSequenceRule where
  | rule1aAtomicNumber
  | rule1bDuplicateNodeProximity
  | rule2AtomicMass
  | rule3DoubleBondGeometry
  | rule4aStereogenicUnitKind
  | rule4bLikeUnlikeDescriptorPairs
  | rule4cPseudoasymmetricDescriptor
  | rule5EnantiomorphicDescriptor
  deriving DecidableEq, Repr

namespace OfficialCIPSequenceRule

/-- Numeric rank of each official sequence rule; lower ranks are consulted first. -/
def rank : OfficialCIPSequenceRule → ℕ
  | rule1aAtomicNumber => 0
  | rule1bDuplicateNodeProximity => 1
  | rule2AtomicMass => 2
  | rule3DoubleBondGeometry => 3
  | rule4aStereogenicUnitKind => 4
  | rule4bLikeUnlikeDescriptorPairs => 5
  | rule4cPseudoasymmetricDescriptor => 6
  | rule5EnantiomorphicDescriptor => 7

/-- The full official sequence-rule order, as a data object. -/
def all : List OfficialCIPSequenceRule :=
  [ rule1aAtomicNumber
  , rule1bDuplicateNodeProximity
  , rule2AtomicMass
  , rule3DoubleBondGeometry
  , rule4aStereogenicUnitKind
  , rule4bLikeUnlikeDescriptorPairs
  , rule4cPseudoasymmetricDescriptor
  , rule5EnantiomorphicDescriptor
  ]

/-- Short Blue Book section label for each official rule slot. -/
def blueBookSection : OfficialCIPSequenceRule → String
  | rule1aAtomicNumber => "P-92.2.1"
  | rule1bDuplicateNodeProximity => "P-92.2.2"
  | rule2AtomicMass => "P-92.3"
  | rule3DoubleBondGeometry => "P-92.4"
  | rule4aStereogenicUnitKind => "P-92.5.1"
  | rule4bLikeUnlikeDescriptorPairs => "P-92.5.2"
  | rule4cPseudoasymmetricDescriptor => "P-92.5.3"
  | rule5EnantiomorphicDescriptor => "P-92.6"

/-- Rule-order relation: `a` is consulted before `b`. -/
def Before (a b : OfficialCIPSequenceRule) : Prop :=
  a.rank < b.rank

@[simp] theorem length_all :
    all.length = 8 :=
  rfl

@[simp] theorem mem_all (rule : OfficialCIPSequenceRule) :
    rule ∈ all := by
  cases rule <;> simp [all]

theorem all_nodup :
    all.Nodup := by
  decide

theorem before_trans {a b c : OfficialCIPSequenceRule}
    (hab : a.Before b) (hbc : b.Before c) :
    a.Before c :=
  Nat.lt_trans hab hbc

@[simp] theorem rule1a_before_rule1b :
    rule1aAtomicNumber.Before rule1bDuplicateNodeProximity := by
  simp [Before, rank]

@[simp] theorem rule1b_before_rule2 :
    rule1bDuplicateNodeProximity.Before rule2AtomicMass := by
  simp [Before, rank]

@[simp] theorem rule2_before_rule3 :
    rule2AtomicMass.Before rule3DoubleBondGeometry := by
  simp [Before, rank]

@[simp] theorem rule3_before_rule4a :
    rule3DoubleBondGeometry.Before rule4aStereogenicUnitKind := by
  simp [Before, rank]

@[simp] theorem rule4a_before_rule4b :
    rule4aStereogenicUnitKind.Before rule4bLikeUnlikeDescriptorPairs := by
  simp [Before, rank]

@[simp] theorem rule4b_before_rule4c :
    rule4bLikeUnlikeDescriptorPairs.Before rule4cPseudoasymmetricDescriptor := by
  simp [Before, rank]

@[simp] theorem rule4c_before_rule5 :
    rule4cPseudoasymmetricDescriptor.Before rule5EnantiomorphicDescriptor := by
  simp [Before, rank]

end OfficialCIPSequenceRule

/-! ### Official descriptor-rule primitive domains -/

/-- Rule 3 geometry classes for double-bond or cumulene sequence descriptors. -/
inductive OfficialRule3Geometry where
  | seqcis
  | seqtrans
  | nonstereogenic
  deriving DecidableEq, Repr

namespace OfficialRule3Geometry

/-- Rule 3 priority: `seqcis` precedes `seqtrans`, both preceding a non-stereogenic unit. -/
def priority : OfficialRule3Geometry → ℕ
  | seqcis => 2
  | seqtrans => 1
  | nonstereogenic => 0

/-- Rule 3 comparison.  `Ordering.gt` means the left descriptor has higher priority. -/
def compare (left right : OfficialRule3Geometry) : Ordering :=
  CIPRuleEngine.comparePriorityNat left.priority right.priority

@[simp] theorem compare_seqcis_seqtrans :
    compare seqcis seqtrans = Ordering.gt :=
  rfl

@[simp] theorem compare_seqtrans_nonstereogenic :
    compare seqtrans nonstereogenic = Ordering.gt :=
  rfl

@[simp] theorem compare_self (descriptor : OfficialRule3Geometry) :
    compare descriptor descriptor = Ordering.eq := by
  cases descriptor <;> rfl

end OfficialRule3Geometry

/-- Rule 4a unit classes. -/
inductive OfficialStereogenicUnitKind where
  | chiral
  | pseudoasymmetric
  | nonstereogenic
  deriving DecidableEq, Repr

namespace OfficialStereogenicUnitKind

/-- Rule 4a priority: chiral units precede pseudoasymmetric units, both preceding non-stereogenic
units. -/
def priority : OfficialStereogenicUnitKind → ℕ
  | chiral => 2
  | pseudoasymmetric => 1
  | nonstereogenic => 0

/-- Rule 4a comparison.  `Ordering.gt` means the left unit class has higher priority. -/
def compare (left right : OfficialStereogenicUnitKind) : Ordering :=
  CIPRuleEngine.comparePriorityNat left.priority right.priority

@[simp] theorem compare_chiral_pseudoasymmetric :
    compare chiral pseudoasymmetric = Ordering.gt :=
  rfl

@[simp] theorem compare_pseudoasymmetric_nonstereogenic :
    compare pseudoasymmetric nonstereogenic = Ordering.gt :=
  rfl

@[simp] theorem compare_self (kind : OfficialStereogenicUnitKind) :
    compare kind kind = Ordering.eq := by
  cases kind <;> rfl

end OfficialStereogenicUnitKind

/-- Rule 4b descriptor-pair type.  A pair is "like" when its two descriptor senses match under
the official senior/junior pairing; otherwise it is "unlike". -/
inductive OfficialDescriptorPairKind where
  | like
  | unlike
  deriving DecidableEq, Repr

namespace OfficialDescriptorPairKind

/-- Rule 4b priority: like descriptor pairs precede unlike descriptor pairs. -/
def priority : OfficialDescriptorPairKind → ℕ
  | like => 1
  | unlike => 0

/-- Rule 4b comparison.  `Ordering.gt` means the left pair kind has higher priority. -/
def compare (left right : OfficialDescriptorPairKind) : Ordering :=
  CIPRuleEngine.comparePriorityNat left.priority right.priority

@[simp] theorem compare_like_unlike :
    compare like unlike = Ordering.gt :=
  rfl

@[simp] theorem compare_self (kind : OfficialDescriptorPairKind) :
    compare kind kind = Ordering.eq := by
  cases kind <;> rfl

end OfficialDescriptorPairKind

/-- Number of Rule-4b reference descriptors selected at the first relevant population.

IUPAC P-92.5.2.1 criterion (c)(i) gives this multiplicity comparison priority over pairing:
one reference descriptor precedes two reference descriptors. -/
inductive OfficialRule4bReferenceCount where
  | one
  | two
  deriving DecidableEq, Repr

namespace OfficialRule4bReferenceCount

/-- Rule-4b reference-count priority.  `Ordering.gt` means the left ligand has priority. -/
def compare : OfficialRule4bReferenceCount → OfficialRule4bReferenceCount → Ordering
  | one, one => Ordering.eq
  | one, two => Ordering.gt
  | two, one => Ordering.lt
  | two, two => Ordering.eq

@[simp] theorem compare_one_two : compare one two = Ordering.gt := rfl

@[simp] theorem compare_two_one : compare two one = Ordering.lt := rfl

@[simp] theorem compare_self (count : OfficialRule4bReferenceCount) :
    compare count count = Ordering.eq := by
  cases count <;> rfl

end OfficialRule4bReferenceCount

/-- Rule 4c pseudoasymmetric descriptor symbols. -/
inductive OfficialPseudoasymmetricDescriptor where
  | r
  | s
  | m
  | p
  deriving DecidableEq, Repr

namespace OfficialPseudoasymmetricDescriptor

/-- Rule 4c comparison.  The official comparisons are `r > s` and `m > p`; cross-family
comparisons are left undefined because they must be handled by the surrounding stereogenic-unit
context. -/
def compare? : OfficialPseudoasymmetricDescriptor → OfficialPseudoasymmetricDescriptor →
    Option Ordering
  | r, r => some Ordering.eq
  | r, s => some Ordering.gt
  | s, r => some Ordering.lt
  | s, s => some Ordering.eq
  | m, m => some Ordering.eq
  | m, p => some Ordering.gt
  | p, m => some Ordering.lt
  | p, p => some Ordering.eq
  | _, _ => none

@[simp] theorem compare?_r_s :
    compare? r s = some Ordering.gt :=
  rfl

@[simp] theorem compare?_s_r :
    compare? s r = some Ordering.lt :=
  rfl

@[simp] theorem compare?_m_p :
    compare? m p = some Ordering.gt :=
  rfl

@[simp] theorem compare?_p_m :
    compare? p m = some Ordering.lt :=
  rfl

@[simp] theorem compare?_self (descriptor : OfficialPseudoasymmetricDescriptor) :
    compare? descriptor descriptor = some Ordering.eq := by
  cases descriptor <;> rfl

/-- Embed the current lowercase tetrahedral pseudoasymmetry descriptors into official Rule 4c. -/
def ofPseudoRS : PseudoRS → OfficialPseudoasymmetricDescriptor
  | PseudoRS.r => r
  | PseudoRS.s => s

@[simp] theorem ofPseudoRS_r :
    ofPseudoRS PseudoRS.r = r :=
  rfl

@[simp] theorem ofPseudoRS_s :
    ofPseudoRS PseudoRS.s = s :=
  rfl

end OfficialPseudoasymmetricDescriptor

/-- The senior/junior sense used by official Rule 4b and Rule 5 descriptor pairs.  Senior senses
are `R`, `M`, and `seqCis`; junior senses are `S`, `P`, and `seqTrans`. -/
inductive OfficialDescriptorSense where
  | senior
  | junior
  deriving DecidableEq, Repr

namespace OfficialDescriptorSense

/-- Senior descriptor senses precede junior descriptor senses in Rule 5. -/
def compare : OfficialDescriptorSense → OfficialDescriptorSense → Ordering
  | senior, senior => Ordering.eq
  | senior, junior => Ordering.gt
  | junior, senior => Ordering.lt
  | junior, junior => Ordering.eq

@[simp] theorem compare_senior_junior :
    compare senior junior = Ordering.gt :=
  rfl

@[simp] theorem compare_junior_senior :
    compare junior senior = Ordering.lt :=
  rfl

@[simp] theorem compare_self (sense : OfficialDescriptorSense) :
    compare sense sense = Ordering.eq := by
  cases sense <;> rfl

end OfficialDescriptorSense

/-- Rule 5 descriptor families.  The `auxiliary` flag records the official auxiliary-descriptor
layer without changing the senior/junior comparison convention. -/
inductive OfficialRule5DescriptorKind where
  | tetrahedralCenter
  | axisOrPlane
  | doubleBondOrCumulene
  deriving DecidableEq, Repr

/-- A descriptor value eligible for official Rule 5 comparison. -/
structure OfficialRule5Descriptor where
  kind : OfficialRule5DescriptorKind
  auxiliary : Bool
  sense : OfficialDescriptorSense
  deriving DecidableEq, Repr

namespace OfficialRule5Descriptor

/-- Official `R` descriptor for Rule 5. -/
def descriptorR : OfficialRule5Descriptor where
  kind := OfficialRule5DescriptorKind.tetrahedralCenter
  auxiliary := false
  sense := OfficialDescriptorSense.senior

/-- Official `S` descriptor for Rule 5. -/
def descriptorS : OfficialRule5Descriptor where
  kind := OfficialRule5DescriptorKind.tetrahedralCenter
  auxiliary := false
  sense := OfficialDescriptorSense.junior

/-- Official `M` descriptor for Rule 5. -/
def descriptorM : OfficialRule5Descriptor where
  kind := OfficialRule5DescriptorKind.axisOrPlane
  auxiliary := false
  sense := OfficialDescriptorSense.senior

/-- Official `P` descriptor for Rule 5. -/
def descriptorP : OfficialRule5Descriptor where
  kind := OfficialRule5DescriptorKind.axisOrPlane
  auxiliary := false
  sense := OfficialDescriptorSense.junior

/-- Official `seqCis` descriptor for Rule 5. -/
def descriptorSeqCis : OfficialRule5Descriptor where
  kind := OfficialRule5DescriptorKind.doubleBondOrCumulene
  auxiliary := false
  sense := OfficialDescriptorSense.senior

/-- Official `seqTrans` descriptor for Rule 5. -/
def descriptorSeqTrans : OfficialRule5Descriptor where
  kind := OfficialRule5DescriptorKind.doubleBondOrCumulene
  auxiliary := false
  sense := OfficialDescriptorSense.junior

/-- The auxiliary version of a Rule 5 descriptor. -/
def asAuxiliary (descriptor : OfficialRule5Descriptor) : OfficialRule5Descriptor where
  kind := descriptor.kind
  auxiliary := true
  sense := descriptor.sense

/-- Rule 5 comparison.  It compares only descriptors of the same descriptor family and auxiliary
level; incompatible descriptor families return `none` so that the caller must use the earlier
official rules to establish the comparison context first. -/
def compare? (left right : OfficialRule5Descriptor) : Option Ordering :=
  if left.kind = right.kind then
    if left.auxiliary = right.auxiliary then
      some (OfficialDescriptorSense.compare left.sense right.sense)
    else
      none
  else
    none

@[simp] theorem compare?_self (descriptor : OfficialRule5Descriptor) :
    compare? descriptor descriptor = some Ordering.eq := by
  simp [compare?]

/-- A Rule 4b pair is like exactly when its two Rule 5 descriptor senses agree. -/
def pairKind (left right : OfficialRule5Descriptor) : OfficialDescriptorPairKind :=
  if left.sense = right.sense then
    OfficialDescriptorPairKind.like
  else
    OfficialDescriptorPairKind.unlike

/-- Embed the current tetrahedral `R/S` descriptors into official Rule 5 descriptors. -/
def ofRS : RS → OfficialRule5Descriptor
  | RS.R => descriptorR
  | RS.S => descriptorS

@[simp] theorem compare?_R_S :
    compare? descriptorR descriptorS = some Ordering.gt :=
  rfl

@[simp] theorem compare?_S_R :
    compare? descriptorS descriptorR = some Ordering.lt :=
  rfl

@[simp] theorem compare?_M_P :
    compare? descriptorM descriptorP = some Ordering.gt :=
  rfl

@[simp] theorem compare?_P_M :
    compare? descriptorP descriptorM = some Ordering.lt :=
  rfl

@[simp] theorem compare?_seqCis_seqTrans :
    compare? descriptorSeqCis descriptorSeqTrans = some Ordering.gt :=
  rfl

@[simp] theorem compare?_seqTrans_seqCis :
    compare? descriptorSeqTrans descriptorSeqCis = some Ordering.lt :=
  rfl

@[simp] theorem compare?_ofRS_R_S :
    compare? (ofRS RS.R) (ofRS RS.S) = some Ordering.gt :=
  rfl

@[simp] theorem compare?_ofRS_S_R :
    compare? (ofRS RS.S) (ofRS RS.R) = some Ordering.lt :=
  rfl

@[simp] theorem compare?_auxiliary_R_S :
    compare? (asAuxiliary descriptorR) (asAuxiliary descriptorS) = some Ordering.gt :=
  rfl

@[simp] theorem pairKind_R_S :
    pairKind descriptorR descriptorS = OfficialDescriptorPairKind.unlike :=
  rfl

@[simp] theorem pairKind_R_M :
    pairKind descriptorR descriptorM = OfficialDescriptorPairKind.like :=
  rfl

@[simp] theorem pairKind_S_P :
    pairKind descriptorS descriptorP = OfficialDescriptorPairKind.like :=
  rfl

@[simp] theorem pairKind_R_P :
    pairKind descriptorR descriptorP = OfficialDescriptorPairKind.unlike :=
  rfl

theorem compare?_ofRS_eq_rule5PairOrdering (left right : RS) :
    compare? (ofRS left) (ofRS right) = some (rule5PairOrdering left right) := by
  cases left <;> cases right <;> rfl

end OfficialRule5Descriptor

/-! ### The official rule system as a bundled target -/

/-- Bundled official sequence-rule system with the comparator primitives that are definitional in
the standard itself. -/
structure OfficialCIPRuleSystem where
  rules : List OfficialCIPSequenceRule
  rules_complete : ∀ rule, rule ∈ rules
  rules_nodup : rules.Nodup
  rule3Compare : OfficialRule3Geometry → OfficialRule3Geometry → Ordering
  rule4aCompare : OfficialStereogenicUnitKind → OfficialStereogenicUnitKind → Ordering
  rule4bReferenceCountCompare :
    OfficialRule4bReferenceCount → OfficialRule4bReferenceCount → Ordering
  rule4bCompare : OfficialDescriptorPairKind → OfficialDescriptorPairKind → Ordering
  rule4cCompare? :
    OfficialPseudoasymmetricDescriptor → OfficialPseudoasymmetricDescriptor → Option Ordering
  rule5Compare? : OfficialRule5Descriptor → OfficialRule5Descriptor → Option Ordering

/-- The IUPAC P-92 sequence-rule system as a concrete Lean object. -/
def iupacSequenceRuleSystem : OfficialCIPRuleSystem where
  rules := OfficialCIPSequenceRule.all
  rules_complete := OfficialCIPSequenceRule.mem_all
  rules_nodup := OfficialCIPSequenceRule.all_nodup
  rule3Compare := OfficialRule3Geometry.compare
  rule4aCompare := OfficialStereogenicUnitKind.compare
  rule4bReferenceCountCompare := OfficialRule4bReferenceCount.compare
  rule4bCompare := OfficialDescriptorPairKind.compare
  rule4cCompare? := OfficialPseudoasymmetricDescriptor.compare?
  rule5Compare? := OfficialRule5Descriptor.compare?

@[simp] theorem iupacSequenceRuleSystem_rules :
    iupacSequenceRuleSystem.rules = OfficialCIPSequenceRule.all :=
  rfl

@[simp] theorem iupacSequenceRuleSystem_rule3_seqcis_seqtrans :
    iupacSequenceRuleSystem.rule3Compare OfficialRule3Geometry.seqcis
      OfficialRule3Geometry.seqtrans = Ordering.gt :=
  rfl

@[simp] theorem iupacSequenceRuleSystem_rule4a_chiral_pseudoasymmetric :
    iupacSequenceRuleSystem.rule4aCompare OfficialStereogenicUnitKind.chiral
      OfficialStereogenicUnitKind.pseudoasymmetric = Ordering.gt :=
  rfl

@[simp] theorem iupacSequenceRuleSystem_rule4b_like_unlike :
    iupacSequenceRuleSystem.rule4bCompare OfficialDescriptorPairKind.like
      OfficialDescriptorPairKind.unlike = Ordering.gt :=
  rfl

@[simp] theorem iupacSequenceRuleSystem_rule4b_one_reference_two :
    iupacSequenceRuleSystem.rule4bReferenceCountCompare
      OfficialRule4bReferenceCount.one OfficialRule4bReferenceCount.two = Ordering.gt :=
  rfl

@[simp] theorem iupacSequenceRuleSystem_rule4c_r_s :
    iupacSequenceRuleSystem.rule4cCompare? OfficialPseudoasymmetricDescriptor.r
      OfficialPseudoasymmetricDescriptor.s = some Ordering.gt :=
  rfl

@[simp] theorem iupacSequenceRuleSystem_rule5_R_S :
    iupacSequenceRuleSystem.rule5Compare? OfficialRule5Descriptor.descriptorR
      OfficialRule5Descriptor.descriptorS = some Ordering.gt :=
  rfl

/-! ### Integrated official-rule comparison contexts -/

namespace CIPRuleEngine

/-- A trace decision tagged by an official-rule-backed trace family. -/
def officialRuleDecision (rule : CIPRuleFamily) (outcome : Ordering) : CIPRuleDecision where
  rule := rule
  outcome := outcome

/-- Compare optional official-rule data.  Missing data means "this rule cannot decide here",
represented by an `eq` trace decision rather than by an unsafe guess. -/
def compareOfficialOption {α : Type*} (cmp : α → α → Ordering) :
    Option α → Option α → Ordering
  | some left, some right => cmp left right
  | _, _ => Ordering.eq

/-- Compare optional official-rule data when the primitive comparator itself can be undefined
outside its family.  Missing or cross-family data safely tie. -/
def compareOfficialOption? {α : Type*} (cmp : α → α → Option Ordering) :
    Option α → Option α → Ordering
  | some left, some right =>
      match cmp left right with
      | some outcome => outcome
      | none => Ordering.eq
  | _, _ => Ordering.eq

/-- Rule context attached to a ligand branch once graph expansion has tied by Rules 1 and 2.

Each field is optional on purpose.  A production detector can fill only the stereochemical facts it
has proved; absent facts produce tied rule decisions and therefore safe failure rather than an
invented priority. -/
structure OfficialLigandRuleContext where
  rule3Geometry? : Option OfficialRule3Geometry := none
  rule4aKind? : Option OfficialStereogenicUnitKind := none
  rule4bPair? : Option OfficialDescriptorPairKind := none
  rule4cDescriptor? : Option OfficialPseudoasymmetricDescriptor := none
  rule5Descriptor? : Option OfficialRule5Descriptor := none
  deriving DecidableEq, Repr

namespace OfficialLigandRuleContext

/-- Empty official-rule context: no descriptor-rich rule can decide. -/
def empty : OfficialLigandRuleContext := {}

/-- Context carrying a Rule 3 double-bond/cumulene geometry fact. -/
def ofRule3Geometry (geometry : OfficialRule3Geometry) : OfficialLigandRuleContext where
  rule3Geometry? := some geometry

/-- Context carrying a Rule 4a stereogenic-unit class. -/
def ofRule4aKind (kind : OfficialStereogenicUnitKind) : OfficialLigandRuleContext where
  rule4aKind? := some kind

/-- Context carrying a Rule 4b like/unlike descriptor-pair fact. -/
def ofRule4bPair (pair : OfficialDescriptorPairKind) : OfficialLigandRuleContext where
  rule4bPair? := some pair

/-- Context carrying a Rule 4c pseudoasymmetric descriptor fact. -/
def ofRule4cDescriptor (descriptor : OfficialPseudoasymmetricDescriptor) :
    OfficialLigandRuleContext where
  rule4aKind? := some OfficialStereogenicUnitKind.pseudoasymmetric
  rule4cDescriptor? := some descriptor

/-- Context carrying the current lowercase tetrahedral pseudoasymmetry descriptor. -/
def ofPseudoRS (descriptor : PseudoRS) : OfficialLigandRuleContext :=
  ofRule4cDescriptor (OfficialPseudoasymmetricDescriptor.ofPseudoRS descriptor)

/-- Context carrying a Rule 5 descriptor. -/
def ofRule5Descriptor (descriptor : OfficialRule5Descriptor) : OfficialLigandRuleContext where
  rule4aKind? := some OfficialStereogenicUnitKind.chiral
  rule5Descriptor? := some descriptor

/-- Context carrying the current tetrahedral `R/S` descriptor as official Rule 5 data. -/
def ofRS (descriptor : RS) : OfficialLigandRuleContext :=
  ofRule5Descriptor (OfficialRule5Descriptor.ofRS descriptor)

/-- Add a Rule 3 fact to an existing context. -/
def withRule3Geometry (context : OfficialLigandRuleContext)
    (geometry : OfficialRule3Geometry) : OfficialLigandRuleContext :=
  { context with rule3Geometry? := some geometry }

/-- Add a Rule 4a fact to an existing context. -/
def withRule4aKind (context : OfficialLigandRuleContext)
    (kind : OfficialStereogenicUnitKind) : OfficialLigandRuleContext :=
  { context with rule4aKind? := some kind }

/-- Add a Rule 4b fact to an existing context. -/
def withRule4bPair (context : OfficialLigandRuleContext)
    (pair : OfficialDescriptorPairKind) : OfficialLigandRuleContext :=
  { context with rule4bPair? := some pair }

/-- Add a Rule 4c fact to an existing context. -/
def withRule4cDescriptor (context : OfficialLigandRuleContext)
    (descriptor : OfficialPseudoasymmetricDescriptor) : OfficialLigandRuleContext :=
  { context with
    rule4aKind? := some OfficialStereogenicUnitKind.pseudoasymmetric
    rule4cDescriptor? := some descriptor }

/-- Add a Rule 5 fact to an existing context. -/
def withRule5Descriptor (context : OfficialLigandRuleContext)
    (descriptor : OfficialRule5Descriptor) : OfficialLigandRuleContext :=
  { context with
    rule4aKind? := some OfficialStereogenicUnitKind.chiral
    rule5Descriptor? := some descriptor }

@[simp] theorem empty_rule3 :
    empty.rule3Geometry? = none :=
  rfl

@[simp] theorem ofRS_R_rule5 :
    (ofRS RS.R).rule5Descriptor? = some OfficialRule5Descriptor.descriptorR :=
  rfl

@[simp] theorem ofRS_S_rule5 :
    (ofRS RS.S).rule5Descriptor? = some OfficialRule5Descriptor.descriptorS :=
  rfl

@[simp] theorem ofPseudoRS_r_rule4c :
    (ofPseudoRS PseudoRS.r).rule4cDescriptor? =
      some OfficialPseudoasymmetricDescriptor.r :=
  rfl

@[simp] theorem ofPseudoRS_s_rule4c :
    (ofPseudoRS PseudoRS.s).rule4cDescriptor? =
      some OfficialPseudoasymmetricDescriptor.s :=
  rfl

end OfficialLigandRuleContext

/-- Rule 3 trace decision from official ligand contexts. -/
def officialRule3Decision (left right : OfficialLigandRuleContext) : CIPRuleDecision :=
  officialRuleDecision CIPRuleFamily.doubleBondGeometry
    (compareOfficialOption OfficialRule3Geometry.compare
      left.rule3Geometry? right.rule3Geometry?)

/-- Rule 4a trace decision from official ligand contexts. -/
def officialRule4aDecision (left right : OfficialLigandRuleContext) : CIPRuleDecision :=
  officialRuleDecision CIPRuleFamily.stereogenicUnitKind
    (compareOfficialOption OfficialStereogenicUnitKind.compare
      left.rule4aKind? right.rule4aKind?)

/-- Rule 4b trace decision from official ligand contexts. -/
def officialRule4bDecision (left right : OfficialLigandRuleContext) : CIPRuleDecision :=
  officialRuleDecision CIPRuleFamily.likeUnlikeDescriptorPair
    (compareOfficialOption OfficialDescriptorPairKind.compare
      left.rule4bPair? right.rule4bPair?)

/-- Rule 4c trace decision from official ligand contexts. -/
def officialRule4cDecision (left right : OfficialLigandRuleContext) : CIPRuleDecision :=
  officialRuleDecision CIPRuleFamily.pseudoasymmetricDescriptor
    (compareOfficialOption? OfficialPseudoasymmetricDescriptor.compare?
      left.rule4cDescriptor? right.rule4cDescriptor?)

/-- Rule 5 trace decision from official ligand contexts. -/
def officialRule5Decision (left right : OfficialLigandRuleContext) : CIPRuleDecision :=
  officialRuleDecision CIPRuleFamily.pseudoasymmetricTiebreak
    (compareOfficialOption? OfficialRule5Descriptor.compare?
      left.rule5Descriptor? right.rule5Descriptor?)

/-- Official descriptor-rich rule trace consulted after Rules 1 and 2 have tied. -/
def compareOfficialContextTrace (left right : OfficialLigandRuleContext) :
    List CIPRuleDecision :=
  [ officialRule3Decision left right
  , officialRule4aDecision left right
  , officialRule4bDecision left right
  , officialRule4cDecision left right
  , officialRule5Decision left right
  ]

/-- A descriptor context compared with itself ties at every later sequence rule. -/
@[simp] theorem compareOfficialContextTrace_self (context : OfficialLigandRuleContext) :
    cipTraceOutcome (compareOfficialContextTrace context context) = Ordering.eq := by
  rcases context with ⟨rule3, rule4a, rule4b, rule4c, rule5⟩
  cases rule3 <;> cases rule4a <;> cases rule4b <;> cases rule4c <;> cases rule5 <;>
    simp [compareOfficialContextTrace, officialRule3Decision, officialRule4aDecision,
      officialRule4bDecision, officialRule4cDecision, officialRule5Decision,
      officialRuleDecision, compareOfficialOption, compareOfficialOption?,
      OfficialRule3Geometry.compare_self, OfficialStereogenicUnitKind.compare_self,
      OfficialDescriptorPairKind.compare_self,
      OfficialPseudoasymmetricDescriptor.compare?_self,
      OfficialRule5Descriptor.compare?_self]

/-- Compare ordinary graph keys first; if they tie, consult the integrated official Rule 3/4/5
context in IUPAC order. -/
def compareKeyThenOfficialTrace (leftKey rightKey : List MoleculeGraph.AtomLabel)
    (left right : OfficialLigandRuleContext) : List CIPRuleDecision :=
  let baseTrace := compareKeyTrace leftKey rightKey
  if cipTraceOutcome baseTrace = Ordering.eq then
    baseTrace ++ compareOfficialContextTrace left right
  else
    baseTrace

/-- Proof-carrying comparison through Rules 1, 2, 3, 4a, 4b, 4c, and 5. -/
def compareKeyThenOfficialCertificate (leftKey rightKey : List MoleculeGraph.AtomLabel)
    (left right : OfficialLigandRuleContext) : CIPTraceCertificate :=
  CIPTraceCertificate.ofTrace (compareKeyThenOfficialTrace leftKey rightKey left right)

@[simp] theorem compareKeyThenOfficialCertificate_outcome
    (leftKey rightKey : List MoleculeGraph.AtomLabel)
    (left right : OfficialLigandRuleContext) :
    (compareKeyThenOfficialCertificate leftKey rightKey left right).outcome =
      cipTraceOutcome (compareKeyThenOfficialTrace leftKey rightKey left right) :=
  rfl

theorem compareKeyThenOfficialTrace_outcome_of_key_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel}
    {left right : OfficialLigandRuleContext}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    cipTraceOutcome (compareKeyThenOfficialTrace leftKey rightKey left right) =
      cipTraceOutcome (compareOfficialContextTrace left right) := by
  simp [compareKeyThenOfficialTrace, h, cipTraceOutcome_append_of_left_eq h]

theorem compareKeyThenOfficialTrace_outcome_of_key_ne_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel}
    {left right : OfficialLigandRuleContext}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) ≠ Ordering.eq) :
    cipTraceOutcome (compareKeyThenOfficialTrace leftKey rightKey left right) =
      cipTraceOutcome (compareKeyTrace leftKey rightKey) := by
  simp [compareKeyThenOfficialTrace, h]

@[simp] theorem compareOfficialContextTrace_rule3_seqcis_seqtrans :
    cipTraceOutcome
      (compareOfficialContextTrace
        (OfficialLigandRuleContext.ofRule3Geometry OfficialRule3Geometry.seqcis)
        (OfficialLigandRuleContext.ofRule3Geometry OfficialRule3Geometry.seqtrans)) =
      Ordering.gt :=
  rfl

@[simp] theorem compareOfficialContextTrace_rule4a_chiral_pseudoasymmetric :
    cipTraceOutcome
      (compareOfficialContextTrace
        (OfficialLigandRuleContext.ofRule4aKind OfficialStereogenicUnitKind.chiral)
        (OfficialLigandRuleContext.ofRule4aKind
          OfficialStereogenicUnitKind.pseudoasymmetric)) =
      Ordering.gt :=
  rfl

@[simp] theorem compareOfficialContextTrace_rule4b_like_unlike :
    cipTraceOutcome
      (compareOfficialContextTrace
        (OfficialLigandRuleContext.ofRule4bPair OfficialDescriptorPairKind.like)
        (OfficialLigandRuleContext.ofRule4bPair OfficialDescriptorPairKind.unlike)) =
      Ordering.gt :=
  rfl

@[simp] theorem compareOfficialContextTrace_rule4c_r_s :
    cipTraceOutcome
      (compareOfficialContextTrace
        (OfficialLigandRuleContext.ofRule4cDescriptor OfficialPseudoasymmetricDescriptor.r)
        (OfficialLigandRuleContext.ofRule4cDescriptor OfficialPseudoasymmetricDescriptor.s)) =
      Ordering.gt :=
  rfl

@[simp] theorem compareOfficialContextTrace_rule5_R_S :
    cipTraceOutcome
      (compareOfficialContextTrace
        (OfficialLigandRuleContext.ofRS RS.R)
        (OfficialLigandRuleContext.ofRS RS.S)) =
      Ordering.gt :=
  rfl

theorem compareKeyThenOfficialCertificate_rule3_seqcis_seqtrans_of_key_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (compareKeyThenOfficialCertificate leftKey rightKey
      (OfficialLigandRuleContext.ofRule3Geometry OfficialRule3Geometry.seqcis)
      (OfficialLigandRuleContext.ofRule3Geometry OfficialRule3Geometry.seqtrans)).outcome =
      Ordering.gt := by
  simp [compareKeyThenOfficialCertificate, compareKeyThenOfficialTrace_outcome_of_key_eq h]

theorem compareKeyThenOfficialCertificate_rule4a_chiral_pseudoasymmetric_of_key_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (compareKeyThenOfficialCertificate leftKey rightKey
      (OfficialLigandRuleContext.ofRule4aKind OfficialStereogenicUnitKind.chiral)
      (OfficialLigandRuleContext.ofRule4aKind
        OfficialStereogenicUnitKind.pseudoasymmetric)).outcome =
      Ordering.gt := by
  simp [compareKeyThenOfficialCertificate, compareKeyThenOfficialTrace_outcome_of_key_eq h]

theorem compareKeyThenOfficialCertificate_rule4b_like_unlike_of_key_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (compareKeyThenOfficialCertificate leftKey rightKey
      (OfficialLigandRuleContext.ofRule4bPair OfficialDescriptorPairKind.like)
      (OfficialLigandRuleContext.ofRule4bPair OfficialDescriptorPairKind.unlike)).outcome =
      Ordering.gt := by
  simp [compareKeyThenOfficialCertificate, compareKeyThenOfficialTrace_outcome_of_key_eq h]

theorem compareKeyThenOfficialCertificate_rule4c_r_s_of_key_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (compareKeyThenOfficialCertificate leftKey rightKey
      (OfficialLigandRuleContext.ofRule4cDescriptor OfficialPseudoasymmetricDescriptor.r)
      (OfficialLigandRuleContext.ofRule4cDescriptor OfficialPseudoasymmetricDescriptor.s)).outcome =
      Ordering.gt := by
  simp [compareKeyThenOfficialCertificate, compareKeyThenOfficialTrace_outcome_of_key_eq h]

theorem compareKeyThenOfficialCertificate_rule5_R_S_of_key_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (compareKeyThenOfficialCertificate leftKey rightKey
      (OfficialLigandRuleContext.ofRS RS.R)
      (OfficialLigandRuleContext.ofRS RS.S)).outcome =
      Ordering.gt := by
  simp [compareKeyThenOfficialCertificate, compareKeyThenOfficialTrace_outcome_of_key_eq h]

end CIPRuleEngine

namespace OneCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Descriptor-facing comparison of two local ligands with official Rule 3/4/5 context supplied by
the caller.  The graph key handles Rules 1 and 2; the context handles Rules 3, 4a, 4b, 4c, and 5
only when the graph key ties. -/
noncomputable def cipRuleCompareOfficialDescriptor (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4) :
    CIPTraceCertificate :=
  CIPRuleEngine.compareKeyThenOfficialCertificate
    (m.cipKeyDescriptor i) (m.cipKeyDescriptor j) (context i) (context j)

/-- Boolean ordering predicate for official-rule-aware ligand sorting.  Decisive official
comparisons are respected; exact ties are broken by the original ligand index only to keep the
computed list total.  Use `ResolvedOfficialCIPDescriptor` before interpreting the order as a
stereochemical descriptor. -/
noncomputable def cipOfficialDescriptorBefore (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4) : Bool :=
  match (m.cipRuleCompareOfficialDescriptor context i j).outcome with
  | Ordering.gt => true
  | Ordering.lt => false
  | Ordering.eq => decide (i ≤ j)

/-- The four ligand indices sorted by the integrated official-rule comparator, with deterministic
tie breaking by ligand index. -/
noncomputable def cipOrderOfficialDescriptor (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) : List (Fin 4) :=
  (List.finRange 4).mergeSort (m.cipOfficialDescriptorBefore context)

theorem cipOrderOfficialDescriptor_perm_finRange (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    (m.cipOrderOfficialDescriptor context).Perm (List.finRange 4) := by
  classical
  simpa [cipOrderOfficialDescriptor] using
    (List.mergeSort_perm (List.finRange 4) (m.cipOfficialDescriptorBefore context))

theorem length_cipOrderOfficialDescriptor (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    (m.cipOrderOfficialDescriptor context).length = 4 := by
  classical
  have hperm := m.cipOrderOfficialDescriptor_perm_finRange context
  have := hperm.length_eq
  simpa [List.length_finRange] using this

theorem nodup_cipOrderOfficialDescriptor (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    (m.cipOrderOfficialDescriptor context).Nodup := by
  classical
  exact (List.nodup_finRange 4).perm (m.cipOrderOfficialDescriptor_perm_finRange context).symm

theorem mem_cipOrderOfficialDescriptor (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i : Fin 4) :
    i ∈ m.cipOrderOfficialDescriptor context := by
  classical
  have hperm := m.cipOrderOfficialDescriptor_perm_finRange context
  exact (hperm.mem_iff).2 (List.mem_finRange i)

/-- The permutation whose order is the official-rule-aware ligand order. -/
noncomputable def cipPermutationOfficialDescriptor (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) : Equiv.Perm (Fin 4) := by
  classical
  let l : List (Fin 4) := m.cipOrderOfficialDescriptor context
  have hlen : l.length = 4 := by
    simpa [l] using m.length_cipOrderOfficialDescriptor context
  have hnodup : l.Nodup := by
    simpa [l] using m.nodup_cipOrderOfficialDescriptor context
  have hmem : ∀ i : Fin 4, i ∈ l := by
    intro i
    simpa [l] using m.mem_cipOrderOfficialDescriptor context i
  exact ((Fin.castOrderIso hlen.symm).toEquiv).trans
    (List.Nodup.getEquivOfForallMemList l hnodup hmem)

/-- Official descriptor priorities are resolved when every distinct ligand pair has a decisive
official-rule-aware comparison. -/
def ResolvedOfficialCIPDescriptor (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) : Prop :=
  ∀ i j : Fin 4, i ≠ j → (m.cipRuleCompareOfficialDescriptor context i j).outcome ≠ Ordering.eq

/-- Official-rule-aware order with tie refusal. -/
noncomputable def cipOrderOfficialDescriptor? (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) : Option (List (Fin 4)) :=
  by
    classical
    exact
      if _h : m.ResolvedOfficialCIPDescriptor context then
        some (m.cipOrderOfficialDescriptor context)
      else
        none

/-- Official-rule-aware permutation with tie refusal. -/
noncomputable def cipPermutationOfficialDescriptor? (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    Option (Equiv.Perm (Fin 4)) :=
  by
    classical
    exact
      if _h : m.ResolvedOfficialCIPDescriptor context then
        some (m.cipPermutationOfficialDescriptor context)
      else
        none

theorem cipOrderOfficialDescriptor?_eq_some_of_resolved (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (h : m.ResolvedOfficialCIPDescriptor context) :
    m.cipOrderOfficialDescriptor? context = some (m.cipOrderOfficialDescriptor context) := by
  classical
  simp [cipOrderOfficialDescriptor?, h]

theorem cipPermutationOfficialDescriptor?_eq_some_of_resolved (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (h : m.ResolvedOfficialCIPDescriptor context) :
    m.cipPermutationOfficialDescriptor? context =
      some (m.cipPermutationOfficialDescriptor context) := by
  classical
  simp [cipPermutationOfficialDescriptor?, h]

/-- Official-rule-aware descriptor engine surface for one-center molecules. -/
structure OfficialCIPDescriptorEngineResult (m : OneCenterMolecule V) where
  key : Fin 4 → List MoleculeGraph.AtomLabel
  context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext
  compare : Fin 4 → Fin 4 → CIPTraceCertificate
  order : List (Fin 4)
  permutation : Equiv.Perm (Fin 4)
  safeOrder? : Option (List (Fin 4))
  safePermutation? : Option (Equiv.Perm (Fin 4))

/-- Run the official-rule-aware descriptor comparison engine with supplied ligand contexts. -/
noncomputable def cipOfficialDescriptorEngine (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    OfficialCIPDescriptorEngineResult m where
  key := m.cipKeyDescriptor
  context := context
  compare := m.cipRuleCompareOfficialDescriptor context
  order := m.cipOrderOfficialDescriptor context
  permutation := m.cipPermutationOfficialDescriptor context
  safeOrder? := m.cipOrderOfficialDescriptor? context
  safePermutation? := m.cipPermutationOfficialDescriptor? context

@[simp] theorem cipOfficialDescriptorEngine_compare (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4) :
    (m.cipOfficialDescriptorEngine context).compare i j =
      m.cipRuleCompareOfficialDescriptor context i j :=
  rfl

@[simp] theorem cipOfficialDescriptorEngine_order (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    (m.cipOfficialDescriptorEngine context).order =
      m.cipOrderOfficialDescriptor context :=
  rfl

@[simp] theorem cipOfficialDescriptorEngine_safePermutation?_eq_some_of_resolved
    (m : OneCenterMolecule V) (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (h : m.ResolvedOfficialCIPDescriptor context) :
    (m.cipOfficialDescriptorEngine context).safePermutation? =
      some (m.cipPermutationOfficialDescriptor context) := by
  simpa using m.cipPermutationOfficialDescriptor?_eq_some_of_resolved context h

end OneCenterMolecule

namespace MultiCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Descriptor-facing local comparison at a distinguished center with official Rule 3/4/5 context. -/
noncomputable def cipRuleCompareOfficialDescriptorAt (m : MultiCenterMolecule V)
    (context : m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (c : m.Center) (i j : Fin 4) : CIPTraceCertificate :=
  CIPRuleEngine.compareKeyThenOfficialCertificate
    (m.cipKeyDescriptorAt c i) (m.cipKeyDescriptorAt c j)
    (context c i) (context c j)

/-- Official-rule-aware local order at a distinguished center. -/
noncomputable def cipOrderOfficialDescriptorAt (m : MultiCenterMolecule V)
    (context : m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (c : m.Center) : List (Fin 4) :=
  (m.toOneCenterMolecule c).cipOrderOfficialDescriptor (context c)

/-- Official-rule-aware local permutation at a distinguished center. -/
noncomputable def cipPermutationOfficialDescriptorAt (m : MultiCenterMolecule V)
    (context : m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (c : m.Center) : Equiv.Perm (Fin 4) :=
  (m.toOneCenterMolecule c).cipPermutationOfficialDescriptor (context c)

/-- Local official-rule-aware resolvedness at a distinguished center. -/
def ResolvedOfficialCIPDescriptorAt (m : MultiCenterMolecule V)
    (context : m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (c : m.Center) : Prop :=
  (m.toOneCenterMolecule c).ResolvedOfficialCIPDescriptor (context c)

/-- Official-rule-aware local order with tie refusal. -/
noncomputable def cipOrderOfficialDescriptorAt? (m : MultiCenterMolecule V)
    (context : m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (c : m.Center) : Option (List (Fin 4)) :=
  (m.toOneCenterMolecule c).cipOrderOfficialDescriptor? (context c)

/-- Official-rule-aware local permutation with tie refusal. -/
noncomputable def cipPermutationOfficialDescriptorAt? (m : MultiCenterMolecule V)
    (context : m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (c : m.Center) : Option (Equiv.Perm (Fin 4)) :=
  (m.toOneCenterMolecule c).cipPermutationOfficialDescriptor? (context c)

end MultiCenterMolecule

/-! ### Bridge from the current trace engine to official rule slots -/

namespace CIPRuleFamily

/-- Official sequence-rule slot corresponding to a current trace family, when the family is an
actual official priority rule rather than an implementation bookkeeping step or graph-expansion
convention. -/
def officialRule? : CIPRuleFamily → Option OfficialCIPSequenceRule
  | atomicNumber => some OfficialCIPSequenceRule.rule1aAtomicNumber
  | isotopeMass => some OfficialCIPSequenceRule.rule2AtomicMass
  | duplicateAtom => some OfficialCIPSequenceRule.rule1bDuplicateNodeProximity
  | doubleBondGeometry => some OfficialCIPSequenceRule.rule3DoubleBondGeometry
  | stereogenicUnitKind => some OfficialCIPSequenceRule.rule4aStereogenicUnitKind
  | likeUnlikeDescriptorPair => some OfficialCIPSequenceRule.rule4bLikeUnlikeDescriptorPairs
  | pseudoasymmetricDescriptor => some OfficialCIPSequenceRule.rule4cPseudoasymmetricDescriptor
  | pseudoasymmetricTiebreak => some OfficialCIPSequenceRule.rule5EnantiomorphicDescriptor
  | multipleBondExpansion => none
  | cycleDuplicateLeaf => none
  | frontierExhaustion => none
  | descriptorSubrule => none

@[simp] theorem officialRule?_atomicNumber :
    officialRule? atomicNumber = some OfficialCIPSequenceRule.rule1aAtomicNumber :=
  rfl

@[simp] theorem officialRule?_isotopeMass :
    officialRule? isotopeMass = some OfficialCIPSequenceRule.rule2AtomicMass :=
  rfl

@[simp] theorem officialRule?_pseudoasymmetricTiebreak :
    officialRule? pseudoasymmetricTiebreak =
      some OfficialCIPSequenceRule.rule5EnantiomorphicDescriptor :=
  rfl

@[simp] theorem officialRule?_doubleBondGeometry :
    officialRule? doubleBondGeometry =
      some OfficialCIPSequenceRule.rule3DoubleBondGeometry :=
  rfl

@[simp] theorem officialRule?_stereogenicUnitKind :
    officialRule? stereogenicUnitKind =
      some OfficialCIPSequenceRule.rule4aStereogenicUnitKind :=
  rfl

@[simp] theorem officialRule?_likeUnlikeDescriptorPair :
    officialRule? likeUnlikeDescriptorPair =
      some OfficialCIPSequenceRule.rule4bLikeUnlikeDescriptorPairs :=
  rfl

@[simp] theorem officialRule?_pseudoasymmetricDescriptor :
    officialRule? pseudoasymmetricDescriptor =
      some OfficialCIPSequenceRule.rule4cPseudoasymmetricDescriptor :=
  rfl

end CIPRuleFamily

namespace CIPRuleDecision

/-- Official rule slot associated with a concrete trace decision, when present. -/
def officialRule? (decision : CIPRuleDecision) : Option OfficialCIPSequenceRule :=
  decision.rule.officialRule?

end CIPRuleDecision

namespace CIPTraceCertificate

/-- Official rule slots touched by a current comparison certificate.  Bookkeeping trace decisions
are intentionally omitted. -/
def officialRules (certificate : CIPTraceCertificate) : List OfficialCIPSequenceRule :=
  certificate.trace.filterMap CIPRuleDecision.officialRule?

end CIPTraceCertificate

/-- Coarse status of each official rule relative to the current engine.  `integrated` means a
current public comparison path emits that rule in proof-carrying traces; `expansionPrimitive`
means the rule is represented by graph-expansion data but is not a standalone descriptor-context
decision. -/
inductive OfficialRuleEngineStatus where
  | integrated
  | expansionPrimitive
  deriving DecidableEq, Repr

/-- Present implementation status of the official rule slots. -/
def officialRuleEngineStatus : OfficialCIPSequenceRule → OfficialRuleEngineStatus
  | OfficialCIPSequenceRule.rule1aAtomicNumber => OfficialRuleEngineStatus.integrated
  | OfficialCIPSequenceRule.rule1bDuplicateNodeProximity =>
      OfficialRuleEngineStatus.expansionPrimitive
  | OfficialCIPSequenceRule.rule2AtomicMass => OfficialRuleEngineStatus.integrated
  | OfficialCIPSequenceRule.rule3DoubleBondGeometry => OfficialRuleEngineStatus.integrated
  | OfficialCIPSequenceRule.rule4aStereogenicUnitKind => OfficialRuleEngineStatus.integrated
  | OfficialCIPSequenceRule.rule4bLikeUnlikeDescriptorPairs => OfficialRuleEngineStatus.integrated
  | OfficialCIPSequenceRule.rule4cPseudoasymmetricDescriptor => OfficialRuleEngineStatus.integrated
  | OfficialCIPSequenceRule.rule5EnantiomorphicDescriptor =>
      OfficialRuleEngineStatus.integrated

@[simp] theorem officialRuleEngineStatus_rule1a :
    officialRuleEngineStatus OfficialCIPSequenceRule.rule1aAtomicNumber =
      OfficialRuleEngineStatus.integrated :=
  rfl

@[simp] theorem officialRuleEngineStatus_rule2 :
    officialRuleEngineStatus OfficialCIPSequenceRule.rule2AtomicMass =
      OfficialRuleEngineStatus.integrated :=
  rfl

@[simp] theorem officialRuleEngineStatus_rule5 :
    officialRuleEngineStatus OfficialCIPSequenceRule.rule5EnantiomorphicDescriptor =
      OfficialRuleEngineStatus.integrated :=
  rfl

@[simp] theorem officialRuleEngineStatus_rule3 :
    officialRuleEngineStatus OfficialCIPSequenceRule.rule3DoubleBondGeometry =
      OfficialRuleEngineStatus.integrated :=
  rfl

@[simp] theorem officialRuleEngineStatus_rule4a :
    officialRuleEngineStatus OfficialCIPSequenceRule.rule4aStereogenicUnitKind =
      OfficialRuleEngineStatus.integrated :=
  rfl

@[simp] theorem officialRuleEngineStatus_rule4b :
    officialRuleEngineStatus OfficialCIPSequenceRule.rule4bLikeUnlikeDescriptorPairs =
      OfficialRuleEngineStatus.integrated :=
  rfl

@[simp] theorem officialRuleEngineStatus_rule4c :
    officialRuleEngineStatus OfficialCIPSequenceRule.rule4cPseudoasymmetricDescriptor =
      OfficialRuleEngineStatus.integrated :=
  rfl

end
end OneCenter
end TetraStereo
