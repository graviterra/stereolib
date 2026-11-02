import TetraStereo.OneCenter.ProductionCIPOccurrenceDescriptorComparatorLaws
import TetraStereo.OneCenter.ProductionCIPLinearOccurrenceComparatorCompleteness
import TetraStereo.OneCenter.DeclarativeCIPOccurrenceRules456

set_option autoImplicit false


































































namespace TetraStereo.UniversalProof.ProductionOccurrenceDomainWitnessProofs

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.ProductionCIPOccurrenceDescriptorComparatorLaws
open TetraStereo.OneCenter.ProductionCIPLinearOccurrenceComparatorCompleteness
open TetraStereo.OneCenter.DeclarativeCIP.ProductionOccurrenceRules456 (TerminalAcyclicCIPFrame)

/-! ## Selector lemmas for the unary compiler -/

theorem option_isSome_eq_true_iff {α : Type} (option : Option α) :
    option.isSome = true ↔ ∃ value, option = some value := by
  constructor
  · intro present
    cases option with
    | none => simp [Option.isSome] at present
    | some value => exact ⟨value, rfl⟩
  · rintro ⟨value, rfl⟩
    rfl

theorem option_isNone_eq_true_iff {α : Type} (option : Option α) :
    option.isNone = true ↔ option = none := by
  constructor
  · intro absent
    cases option with
    | none => rfl
    | some value => simp [Option.isNone] at absent
  · rintro rfl
    rfl

/-! ## The literal unary production selector

`productionFullyCompiled` is exactly the conjunction of unary production observations already
proved sufficient by `compareOccurrenceBranches?_terminal_supported_silent_of_left_acyclic`: a
terminal cursor, an acyclic root atom at the selected fuel, a Rule-1a label present at the root, and
no auxiliary Rule-4/5 fact at the root.  Each conjunct is a property of the single cursor. -/

def productionFullyCompiled (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (cursor : CanonicalRerootCursor) : Bool :=
  cursorTerminal mol cursor
    && !mol.atomLiesInCycle fuel cursor.node.atom
    && (mol.canonicalRule1aLabel? cursor.node).isSome
    && (state.factAt? cursor.node).isNone

/-- `Bool.not` as an acyclicity selector. -/
theorem bool_not_eq_true_iff (value : Bool) : (!value) = true ↔ value = false := by
  cases value <;> simp

theorem bool_not_eq_true_of (value : Bool) (h : value = false) : (!value) = true :=
  (bool_not_eq_true_iff value).mpr h

/-- Refinement law: a compiled cursor exposes every literal production-support fact. -/
theorem productionFullyCompiled_spec {mol : RawMolecule} {state : OccurrenceAuxState}
    {fuel : Nat} {cursor : CanonicalRerootCursor}
    (compiled : productionFullyCompiled mol state fuel cursor = true) :
    cursorTerminal mol cursor = true ∧
      mol.atomLiesInCycle fuel cursor.node.atom = false ∧
      (mol.canonicalRule1aLabel? cursor.node).isSome = true ∧
      (state.factAt? cursor.node).isNone = true := by
  simp only [productionFullyCompiled, Bool.and_eq_true] at compiled
  exact ⟨compiled.1.1.1, (bool_not_eq_true_iff _).mp compiled.1.1.2, compiled.1.2, compiled.2⟩

/-- Construction law: the literal production-support facts inhabit the compiled domain. -/
theorem productionFullyCompiled_eq_true_of {mol : RawMolecule} {state : OccurrenceAuxState}
    {fuel : Nat} {cursor : CanonicalRerootCursor}
    (terminal : cursorTerminal mol cursor = true)
    (acyclic : mol.atomLiesInCycle fuel cursor.node.atom = false)
    (label : (mol.canonicalRule1aLabel? cursor.node).isSome = true)
    (silent : (state.factAt? cursor.node).isNone = true) :
    productionFullyCompiled mol state fuel cursor = true := by
  unfold productionFullyCompiled
  rw [terminal, bool_not_eq_true_of _ acyclic, label, silent]
  rfl

/-- Complete characterization of the compiled domain by literal production selectors. -/
theorem productionFullyCompiled_iff {mol : RawMolecule} {state : OccurrenceAuxState}
    {fuel : Nat} {cursor : CanonicalRerootCursor} :
    productionFullyCompiled mol state fuel cursor = true ↔
      (cursorTerminal mol cursor = true ∧
        mol.atomLiesInCycle fuel cursor.node.atom = false ∧
        (mol.canonicalRule1aLabel? cursor.node).isSome = true ∧
        (state.factAt? cursor.node).isNone = true) :=
  ⟨productionFullyCompiled_spec, fun facts =>
    productionFullyCompiled_eq_true_of facts.1 facts.2.1 facts.2.2.1 facts.2.2.2⟩

/-- Cap-independence of the compiled domain: a compiled terminal cursor has an empty child sphere,
so no compiled traversal can ever reach `RawMolecule.defaultBranchWidthCap`. -/
theorem productionFullyCompiled_children_eq_nil {mol : RawMolecule} {state : OccurrenceAuxState}
    {fuel : Nat} {cursor : CanonicalRerootCursor}
    (compiled : productionFullyCompiled mol state fuel cursor = true) :
    cursor.children mol = [] :=
  cursor_children_eq_nil_of_terminal mol cursor (productionFullyCompiled_spec compiled).1

/-! ## Pair success and reverse success from literal support -/

/-- Pairwise production success on the compiled domain, derived from the proved production theorem
rather than assumed.  Only the unary supports of the two operands are used. -/
theorem pair_success_of_compiled {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {left right : CanonicalRerootCursor}
    (leftCompiled : productionFullyCompiled mol state fuel left = true)
    (rightCompiled : productionFullyCompiled mol state fuel right = true) :
    ∃ comparison, compareOccurrenceBranches? mol state fuel left right = some comparison := by
  have leftFacts := productionFullyCompiled_spec leftCompiled
  have rightFacts := productionFullyCompiled_spec rightCompiled
  rcases (option_isSome_eq_true_iff (mol.canonicalRule1aLabel? left.node)).mp
      leftFacts.2.2.1 with ⟨leftLabel, leftLabelEq⟩
  rcases (option_isSome_eq_true_iff (mol.canonicalRule1aLabel? right.node)).mp
      rightFacts.2.2.1 with ⟨rightLabel, rightLabelEq⟩
  rcases compareOccurrenceBranches?_terminal_supported_silent_of_left_acyclic mol state fuel
      left right leftFacts.1 rightFacts.1 leftFacts.2.1
      ⟨leftLabel, leftLabelEq⟩ ⟨rightLabel, rightLabelEq⟩
      ((option_isNone_eq_true_iff (state.factAt? left.node)).mp leftFacts.2.2.2)
      ((option_isNone_eq_true_iff (state.factAt? right.node)).mp rightFacts.2.2.2) with
    ⟨ordering, _, success⟩
  exact ⟨{ ordering := ordering }, success⟩

/-- Reverse success on the compiled domain, derived from the *unary* supports of both operands.
This does not use the forward result: it is a second application of the production terminal theorem
with the arguments exchanged. -/
theorem compiledPair_reverse_success {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {left right : CanonicalRerootCursor}
    (leftCompiled : productionFullyCompiled mol state fuel left = true)
    (rightCompiled : productionFullyCompiled mol state fuel right = true) :
    ∃ comparison, compareOccurrenceBranches? mol state fuel right left = some comparison :=
  pair_success_of_compiled rightCompiled leftCompiled

/-! ## The concrete `UnaryDomainTotalOccurrenceOrderingAPI` instance -/

/-- Unary compiler: it returns the lawful fail-closed projected key for compiled cursors and refuses
otherwise.  The domain tag is `Unit`, so same-domain equality is definitionally true and cannot hide
a pair-completeness assumption. -/
def productionUnaryCompile? (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (cursor : CanonicalRerootCursor) :
    Option (Unit × FailClosedOccurrenceBranchProjectedKey) :=
  if productionFullyCompiled mol state fuel cursor = true then
    some ((), buildFailClosedOccurrenceBranchProjectedKey mol state fuel cursor)
  else
    none

theorem productionUnaryCompile?_eq_some_iff {mol : RawMolecule} {state : OccurrenceAuxState}
    {fuel : Nat} {cursor : CanonicalRerootCursor} {domain : Unit}
    {key : FailClosedOccurrenceBranchProjectedKey} :
    productionUnaryCompile? mol state fuel cursor = some (domain, key) ↔
      productionFullyCompiled mol state fuel cursor = true ∧
        some ((), buildFailClosedOccurrenceBranchProjectedKey mol state fuel cursor) =
          some (domain, key) := by
  by_cases h : productionFullyCompiled mol state fuel cursor = true
  · have hsome : productionUnaryCompile? mol state fuel cursor =
        some ((), buildFailClosedOccurrenceBranchProjectedKey mol state fuel cursor) := by
      unfold productionUnaryCompile?
      rw [if_pos h]
    rw [hsome, h]
    simp
  · have hnone : productionUnaryCompile? mol state fuel cursor = none := by
      unfold productionUnaryCompile?
      rw [if_neg h]
    have hfalse : productionFullyCompiled mol state fuel cursor = false :=
      Bool.eq_false_of_not_eq_true h
    rw [hnone, hfalse]
    simp

theorem productionFullyCompiled_of_compile?_eq_some {mol : RawMolecule}
    {state : OccurrenceAuxState} {fuel : Nat} {cursor : CanonicalRerootCursor}
    {domain : Unit} {key : FailClosedOccurrenceBranchProjectedKey}
    (compiled : productionUnaryCompile? mol state fuel cursor = some (domain, key)) :
    productionFullyCompiled mol state fuel cursor = true :=
  (productionUnaryCompile?_eq_some_iff.mp compiled).1

theorem compile?_eq_some_of_compiled {mol : RawMolecule} {state : OccurrenceAuxState}
    {fuel : Nat} {cursor : CanonicalRerootCursor}
    (compiled : productionFullyCompiled mol state fuel cursor = true) :
    productionUnaryCompile? mol state fuel cursor =
      some ((), buildFailClosedOccurrenceBranchProjectedKey mol state fuel cursor) :=
  (productionUnaryCompile?_eq_some_iff.mpr ⟨compiled, rfl⟩)

/-- The concrete unary production occurrence-ordering domain.  Its key API is the certified
fail-closed projected key; its compiler is the literal unary selector; and `pair_complete` is
*derived* from the production terminal theorem through `pair_success_of_compiled`. -/
def productionUnaryDomainAPI (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat) :
    UnaryDomainTotalOccurrenceOrderingAPI mol state fuel where
  toSuccessfulOccurrenceOrderingKeyAPI := failClosedOccurrenceOrderingAPI mol state fuel
  Domain := Unit
  compile? := productionUnaryCompile? mol state fuel
  compile_key := by
    intro cursor domain key compiled
    have keyEq : productionUnaryCompile? mol state fuel cursor = some (domain, key) := compiled
    have hpair :
        ((), buildFailClosedOccurrenceBranchProjectedKey mol state fuel cursor) = (domain, key) :=
      Option.some.inj (productionUnaryCompile?_eq_some_iff.mp keyEq).2
    exact (congrArg Prod.snd hpair).symm
  pair_complete := by
    intro left right domain leftKey rightKey leftCompiled rightCompiled
    have leftEq : productionUnaryCompile? mol state fuel left = some (domain, leftKey) := leftCompiled
    have rightEq : productionUnaryCompile? mol state fuel right = some (domain, rightKey) :=
      rightCompiled
    exact pair_success_of_compiled
      (productionFullyCompiled_of_compile?_eq_some leftEq)
      (productionFullyCompiled_of_compile?_eq_some rightEq)

theorem productionUnaryDomainAPI_compile?_of_compiled {mol : RawMolecule}
    {state : OccurrenceAuxState} {fuel : Nat} {cursor : CanonicalRerootCursor}
    (compiled : productionFullyCompiled mol state fuel cursor = true) :
    (productionUnaryDomainAPI mol state fuel).compile? cursor =
      some ((), (failClosedOccurrenceOrderingAPI mol state fuel).build cursor) := by
  show productionUnaryCompile? mol state fuel cursor =
    some ((), buildFailClosedOccurrenceBranchProjectedKey mol state fuel cursor)
  exact compile?_eq_some_of_compiled compiled

/-! ## Connection to the production structural frame -/

/-- Every root of a `TerminalAcyclicCIPFrame` is compiled.  The unary support facts are read off
the frame, so the domain is inhabited on a chemically structural class without an all-pairs
certificate. -/
theorem compiled_of_terminalFrame {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : TerminalAcyclicCIPFrame (mol := mol) state fuel node roots)
    {cursor : CanonicalRerootCursor} (member : cursor ∈ roots) :
    productionFullyCompiled mol state fuel cursor = true :=
  productionFullyCompiled_eq_true_of
    (frame.terminal cursor member)
    (frame.acyclic cursor member)
    ((option_isSome_eq_true_iff _).mpr (frame.rule1a_supported cursor member))
    ((option_isNone_eq_true_iff _).mpr (frame.descriptor_silent cursor member))

/-- Two-success endpoint closure routed through the concrete unary-domain API.  Endpoint existence
is obtained from the domain's derived `pair_complete` (not an assumed law), and the endpoint value
from the intrinsic three-success ordering theorem.  No all-pairs comparison certificate appears. -/
theorem terminalFrame_endpoint_via_unaryDomainAPI
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : TerminalAcyclicCIPFrame (mol := mol) state fuel node roots)
    {left middle right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (_middle_mem : middle ∈ roots) (right_mem : right ∈ roots)
    {leftMiddle middleRight : OccurrenceComparison} {composed : Ordering}
    (leftMiddleEq : compareOccurrenceBranches? mol state fuel left middle = some leftMiddle)
    (middleRightEq : compareOccurrenceBranches? mol state fuel middle right = some middleRight)
    (composition :
      composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering = some composed) :
    ∃ leftRight,
      compareOccurrenceBranches? mol state fuel left right = some leftRight ∧
        leftRight.ordering = composed := by
  have leftCompiled := productionUnaryDomainAPI_compile?_of_compiled
    (compiled_of_terminalFrame frame left_mem)
  have rightCompiled := productionUnaryDomainAPI_compile?_of_compiled
    (compiled_of_terminalFrame frame right_mem)
  exact UnaryDomainTotalOccurrenceOrderingAPI.endpoint_exists_and_eq_composed
    (productionUnaryDomainAPI mol state fuel)
    leftCompiled rightCompiled leftMiddleEq middleRightEq composition

/-! ## A closed finite counterexample to `SuccessCompilesInOneDomain`

The molecule is a tetrahedral carbon bonded to four one-carbon chains whose unique forward children
are F, Cl, Br and I.  Every chain root is nonterminal, so it fails the terminal conjunct of
`productionFullyCompiled`, yet production comparison succeeds on such roots (the bounded acyclic
linear theorem).  Hence the strongest success-closure law is false for this compiler, and the
witness is honestly restricted to the compiled domain. -/

namespace RestrictedDomainCounterexample

def center : AtomSpec :=
  { AtomSpec.aliphatic Element.C with tetrahedral? := some .clockwise }

def carbon : AtomSpec := AtomSpec.aliphatic Element.C

def molecule : RawMolecule where
  atoms := [center, carbon, AtomSpec.aliphatic Element.F,
    carbon, AtomSpec.aliphatic Element.Cl,
    carbon, AtomSpec.aliphatic Element.Br,
    carbon, AtomSpec.aliphatic Element.I]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 1, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single },
      { source := 3, target := 4, kind := .single },
      { source := 0, target := 5, kind := .single },
      { source := 5, target := 6, kind := .single },
      { source := 0, target := 7, kind := .single },
      { source := 7, target := 8, kind := .single } ]

def node : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 0, history := [0], provenance := .realAtom }

def root (atom : Nat) : CanonicalRerootCursor :=
  { node := RawMolecule.canonicalRoot 0 atom, previous? := some node }

def child (rootAtom childAtom : Nat) : CanonicalRerootCursor :=
  { node :=
      { atom := childAtom, parent := rootAtom, history := [childAtom, rootAtom, 0],
        provenance := .realAtom }
    previous? := some (root rootAtom).node }

def supportedRoot (rootAtom childAtom : Nat)
    (rootLabel : ∃ label, molecule.canonicalRule1aLabel? (root rootAtom).node = some label)
    (childLabel : ∃ label,
      molecule.canonicalRule1aLabel? (child rootAtom childAtom).node = some label)
    (children : (root rootAtom).children molecule = [child rootAtom childAtom])
    (childTerminal : cursorTerminal molecule (child rootAtom childAtom) = true)
    (rootAcyclic : molecule.atomLiesInCycle 2 (root rootAtom).node.atom = false)
    (childAcyclic : molecule.atomLiesInCycle 2 (child rootAtom childAtom).node.atom = false) :
    AcyclicLinearCursorSupport molecule 2 (root rootAtom) :=
  { linear := .step 1 (root rootAtom) (child rootAtom childAtom) rootLabel children
      (.terminal 1 (child rootAtom childAtom) childLabel childTerminal)
    acyclic := .step (root rootAtom) (child rootAtom childAtom) rootAcyclic children
      (.terminal (child rootAtom childAtom) childAcyclic childTerminal) }

def support1 : AcyclicLinearCursorSupport molecule 2 (root 1) := by
  apply supportedRoot 1 2
  all_goals first | decide | simp [root, child, RawMolecule.canonicalRoot,
    RawMolecule.canonicalRule1aLabel?]

/-- The first-chain root is genuinely nonterminal, so it is not compiled. -/
theorem root_one_nonterminal : cursorTerminal molecule (root 1) = false := by decide

theorem root_one_not_compiled :
    productionFullyCompiled molecule [] 2 (root 1) = false := by
  simp [productionFullyCompiled, root_one_nonterminal]

/-- Its unique forward child is terminal and therefore compiled, so the domain is nonempty. -/
theorem child_two_compiled :
    productionFullyCompiled molecule [] 2 (child 1 2) = true := by
  apply productionFullyCompiled_eq_true_of <;> decide

/-- The production executable succeeds on the nonterminal root pair. -/
theorem success_with_uncompiled_operand :
    ∃ comparison,
      compareOccurrenceBranches? molecule [] 2 (root 1) (root 1) = some comparison := by
  rcases compareOccurrenceBranches?_acyclic_linear_empty_eq_raw molecule 2 (root 1) (root 1)
      support1 support1 with ⟨ordering, _, success⟩
  exact ⟨{ ordering := ordering }, success⟩

end RestrictedDomainCounterexample

/-- The closed universality law `SuccessCompilesInOneDomain` is false for the concrete unary
compiler: a successful comparison has a nonterminal, uncompiled operand.  This is exactly why the
witness is restricted to the checkable fully compiled domain instead of being totalized. -/
theorem successCompilesInOneDomain_false :
    ¬ UnaryDomainTotalOccurrenceOrderingAPI.SuccessCompilesInOneDomain
        (productionUnaryDomainAPI RestrictedDomainCounterexample.molecule [] 2) := by
  intro closure
  rcases RestrictedDomainCounterexample.success_with_uncompiled_operand with ⟨comparison, success⟩
  rcases closure (RestrictedDomainCounterexample.root 1) (RestrictedDomainCounterexample.root 1)
      comparison success with ⟨domain, leftKey, rightKey, leftCompiled, _rightCompiled⟩
  have compiledFalse :
      productionFullyCompiled RestrictedDomainCounterexample.molecule [] 2
        (RestrictedDomainCounterexample.root 1) = false :=
    RestrictedDomainCounterexample.root_one_not_compiled
  have compiledTrue := productionFullyCompiled_of_compile?_eq_some
    (mol := RestrictedDomainCounterexample.molecule) (state := []) (fuel := 2)
    (cursor := RestrictedDomainCounterexample.root 1) leftCompiled
  rw [compiledFalse] at compiledTrue
  exact Bool.false_ne_true compiledTrue

end TetraStereo.UniversalProof.ProductionOccurrenceDomainWitnessProofs
