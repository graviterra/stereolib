import TetraStereo.OneCenter.CIPAuthoritativeBranchComparator
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.RawMolecule

/-! ## Observation-parameterized Rule-1b core

The width-unbounded comparator reads every Rule-1b distance through one observer
`CanonicalBranchNode → Option ℕ`.  The legacy path above is exactly the specialization at
`rule1bRootDistanceObservation`; a 2013 represented-atom reading lives in a leaf module that
imports this core and supplies its own observer without touching any constructor, stored
provenance, or stored attachment distance.
-/

/-- The legacy Rule-1b observation: the stored root distance of every canonical occurrence.

This observer never fails, so the specialized core propagates exactly the same `none` failures as
the legacy path (excessive bonding number, unsupported Rule-1a labeling, or sibling-ranking
failure). -/
def rule1bRootDistanceObservation (node : CanonicalBranchNode) : Option ℕ :=
  some node.rule1bRootDistance

/-- Root key whose Rule-1b field is supplied by an explicit observation.  Every other field is
identical to `canonicalRootKeyAuthoritative?`. -/
def canonicalRootKeyAuthoritativeWithRule1b? (mol : RawMolecule)
    (observe : CanonicalBranchNode → Option ℕ) (node : CanonicalBranchNode)
    (complete : Bool) : Option CanonicalBranchKey := do
  let rule1a ← mol.canonicalRule1aLabelAuthoritative? node
  let rule1bDistance ← observe node
  some
    { rule1a := [[([], rule1a)]]
      rule1b := [[([], rule1bDistance)]]
      rule2 :=
        let mass :=
          match node.provenance with
          | CanonicalNodeProvenance.realAtom => mol.atomMassAt node.atom
          | _ => 0
        [[([], mass)]]
      realAtoms :=
        match node.provenance with
        | CanonicalNodeProvenance.realAtom => [[([], node.atom)]]
        | _ => [[]]
      sourceNodes := [[([], node)]]
      sourceOccurrences := [([], node)]
      sourceTree? := some (.node node .nil)
      complete := complete }

/-- Compile a finite canonical branch key with an explicit Rule-1b observation.

Child enumeration, sorting, the key comparator, the depth bound, and every `Option` failure are
exactly the legacy ones; only the Rule-1b distance read is parameterized. -/
def buildCanonicalBranchKeyAuthoritativeWithRule1b (mol : RawMolecule)
    (observe : CanonicalBranchNode → Option ℕ) :
    ℕ → CanonicalBranchNode → Option CanonicalBranchKey
  | 0, node => mol.canonicalRootKeyAuthoritativeWithRule1b? observe node (mol.canonicalTerminal node)
  | fuel + 1, node => do
      if mol.canonicalTerminal node then
        mol.canonicalRootKeyAuthoritativeWithRule1b? observe node true
      else
        let children := mol.canonicalChildren node
        if authoritativeChildSlots < children.length then none
        else
          let childKeys ← children.mapM fun child =>
            mol.buildCanonicalBranchKeyAuthoritativeWithRule1b observe fuel child
          let sorted ← sortCanonicalKeys? childKeys
          let root ← mol.canonicalRootKeyAuthoritativeWithRule1b? observe node
            (sorted.all fun child => child.complete)
          some (assembleCanonicalBranchKey root sorted)

/-- Compare two canonical occurrences under one constitutional sequence rule with an explicit
Rule-1b observation.  Rule 1a and Rule 2 are unchanged; Rule 1b reads both distances through the
observer and refuses when the observer does. -/
def compareCanonicalNodeRuleAuthoritativeWithRule1b? (mol : RawMolecule)
    (observe : CanonicalBranchNode → Option ℕ) (rule : CanonicalRuleStage)
    (left right : CanonicalBranchNode) : Option Ordering :=
  match rule with
  | CanonicalRuleStage.rule1a => do
      let leftLabel ← mol.canonicalRule1aLabelAuthoritative? left
      let rightLabel ← mol.canonicalRule1aLabelAuthoritative? right
      some (compareCIPAtomicLabel leftLabel rightLabel)
  | CanonicalRuleStage.rule1b => do
      let leftDistance ← observe left
      let rightDistance ← observe right
      some (if leftDistance < rightDistance then Ordering.gt
        else if rightDistance < leftDistance then Ordering.lt else Ordering.eq)
  | CanonicalRuleStage.rule2 => some (mol.compareCanonicalNodeRule rule left right)

/-- Immediate rule-major node comparison for the observation-parameterized path. -/
def compareCanonicalNodeThroughAuthoritativeWithRule1b? (mol : RawMolecule)
    (observe : CanonicalBranchNode → Option ℕ) (stage : CanonicalRuleStage)
    (left right : CanonicalBranchNode) : Option Ordering := do
  let rule1a ← mol.compareCanonicalNodeRuleAuthoritativeWithRule1b? observe
    CanonicalRuleStage.rule1a left right
  match rule1a with
  | Ordering.lt => some Ordering.lt
  | Ordering.gt => some Ordering.gt
  | Ordering.eq =>
      match stage with
      | CanonicalRuleStage.rule1a => some Ordering.eq
      | CanonicalRuleStage.rule1b =>
          mol.compareCanonicalNodeRuleAuthoritativeWithRule1b? observe
            CanonicalRuleStage.rule1b left right
      | CanonicalRuleStage.rule2 => do
          let rule1b ← mol.compareCanonicalNodeRuleAuthoritativeWithRule1b? observe
            CanonicalRuleStage.rule1b left right
          match rule1b with
          | Ordering.eq =>
              mol.compareCanonicalNodeRuleAuthoritativeWithRule1b? observe
                CanonicalRuleStage.rule2 left right
          | decision => some decision

/-- Recursively ranked children padded to the bonding-number-six positional arity, with an explicit
Rule-1b observation. Padding retains the legacy stored attachment coordinate; observation
selection affects comparison only. -/
def rankedCanonicalChildrenAuthoritativeWithRule1b? (mol : RawMolecule)
    (_observe : CanonicalBranchNode → Option ℕ)
    (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering)
    (node : CanonicalBranchNode) : Option (List CanonicalBranchNode) := do
  let children := mol.canonicalChildren node
  if authoritativeChildSlots < children.length then none
  else
    let sorted ← sortCanonicalBy? before children
    let phantom := mol.canonicalPhantom node.atom (node.rule1bRootDistance + 1)
    some (sorted ++ List.replicate (authoritativeChildSlots - sorted.length) phantom)

/-- Expand one complete paired sphere without a frontier-width cutoff, observation-parameterized. -/
def nextCanonicalPairsAuthoritativeWithRule1b? (mol : RawMolecule)
    (observe : CanonicalBranchNode → Option ℕ)
    (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering) :
    List (CanonicalBranchNode × CanonicalBranchNode) →
      Option (List (CanonicalBranchNode × CanonicalBranchNode))
  | [] => some []
  | pair :: pairs => do
      let rest ← mol.nextCanonicalPairsAuthoritativeWithRule1b? observe before pairs
      if mol.canonicalTerminal pair.1 && mol.canonicalTerminal pair.2 then
        some rest
      else
        let left ← mol.rankedCanonicalChildrenAuthoritativeWithRule1b? observe before pair.1
        let right ← mol.rankedCanonicalChildrenAuthoritativeWithRule1b? observe before pair.2
        some (left.zip right ++ rest)

/-- Compare all already parent-ranked nodes in one sphere, observation-parameterized. -/
def compareCanonicalPairLabelsAuthoritativeWithRule1b? (mol : RawMolecule)
    (observe : CanonicalBranchNode → Option ℕ) (rule : CanonicalRuleStage) :
    List (CanonicalBranchNode × CanonicalBranchNode) → Option Ordering
  | [] => some Ordering.eq
  | pair :: pairs =>
      match mol.compareCanonicalNodeRuleAuthoritativeWithRule1b? observe rule pair.1 pair.2 with
      | none => none
      | some Ordering.eq => mol.compareCanonicalPairLabelsAuthoritativeWithRule1b? observe rule pairs
      | some decision => some decision

/-- Compare one rule sphere-by-sphere with no arbitrary width cap, observation-parameterized. -/
def compareCanonicalRuleAuthoritativeWithRule1b? (mol : RawMolecule)
    (observe : CanonicalBranchNode → Option ℕ)
    (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering)
    (rule : CanonicalRuleStage) :
    ℕ → List (CanonicalBranchNode × CanonicalBranchNode) → Option Ordering
  | 0, pairs =>
      match mol.compareCanonicalPairLabelsAuthoritativeWithRule1b? observe rule pairs with
      | none => none
      | some Ordering.eq =>
          match mol.nextCanonicalPairsAuthoritativeWithRule1b? observe before pairs with
          | some [] => some Ordering.eq
          | _ => none
      | some decision => some decision
  | fuel + 1, pairs =>
      match mol.compareCanonicalPairLabelsAuthoritativeWithRule1b? observe rule pairs with
      | none => none
      | some Ordering.eq =>
          match mol.nextCanonicalPairsAuthoritativeWithRule1b? observe before pairs with
          | none => none
          | some [] => some Ordering.eq
          | some next =>
              mol.compareCanonicalRuleAuthoritativeWithRule1b? observe before rule fuel next
      | some decision => some decision

/-- Parent-refined comparison through Rules 1a, 1b, and 2 with no sphere-width cutoff,
observation-parameterized. -/
def compareCanonicalBranchAuthoritativeAtWithRule1b? (mol : RawMolecule)
    (observe : CanonicalBranchNode → Option ℕ) :
    ℕ → CanonicalRuleStage → CanonicalBranchNode → CanonicalBranchNode → Option Ordering
  | 0, stage, left, right =>
      mol.compareCanonicalNodeThroughAuthoritativeWithRule1b? observe stage left right
  | fuel + 1, stage, left, right =>
      let before := mol.compareCanonicalBranchAuthoritativeAtWithRule1b? observe fuel stage
      let compareRule := fun rule =>
        mol.compareCanonicalRuleAuthoritativeWithRule1b? observe before rule (fuel + 1) [(left, right)]
      match compareRule CanonicalRuleStage.rule1a with
      | none => none
      | some Ordering.lt => some Ordering.lt
      | some Ordering.gt => some Ordering.gt
      | some Ordering.eq =>
          match stage with
          | CanonicalRuleStage.rule1a => some Ordering.eq
          | CanonicalRuleStage.rule1b => compareRule CanonicalRuleStage.rule1b
          | CanonicalRuleStage.rule2 =>
              match compareRule CanonicalRuleStage.rule1b with
              | some Ordering.eq => compareRule CanonicalRuleStage.rule2
              | decision => decision

/-- Exact constitutional ligand comparison with an explicit Rule-1b observation. -/
def compareBranchesAuthoritativeWithRule1b? (mol : RawMolecule)
    (observe : CanonicalBranchNode → Option ℕ) (center left right : ℕ) : Option Ordering :=
  mol.compareCanonicalBranchAuthoritativeAtWithRule1b? observe (mol.atomCount + 1)
    CanonicalRuleStage.rule2 (canonicalRoot center left) (canonicalRoot center right)

/-! ## Legacy specialization equalities

Each legacy entry point is exactly the observation-parameterized core specialized to
`rule1bRootDistanceObservation`.  The legacy bodies are kept byte-for-byte so that downstream
proofs unfolding them do not change. -/

private theorem listMapM_congr_option {α β : Type*} (f g : α → Option β) :
    ∀ (values : List α), (∀ value, value ∈ values → f value = g value) →
      values.mapM f = values.mapM g
  | [], _ => by simp
  | value :: values, pointwise => by
      have head : f value = g value := pointwise value (by simp)
      have tail : values.mapM f = values.mapM g :=
        listMapM_congr_option f g values (fun tailValue present =>
          pointwise tailValue (by simp [present]))
      simp [head, tail]

theorem canonicalRootKeyAuthoritative?_eq_observation (mol : RawMolecule)
    (node : CanonicalBranchNode) (complete : Bool) :
    mol.canonicalRootKeyAuthoritative? node complete =
      mol.canonicalRootKeyAuthoritativeWithRule1b? rule1bRootDistanceObservation node complete := by
  simp [canonicalRootKeyAuthoritative?, canonicalRootKeyAuthoritativeWithRule1b?,
    rule1bRootDistanceObservation, CanonicalBranchNode.rule1bCode]
  rfl

theorem buildCanonicalBranchKeyAuthoritative_eq_observation (mol : RawMolecule) :
    ∀ (fuel : ℕ) (node : CanonicalBranchNode),
      mol.buildCanonicalBranchKeyAuthoritative fuel node =
        mol.buildCanonicalBranchKeyAuthoritativeWithRule1b rule1bRootDistanceObservation fuel node := by
  intro fuel
  induction fuel with
  | zero =>
      intro node
      unfold buildCanonicalBranchKeyAuthoritative buildCanonicalBranchKeyAuthoritativeWithRule1b
      exact canonicalRootKeyAuthoritative?_eq_observation mol node (mol.canonicalTerminal node)
  | succ fuel ih =>
      intro node
      unfold buildCanonicalBranchKeyAuthoritative buildCanonicalBranchKeyAuthoritativeWithRule1b
      by_cases terminal : mol.canonicalTerminal node = true
      · simp [terminal, canonicalRootKeyAuthoritative?_eq_observation]
      · simp only [if_neg terminal]
        let children := mol.canonicalChildren node
        by_cases tooWide : authoritativeChildSlots < children.length
        · simp [children, tooWide]
        · rw [if_neg tooWide]
          have hmap : children.mapM (fun child => mol.buildCanonicalBranchKeyAuthoritative fuel child) =
              children.mapM (fun child => mol.buildCanonicalBranchKeyAuthoritativeWithRule1b
                rule1bRootDistanceObservation fuel child) := by
            exact listMapM_congr_option
              (fun child => mol.buildCanonicalBranchKeyAuthoritative fuel child)
              (fun child => mol.buildCanonicalBranchKeyAuthoritativeWithRule1b
                rule1bRootDistanceObservation fuel child)
              children (fun child _ => ih child)
          simp [children, hmap, tooWide, canonicalRootKeyAuthoritative?_eq_observation]

theorem compareCanonicalNodeRuleAuthoritative?_eq_observation (mol : RawMolecule)
    (rule : CanonicalRuleStage) (left right : CanonicalBranchNode) :
    mol.compareCanonicalNodeRuleAuthoritative? rule left right =
      mol.compareCanonicalNodeRuleAuthoritativeWithRule1b? rule1bRootDistanceObservation
        rule left right := by
  cases rule <;>
    simp [compareCanonicalNodeRuleAuthoritative?, compareCanonicalNodeRuleAuthoritativeWithRule1b?,
      rule1bRootDistanceObservation, compareCanonicalNodeRule]

theorem compareCanonicalNodeThroughAuthoritative?_eq_observation (mol : RawMolecule)
    (stage : CanonicalRuleStage) (left right : CanonicalBranchNode) :
    mol.compareCanonicalNodeThroughAuthoritative? stage left right =
      mol.compareCanonicalNodeThroughAuthoritativeWithRule1b? rule1bRootDistanceObservation
        stage left right := by
  cases stage <;>
    simp [compareCanonicalNodeThroughAuthoritative?,
      compareCanonicalNodeThroughAuthoritativeWithRule1b?,
      compareCanonicalNodeRuleAuthoritative?_eq_observation] <;>
    rfl

theorem rankedCanonicalChildrenAuthoritative?_eq_observation (mol : RawMolecule)
    (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering)
    (node : CanonicalBranchNode) :
    mol.rankedCanonicalChildrenAuthoritative? before node =
      mol.rankedCanonicalChildrenAuthoritativeWithRule1b? rule1bRootDistanceObservation
        before node := by
  simp [rankedCanonicalChildrenAuthoritative?,
    rankedCanonicalChildrenAuthoritativeWithRule1b?]

theorem nextCanonicalPairsAuthoritative?_eq_observation (mol : RawMolecule)
    (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering) :
    ∀ (pairs : List (CanonicalBranchNode × CanonicalBranchNode)),
      mol.nextCanonicalPairsAuthoritative? before pairs =
        mol.nextCanonicalPairsAuthoritativeWithRule1b? rule1bRootDistanceObservation before pairs := by
  intro pairs
  induction pairs with
  | nil =>
      unfold nextCanonicalPairsAuthoritative? nextCanonicalPairsAuthoritativeWithRule1b?
      rfl
  | cons pair pairs ih =>
      unfold nextCanonicalPairsAuthoritative? nextCanonicalPairsAuthoritativeWithRule1b?
      simp [ih, rankedCanonicalChildrenAuthoritative?_eq_observation]

theorem compareCanonicalPairLabelsAuthoritative?_eq_observation (mol : RawMolecule)
    (rule : CanonicalRuleStage) :
    ∀ (pairs : List (CanonicalBranchNode × CanonicalBranchNode)),
      mol.compareCanonicalPairLabelsAuthoritative? rule pairs =
        mol.compareCanonicalPairLabelsAuthoritativeWithRule1b? rule1bRootDistanceObservation
          rule pairs := by
  intro pairs
  induction pairs with
  | nil =>
      unfold compareCanonicalPairLabelsAuthoritative?
        compareCanonicalPairLabelsAuthoritativeWithRule1b?
      rfl
  | cons pair pairs ih =>
      unfold compareCanonicalPairLabelsAuthoritative?
        compareCanonicalPairLabelsAuthoritativeWithRule1b?
      simp [ih, compareCanonicalNodeRuleAuthoritative?_eq_observation]
      rfl

theorem compareCanonicalRuleAuthoritative?_eq_observation (mol : RawMolecule)
    (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering)
    (rule : CanonicalRuleStage) :
    ∀ (fuel : ℕ) (pairs : List (CanonicalBranchNode × CanonicalBranchNode)),
      mol.compareCanonicalRuleAuthoritative? before rule fuel pairs =
        mol.compareCanonicalRuleAuthoritativeWithRule1b? rule1bRootDistanceObservation
          before rule fuel pairs := by
  intro fuel
  induction fuel with
  | zero =>
      intro pairs
      unfold compareCanonicalRuleAuthoritative? compareCanonicalRuleAuthoritativeWithRule1b?
      simp [compareCanonicalPairLabelsAuthoritative?_eq_observation,
        nextCanonicalPairsAuthoritative?_eq_observation]
      rfl
  | succ fuel ih =>
      intro pairs
      unfold compareCanonicalRuleAuthoritative? compareCanonicalRuleAuthoritativeWithRule1b?
      simp [compareCanonicalPairLabelsAuthoritative?_eq_observation,
        nextCanonicalPairsAuthoritative?_eq_observation, ih]
      rfl

theorem compareCanonicalBranchAuthoritativeAt?_eq_observation (mol : RawMolecule) :
    ∀ (fuel : ℕ) (stage : CanonicalRuleStage) (left right : CanonicalBranchNode),
      mol.compareCanonicalBranchAuthoritativeAt? fuel stage left right =
        mol.compareCanonicalBranchAuthoritativeAtWithRule1b? rule1bRootDistanceObservation
          fuel stage left right := by
  intro fuel
  induction fuel with
  | zero =>
      intro stage left right
      unfold compareCanonicalBranchAuthoritativeAt?
        compareCanonicalBranchAuthoritativeAtWithRule1b?
      exact compareCanonicalNodeThroughAuthoritative?_eq_observation mol stage left right
  | succ fuel ih =>
      intro stage left right
      unfold compareCanonicalBranchAuthoritativeAt?
        compareCanonicalBranchAuthoritativeAtWithRule1b?
      have hbefore :
          mol.compareCanonicalBranchAuthoritativeAt? fuel stage =
            mol.compareCanonicalBranchAuthoritativeAtWithRule1b?
              rule1bRootDistanceObservation fuel stage := by
        funext l r
        exact ih stage l r
      simp [hbefore, compareCanonicalRuleAuthoritative?_eq_observation]
      rfl

theorem compareBranchesAuthoritative?_eq_observation (mol : RawMolecule)
    (center left right : ℕ) :
    mol.compareBranchesAuthoritative? center left right =
      mol.compareBranchesAuthoritativeWithRule1b? rule1bRootDistanceObservation center left right := by
  simp [compareBranchesAuthoritative?, compareBranchesAuthoritativeWithRule1b?,
    compareCanonicalBranchAuthoritativeAt?_eq_observation]

end TetraStereo.OneCenter.RawMolecule

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.RawMolecule.canonicalRootKeyAuthoritative?_eq_observation
assert_kernel_only TetraStereo.OneCenter.RawMolecule.buildCanonicalBranchKeyAuthoritative_eq_observation
assert_kernel_only TetraStereo.OneCenter.RawMolecule.compareCanonicalNodeRuleAuthoritative?_eq_observation
assert_kernel_only TetraStereo.OneCenter.RawMolecule.compareCanonicalNodeThroughAuthoritative?_eq_observation
assert_kernel_only TetraStereo.OneCenter.RawMolecule.rankedCanonicalChildrenAuthoritative?_eq_observation
assert_kernel_only TetraStereo.OneCenter.RawMolecule.nextCanonicalPairsAuthoritative?_eq_observation
assert_kernel_only TetraStereo.OneCenter.RawMolecule.compareCanonicalPairLabelsAuthoritative?_eq_observation
assert_kernel_only TetraStereo.OneCenter.RawMolecule.compareCanonicalRuleAuthoritative?_eq_observation
assert_kernel_only TetraStereo.OneCenter.RawMolecule.compareCanonicalBranchAuthoritativeAt?_eq_observation
assert_kernel_only TetraStereo.OneCenter.RawMolecule.compareBranchesAuthoritative?_eq_observation
