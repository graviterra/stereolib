import TetraStereo.OneCenter.BranchSphereKey

set_option autoImplicit false

namespace TetraStereo.OneCenter.RawMolecule

/-!
# Width-unbounded constitutional CIP comparison

The ordinary production path retains a frontier cap for predictable resource use.  That cap cannot
appear in a completeness theorem.  This module supplies a separate exact path: recursion is bounded
only by molecular depth, while every sphere is allowed to grow to its actual finite size.

IUPAC P-92 states the CIP system for bonding numbers through six.  After removing the incoming
parent occurrence, five positional child slots suffice.  Multiple-bond and ring duplicates remain
terminal canonical occurrences and occupy those same slots.
-/

/-- Maximum number of child occurrences below one incoming ligand occurrence in the supported
bonding-number-six domain. -/
def authoritativeChildSlots : ℕ := 5

/-! ## Exact Rule-1a labels for the authoritative comparator -/

/-- Exact maximum-matching average for the localized mancude component containing a written
multiple-bond duplicate.

This is the same computation used by `generalMancudeRule1aLabel?`.  Termination is witnessed by the
finite component edge list: every recursive branch consumes its first remaining edge. -/
def generalMancudeRule1aLabelAuthoritative? (mol : RawMolecule)
    (attached duplicated : ℕ) : Option CIPAtomicLabel :=
  let allEdges := mol.localizedMancudeEdges
  let vertices := edgeComponent allEdges (allEdges.length + 1) [attached] [attached]
  let edges := allEdges.filter fun edge => vertices.contains edge.1 && vertices.contains edge.2
  if !(vertices.contains duplicated) || edges.isEmpty then none
  else do
    let stats ← mol.mancudeMatchingStats attached (edges.length + 1) edges
    let writtenDoubleCount :=
      (edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2).length
    if stats.size != writtenDoubleCount || stats.count == 0 then none
    else some { numerator := stats.partnerZSum, denominator := stats.count }

/-- Exact Rule-1a duplicate label with no resonance-component size cutoff.  Closed simple cycles
retain their proved formula; every other localized component is averaged over all of its
maximum-cardinality Kekulé matchings. -/
def mancudeRule1aLabelAuthoritative? (mol : RawMolecule) (attached duplicated : ℕ) :
    Option CIPAtomicLabel :=
  if !containsUndirectedEdge mol.localizedMancudeEdges attached duplicated then
    some { numerator := mol.atomZAt duplicated, denominator := 1 }
  else
    match mol.simpleMancudeCycle? attached duplicated with
    | some (cycle, alternate) => some (mol.simpleMancudeCycleLabel duplicated alternate cycle)
    | none => mol.generalMancudeRule1aLabelAuthoritative? attached duplicated

/-- Rule-1a node label used by the authoritative constitutional comparator. -/
def canonicalRule1aLabelAuthoritative? (mol : RawMolecule) (node : CanonicalBranchNode) :
    Option CIPAtomicLabel :=
  match node.provenance with
  | CanonicalNodeProvenance.phantom _ => some { numerator := 0, denominator := 1 }
  | CanonicalNodeProvenance.multipleBondDuplicate _ =>
      mol.mancudeRule1aLabelAuthoritative? node.parent node.atom
  | _ => some { numerator := mol.atomZAt node.atom, denominator := 1 }

/-- Root key whose Rule-1a field is supplied by the uncapped authoritative labeler. -/
def canonicalRootKeyAuthoritative? (mol : RawMolecule) (node : CanonicalBranchNode)
    (complete : Bool) : Option CanonicalBranchKey := do
  let rule1a ← mol.canonicalRule1aLabelAuthoritative? node
  some
    { rule1a := [[([], rule1a)]]
      rule1b := [[([], node.rule1bCode)]]
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

/-- Compile a finite canonical branch key without a total-node budget or a three-child restriction.

The only local arity check is the chemically stated bonding-number-six bound.  At the public depth
`atomCount + 1`, simple real-atom paths are exhausted and all duplicate nodes are terminal. -/
def buildCanonicalBranchKeyAuthoritative (mol : RawMolecule) :
    ℕ → CanonicalBranchNode → Option CanonicalBranchKey
  | 0, node => mol.canonicalRootKeyAuthoritative? node (mol.canonicalTerminal node)
  | fuel + 1, node => do
      if mol.canonicalTerminal node then
        mol.canonicalRootKeyAuthoritative? node true
      else
        let children := mol.canonicalChildren node
        if authoritativeChildSlots < children.length then none
        else
          let childKeys ← children.mapM fun child =>
            mol.buildCanonicalBranchKeyAuthoritative fuel child
          let sorted ← sortCanonicalKeys? childKeys
          let root ← mol.canonicalRootKeyAuthoritative? node
            (sorted.all fun child => child.complete)
          some (assembleCanonicalBranchKey root sorted)

/-- Compare two canonical occurrences under one constitutional sequence rule, using the uncapped
Rule-1a labeler where applicable. -/
def compareCanonicalNodeRuleAuthoritative? (mol : RawMolecule) (rule : CanonicalRuleStage)
    (left right : CanonicalBranchNode) : Option Ordering :=
  match rule with
  | CanonicalRuleStage.rule1a => do
      let leftLabel ← mol.canonicalRule1aLabelAuthoritative? left
      let rightLabel ← mol.canonicalRule1aLabelAuthoritative? right
      some (compareCIPAtomicLabel leftLabel rightLabel)
  | CanonicalRuleStage.rule1b
  | CanonicalRuleStage.rule2 => some (mol.compareCanonicalNodeRule rule left right)

/-- Immediate rule-major node comparison for the authoritative path. -/
def compareCanonicalNodeThroughAuthoritative? (mol : RawMolecule) (stage : CanonicalRuleStage)
    (left right : CanonicalBranchNode) : Option Ordering := do
  let rule1a ← mol.compareCanonicalNodeRuleAuthoritative? CanonicalRuleStage.rule1a left right
  match rule1a with
  | Ordering.lt => some Ordering.lt
  | Ordering.gt => some Ordering.gt
  | Ordering.eq =>
      match stage with
      | CanonicalRuleStage.rule1a => some Ordering.eq
      | CanonicalRuleStage.rule1b =>
          mol.compareCanonicalNodeRuleAuthoritative? CanonicalRuleStage.rule1b left right
      | CanonicalRuleStage.rule2 => do
          let rule1b ←
            mol.compareCanonicalNodeRuleAuthoritative? CanonicalRuleStage.rule1b left right
          match rule1b with
          | Ordering.eq =>
              mol.compareCanonicalNodeRuleAuthoritative? CanonicalRuleStage.rule2 left right
          | decision => some decision

/-- Recursively ranked children padded to the bonding-number-six positional arity.

Unlike `rankedCanonicalChildren?`, this is not restricted to the tetravalent three-child fast-path
domain. -/
def rankedCanonicalChildrenAuthoritative? (mol : RawMolecule)
    (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering)
    (node : CanonicalBranchNode) : Option (List CanonicalBranchNode) := do
  let children := mol.canonicalChildren node
  if authoritativeChildSlots < children.length then none
  else
    let sorted ← sortCanonicalBy? before children
    let phantom := mol.canonicalPhantom node.atom (node.rule1bRootDistance + 1)
    some (sorted ++ List.replicate (authoritativeChildSlots - sorted.length) phantom)

/-- Expand one complete paired sphere without a frontier-width cutoff. -/
def nextCanonicalPairsAuthoritative? (mol : RawMolecule)
    (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering) :
    List (CanonicalBranchNode × CanonicalBranchNode) →
      Option (List (CanonicalBranchNode × CanonicalBranchNode))
  | [] => some []
  | pair :: pairs => do
      let rest ← mol.nextCanonicalPairsAuthoritative? before pairs
      if mol.canonicalTerminal pair.1 && mol.canonicalTerminal pair.2 then
        some rest
      else
        let left ← mol.rankedCanonicalChildrenAuthoritative? before pair.1
        let right ← mol.rankedCanonicalChildrenAuthoritative? before pair.2
        some (left.zip right ++ rest)

/-- Compare all already parent-ranked nodes in one sphere with authoritative Rule-1a labels. -/
def compareCanonicalPairLabelsAuthoritative? (mol : RawMolecule) (rule : CanonicalRuleStage) :
    List (CanonicalBranchNode × CanonicalBranchNode) → Option Ordering
  | [] => some Ordering.eq
  | pair :: pairs =>
      match mol.compareCanonicalNodeRuleAuthoritative? rule pair.1 pair.2 with
      | none => none
      | some Ordering.eq => mol.compareCanonicalPairLabelsAuthoritative? rule pairs
      | some decision => some decision

/-- Compare one rule sphere-by-sphere with no arbitrary width cap. -/
def compareCanonicalRuleAuthoritative? (mol : RawMolecule)
    (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering)
    (rule : CanonicalRuleStage) :
    ℕ → List (CanonicalBranchNode × CanonicalBranchNode) → Option Ordering
  | 0, pairs =>
      match mol.compareCanonicalPairLabelsAuthoritative? rule pairs with
      | none => none
      | some Ordering.eq =>
          match mol.nextCanonicalPairsAuthoritative? before pairs with
          | some [] => some Ordering.eq
          | _ => none
      | some decision => some decision
  | fuel + 1, pairs =>
      match mol.compareCanonicalPairLabelsAuthoritative? rule pairs with
      | none => none
      | some Ordering.eq =>
          match mol.nextCanonicalPairsAuthoritative? before pairs with
          | none => none
          | some [] => some Ordering.eq
          | some next => mol.compareCanonicalRuleAuthoritative? before rule fuel next
      | some decision => some decision

/-- A strict decision in the current complete sphere is returned independently of that sphere's
width. -/
theorem compareCanonicalRuleAuthoritative?_eq_of_pairLabels_ne_eq
    (mol : RawMolecule)
    (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering)
    (rule : CanonicalRuleStage) (fuel : ℕ)
    (pairs : List (CanonicalBranchNode × CanonicalBranchNode)) (decision : Ordering)
    (observed : mol.compareCanonicalPairLabelsAuthoritative? rule pairs = some decision)
    (strict : decision ≠ Ordering.eq) :
    mol.compareCanonicalRuleAuthoritative? before rule fuel pairs = some decision := by
  cases fuel <;> simp [compareCanonicalRuleAuthoritative?, observed]

/-- Parent-refined comparison through Rules 1a, 1b, and 2 with no sphere-width cutoff. -/
def compareCanonicalBranchAuthoritativeAt? (mol : RawMolecule) :
    ℕ → CanonicalRuleStage → CanonicalBranchNode → CanonicalBranchNode → Option Ordering
  | 0, stage, left, right => mol.compareCanonicalNodeThroughAuthoritative? stage left right
  | fuel + 1, stage, left, right =>
      let before := mol.compareCanonicalBranchAuthoritativeAt? fuel stage
      let compareRule := fun rule =>
        mol.compareCanonicalRuleAuthoritative? before rule (fuel + 1) [(left, right)]
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

/-- Exact constitutional ligand comparison for the supported bonding-number-six molecular domain.

Depth `atomCount + 1` exhausts every simple real-atom occurrence path; canonical duplicate and
phantom nodes are terminal.  `none` therefore denotes unsupported chemical labeling, excessive
local bonding number, or sibling-ranking failure—not an arbitrary global sphere-width budget. -/
def compareBranchesAuthoritative? (mol : RawMolecule) (center left right : ℕ) : Option Ordering :=
  mol.compareCanonicalBranchAuthoritativeAt? (mol.atomCount + 1) CanonicalRuleStage.rule2
    (canonicalRoot center left) (canonicalRoot center right)

/-- Four-valued observation of the width-unbounded constitutional comparison. -/
def compareBranchesAuthoritativeStatus (mol : RawMolecule) (center left right : ℕ) :
    BranchComparisonStatus :=
  match mol.compareBranchesAuthoritative? center left right with
  | some Ordering.lt => .lower
  | some Ordering.gt => .higher
  | some Ordering.eq => .tied
  | none => .unresolved

/-- Strict descending ligand-position order through the width-unbounded comparator. -/
def rankBranchPositionsAuthoritative? (mol : RawMolecule) (center : ℕ)
    (ligands : List ℕ) : Option (List ℕ) :=
  let atomOf := fun position => ligands.getD position 0
  let compareAt := fun left right =>
    mol.compareBranchesAuthoritative? center (atomOf left) (atomOf right)
  let sorted := sortDescBy (fun left right => compareAt left right != some Ordering.lt)
    (List.range ligands.length)
  let strict := (List.range (sorted.length - 1)).all fun index =>
    match sorted[index]?, sorted[index + 1]? with
    | some left, some right => compareAt left right == some Ordering.gt
    | _, _ => false
  if strict then some sorted else none

/-- At least one pair remains unsupported even on the width-unbounded path. -/
def hasAuthoritativelyUnresolvedBranches (mol : RawMolecule) (center : ℕ)
    (ligands : List ℕ) : Bool :=
  (List.range ligands.length).any fun left =>
    (List.range ligands.length).any fun right =>
      left < right &&
        mol.compareBranchesAuthoritativeStatus center (ligands.getD left 0)
          (ligands.getD right 0) == .unresolved

/-- At least one ligand pair is proved to tie by the width-unbounded path. -/
def hasAuthoritativelyTiedBranches (mol : RawMolecule) (center : ℕ)
    (ligands : List ℕ) : Bool :=
  (List.range ligands.length).any fun left =>
    (List.range ligands.length).any fun right =>
      left < right &&
        mol.compareBranchesAuthoritativeStatus center (ligands.getD left 0)
          (ligands.getD right 0) == .tied

end TetraStereo.OneCenter.RawMolecule
