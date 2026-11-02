import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRerootFrame
import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Key

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Recursive source-canonical Rules-4a--5 keys

The constitutional part of each key is the exact rational Rules-1a--2 source tree.  The later-rule
part records occurrence labels read only through the strict dependency view.  Recursive sibling
ranking therefore contains no written aromatic single/double placement; the theorem at the end
proves equality of the complete key for any two exact Kekule realizations.
-/

open CertifiedLocalizedCIPInput

/-- Read one canonical cursor only when it is a strict dependency of the descriptor target. -/
def aromaticCanonicalDependencyLabel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    Option AromaticCanonicalAuxiliaryLabel :=
  if dependency : source.AromaticCanonicalDepthDependency cursor.occurrence target then
    view cursor.occurrence dependency
  else none

/-- Exact cumulative Rules-4a--5 tree on the source-canonical occurrence topology. -/
structure AromaticCanonicalCumulativeRule45Key
    (source : AuthoritativeChemicalInput) where
  constitutional : ExactOfficialRuleMajorKey source.AromaticCanonicalAtom
  descriptor : List (List (OfficialSparseEntry (List Nat)))
  labels : List (List (OfficialSparseEntry (Option AromaticCanonicalAuxiliaryLabel)))
  rankedLabels : List (List
    (OfficialSparseEntry (Option AromaticCanonicalAuxiliaryLabel)))

/-- Constitutional comparison followed by the complete cumulative later-rule projection. -/
def compareAromaticCanonicalCumulativeRule45Keys
    (source : AuthoritativeChemicalInput) :
    source.AromaticCanonicalCumulativeRule45Key →
    source.AromaticCanonicalCumulativeRule45Key → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.constitutional)
      (ExactOfficialRuleMajorKey.compareObserved source.molecule.toLocalizedMoleculeGraph
        source.molecule.semanticExactOfficialRule1aObservation))
    (Ordering.byKey (fun key => key.descriptor)
      (OfficialRuleMajorKey.compareSparseLayers
        compareLocalizedCumulativeRule45Priority))

/-- The source-canonical cumulative comparator is oriented and transitive. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_transCmp
    (source : AuthoritativeChemicalInput) :
    Std.TransCmp source.compareAromaticCanonicalCumulativeRule45Keys := by
  letI : Std.TransCmp ExactOfficialRuleMajorKey.compareExactAtomicNumber :=
    ExactOfficialRuleMajorKey.compareExactAtomicNumber_transCmp
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  letI : Std.TransCmp OfficialRuleMajorKey.compareRule1b := by
    unfold OfficialRuleMajorKey.compareRule1b
    infer_instance
  letI : Std.TransCmp
      (OfficialRuleMajorKey.compareSparseLayers
        ExactOfficialRuleMajorKey.compareExactAtomicNumber) := by
    unfold OfficialRuleMajorKey.compareSparseLayers
      OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareSparseEntry
    infer_instance
  letI : Std.TransCmp
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b) := by
    unfold OfficialRuleMajorKey.compareSparseLayers
      OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareSparseEntry
    infer_instance
  letI : Std.TransCmp
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat) := by
    unfold OfficialRuleMajorKey.compareSparseLayers
      OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareSparseEntry
    infer_instance
  letI : Std.TransCmp
      (ExactOfficialRuleMajorKey.compareObserved source.molecule.toLocalizedMoleculeGraph
        source.molecule.semanticExactOfficialRule1aObservation) := by
    unfold ExactOfficialRuleMajorKey.compareObserved
      ExactOfficialRuleMajorKey.compareAddressedSourcesObserved
      ExactOfficialRuleMajorKey.observedRule1aLayers
    infer_instance
  unfold compareAromaticCanonicalCumulativeRule45Keys
    compareLocalizedCumulativeRule45Priority
    OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer
    OfficialRuleMajorKey.compareSparseEntry
  infer_instance

/-- Recursive cumulative comparison is defined directly on the semantic source; no Kekule
selection is an input. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_source_fixed
    (source : AuthoritativeChemicalInput) :
    source.compareAromaticCanonicalCumulativeRule45Keys =
      source.compareAromaticCanonicalCumulativeRule45Keys :=
  rfl

/-- Generic descending insertion under an explicit comparator. -/
def insertAromaticCanonicalCumulativeRule45Key
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalCumulativeRule45Key →
      source.AromaticCanonicalCumulativeRule45Key → Ordering)
    (key : source.AromaticCanonicalCumulativeRule45Key) :
    List source.AromaticCanonicalCumulativeRule45Key →
      List source.AromaticCanonicalCumulativeRule45Key
  | [] => [key]
  | head :: tail =>
      match compare key head with
      | .lt => head :: insertAromaticCanonicalCumulativeRule45Key compare key tail
      | .eq | .gt => key :: head :: tail

/-- Generic structural descending sort. -/
def sortAromaticCanonicalCumulativeRule45Keys
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalCumulativeRule45Key →
      source.AromaticCanonicalCumulativeRule45Key → Ordering) :
    List source.AromaticCanonicalCumulativeRule45Key →
      List source.AromaticCanonicalCumulativeRule45Key
  | [] => []
  | key :: keys =>
      insertAromaticCanonicalCumulativeRule45Key compare key
        (sortAromaticCanonicalCumulativeRule45Keys compare keys)

/-! ## Recursive cumulative-key reflection -/

/-- Comparator-visible equivalence of cumulative keys together with the reflected label
projections needed downstream by Rule 4b.  Physical source-node identities need not be equal. -/
structure AromaticCanonicalCumulativeRule45UppercaseReflection
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalCumulativeRule45Key) : Prop where
  rule1a : ExactOfficialRuleMajorKey.observedRule1aLayers
      source.molecule.semanticExactOfficialRule1aObservation left.constitutional.sourceNodes =
    ExactOfficialRuleMajorKey.observedRule1aLayers
      source.molecule.semanticExactOfficialRule1aObservation right.constitutional.sourceNodes
  rule1b : ExactOfficialRuleMajorKey.rule1bLayers left.constitutional.sourceNodes =
    ExactOfficialRuleMajorKey.rule1bLayers right.constitutional.sourceNodes
  rule2 : ExactOfficialRuleMajorKey.rule2Layers source.molecule.toLocalizedMoleculeGraph
      left.constitutional.sourceNodes =
    ExactOfficialRuleMajorKey.rule2Layers source.molecule.toLocalizedMoleculeGraph
      right.constitutional.sourceNodes
  descriptor : left.descriptor = right.descriptor
  labels : right.labels = reflectUppercaseRankedLabels left.labels
  rankedLabels : right.rankedLabels = reflectUppercaseRankedLabels left.rankedLabels

theorem compareAromaticCanonicalCumulativeRule45Keys_congr_reflection
    (source : AuthoritativeChemicalInput)
    {left left' right right' : source.AromaticCanonicalCumulativeRule45Key}
    (leftReflected : source.AromaticCanonicalCumulativeRule45UppercaseReflection left left')
    (rightReflected : source.AromaticCanonicalCumulativeRule45UppercaseReflection right right') :
    source.compareAromaticCanonicalCumulativeRule45Keys left right =
      source.compareAromaticCanonicalCumulativeRule45Keys left' right' := by
  unfold compareAromaticCanonicalCumulativeRule45Keys
    ExactOfficialRuleMajorKey.compareObserved
    ExactOfficialRuleMajorKey.compareAddressedSourcesObserved
  simp [compareLex, Ordering.byKey,
    leftReflected.rule1a, leftReflected.rule1b, leftReflected.rule2,
    leftReflected.descriptor,
    rightReflected.rule1a, rightReflected.rule1b, rightReflected.rule2,
    rightReflected.descriptor]

private theorem insertAromaticCanonicalCumulativeRule45Key_reflection
    (source : AuthoritativeChemicalInput)
    {leftKey rightKey : source.AromaticCanonicalCumulativeRule45Key}
    (keyReflected : source.AromaticCanonicalCumulativeRule45UppercaseReflection
      leftKey rightKey) :
    ∀ {left right : List source.AromaticCanonicalCumulativeRule45Key},
      List.Forall₂ source.AromaticCanonicalCumulativeRule45UppercaseReflection left right →
      List.Forall₂ source.AromaticCanonicalCumulativeRule45UppercaseReflection
        (insertAromaticCanonicalCumulativeRule45Key
          source.compareAromaticCanonicalCumulativeRule45Keys leftKey left)
        (insertAromaticCanonicalCumulativeRule45Key
          source.compareAromaticCanonicalCumulativeRule45Keys rightKey right)
  | [], [], .nil => .cons keyReflected .nil
  | leftHead :: leftTail, rightHead :: rightTail,
      .cons headReflected tailReflected => by
      unfold insertAromaticCanonicalCumulativeRule45Key
      rw [source.compareAromaticCanonicalCumulativeRule45Keys_congr_reflection
        keyReflected headReflected]
      cases comparison : source.compareAromaticCanonicalCumulativeRule45Keys
          rightKey rightHead with
      | eq | gt =>
          exact .cons keyReflected (.cons headReflected tailReflected)
      | lt =>
          exact .cons headReflected
            (insertAromaticCanonicalCumulativeRule45Key_reflection
              source keyReflected tailReflected)

/-- Stable cumulative-key sorting is natural under comparator-visible uppercase reflection.
Mirrored source identities may differ, but the production sort follows the same branches. -/
theorem sortAromaticCanonicalCumulativeRule45Keys_reflection
    (source : AuthoritativeChemicalInput) :
    ∀ {left right : List source.AromaticCanonicalCumulativeRule45Key},
      List.Forall₂ source.AromaticCanonicalCumulativeRule45UppercaseReflection left right →
      List.Forall₂ source.AromaticCanonicalCumulativeRule45UppercaseReflection
        (sortAromaticCanonicalCumulativeRule45Keys
          source.compareAromaticCanonicalCumulativeRule45Keys left)
        (sortAromaticCanonicalCumulativeRule45Keys
          source.compareAromaticCanonicalCumulativeRule45Keys right)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons headReflected tailReflected => by
      unfold sortAromaticCanonicalCumulativeRule45Keys
      exact insertAromaticCanonicalCumulativeRule45Key_reflection source headReflected
        (sortAromaticCanonicalCumulativeRule45Keys_reflection source tailReflected)

theorem insertAromaticCanonicalCumulativeRule45Key_perm
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalCumulativeRule45Key →
      source.AromaticCanonicalCumulativeRule45Key → Ordering)
    (key : source.AromaticCanonicalCumulativeRule45Key) :
    ∀ keys,
      (insertAromaticCanonicalCumulativeRule45Key compare key keys).Perm (key :: keys)
  | [] => List.Perm.refl _
  | head :: tail => by
      unfold insertAromaticCanonicalCumulativeRule45Key
      cases comparison : compare key head with
      | eq => exact List.Perm.refl _
      | gt => exact List.Perm.refl _
      | lt =>
          exact (List.Perm.cons head
            (insertAromaticCanonicalCumulativeRule45Key_perm compare key tail)).trans
              (List.Perm.swap key head tail)

theorem sortAromaticCanonicalCumulativeRule45Keys_perm
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalCumulativeRule45Key →
      source.AromaticCanonicalCumulativeRule45Key → Ordering) :
    ∀ keys,
      (sortAromaticCanonicalCumulativeRule45Keys compare keys).Perm keys
  | [] => List.Perm.refl []
  | key :: keys =>
      (insertAromaticCanonicalCumulativeRule45Key_perm compare key
        (sortAromaticCanonicalCumulativeRule45Keys compare keys)).trans
          (List.Perm.cons key
            (sortAromaticCanonicalCumulativeRule45Keys_perm compare keys))

/-- Independent descending-order predicate for a cumulative sibling list. -/
def AromaticCanonicalCumulativeRule45KeysDescending
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalCumulativeRule45Key →
      source.AromaticCanonicalCumulativeRule45Key → Ordering)
    (keys : List source.AromaticCanonicalCumulativeRule45Key) : Prop :=
  keys.Pairwise fun left right => compare left right ≠ Ordering.lt

theorem insertAromaticCanonicalCumulativeRule45Key_descending
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalCumulativeRule45Key →
      source.AromaticCanonicalCumulativeRule45Key → Ordering)
    [Std.TransCmp compare]
    (key : source.AromaticCanonicalCumulativeRule45Key) :
    ∀ keys,
      AromaticCanonicalCumulativeRule45KeysDescending compare keys →
      AromaticCanonicalCumulativeRule45KeysDescending compare
        (insertAromaticCanonicalCumulativeRule45Key compare key keys)
  | [], _ => by
      simp [insertAromaticCanonicalCumulativeRule45Key,
        AromaticCanonicalCumulativeRule45KeysDescending]
  | head :: tail, sorted => by
      have headOverTail : ∀ observed ∈ tail,
          compare head observed ≠ Ordering.lt :=
        (List.pairwise_cons.mp sorted).1
      have tailSorted : AromaticCanonicalCumulativeRule45KeysDescending compare tail :=
        (List.pairwise_cons.mp sorted).2
      unfold insertAromaticCanonicalCumulativeRule45Key
      cases comparison : compare key head with
      | gt =>
          rw [AromaticCanonicalCumulativeRule45KeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | eq =>
          rw [AromaticCanonicalCumulativeRule45KeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | lt =>
          have insertedSorted :=
            insertAromaticCanonicalCumulativeRule45Key_descending
              compare key tail tailSorted
          rw [AromaticCanonicalCumulativeRule45KeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            have permutation :=
              insertAromaticCanonicalCumulativeRule45Key_perm compare key tail
            have sourcePresent : observed ∈ key :: tail :=
              (permutation.mem_iff).mp present
            rcases List.mem_cons.mp sourcePresent with same | tailPresent
            · subst observed
              have reverse : compare head key = Ordering.gt := by
                rw [Std.OrientedCmp.gt_iff_lt]
                exact comparison
              simp [reverse]
            · exact headOverTail observed tailPresent
          · exact insertedSorted

theorem sortAromaticCanonicalCumulativeRule45Keys_descending
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalCumulativeRule45Key →
      source.AromaticCanonicalCumulativeRule45Key → Ordering)
    [Std.TransCmp compare] :
    ∀ keys,
      AromaticCanonicalCumulativeRule45KeysDescending compare
        (sortAromaticCanonicalCumulativeRule45Keys compare keys)
  | [] => by
      simp [sortAromaticCanonicalCumulativeRule45Keys,
        AromaticCanonicalCumulativeRule45KeysDescending]
  | key :: keys =>
      insertAromaticCanonicalCumulativeRule45Key_descending compare key
        (sortAromaticCanonicalCumulativeRule45Keys compare keys)
        (sortAromaticCanonicalCumulativeRule45Keys_descending compare keys)

def aromaticCanonicalDescriptorChildLayerCount
    {source : AuthoritativeChemicalInput}
    (children : List source.AromaticCanonicalCumulativeRule45Key) : Nat :=
  children.foldl (fun longest child => max longest child.descriptor.length) 0

def mergeAromaticCanonicalDescriptorChildren
    {source : AuthoritativeChemicalInput}
    (children : List source.AromaticCanonicalCumulativeRule45Key) :
    List (List (OfficialSparseEntry (List Nat))) :=
  let count := aromaticCanonicalDescriptorChildLayerCount children
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2
        (child.1.descriptor.getD depth [])

def aromaticCanonicalLabelChildLayerCount
    {source : AuthoritativeChemicalInput}
    (children : List source.AromaticCanonicalCumulativeRule45Key) : Nat :=
  children.foldl (fun longest child => max longest child.labels.length) 0

def mergeAromaticCanonicalLabelChildren
    {source : AuthoritativeChemicalInput}
    (children : List source.AromaticCanonicalCumulativeRule45Key) :
    List (List (OfficialSparseEntry (Option AromaticCanonicalAuxiliaryLabel))) :=
  let count := aromaticCanonicalLabelChildLayerCount children
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2 (child.1.labels.getD depth [])

def aromaticCanonicalRankedChildTail
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalCumulativeRule45Key →
      source.AromaticCanonicalCumulativeRule45Key → Ordering)
    (previous : source.AromaticCanonicalCumulativeRule45Key) (rank : Nat) :
    List source.AromaticCanonicalCumulativeRule45Key →
      List (source.AromaticCanonicalCumulativeRule45Key × Nat)
  | [] => []
  | child :: children =>
      let childRank := if compare child previous = Ordering.eq then rank else rank + 1
      (child, childRank) ::
        aromaticCanonicalRankedChildTail compare child childRank children

def aromaticCanonicalRankedChildren
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalCumulativeRule45Key →
      source.AromaticCanonicalCumulativeRule45Key → Ordering) :
    List source.AromaticCanonicalCumulativeRule45Key →
      List (source.AromaticCanonicalCumulativeRule45Key × Nat)
  | [] => []
  | child :: children =>
      (child, 0) :: aromaticCanonicalRankedChildTail compare child 0 children

def aromaticCanonicalRankedLabelChildLayerCount
    {source : AuthoritativeChemicalInput}
    (children : List source.AromaticCanonicalCumulativeRule45Key) : Nat :=
  children.foldl (fun longest child => max longest child.rankedLabels.length) 0

def mergeAromaticCanonicalRankedLabelChildren
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalCumulativeRule45Key →
      source.AromaticCanonicalCumulativeRule45Key → Ordering)
    (children : List source.AromaticCanonicalCumulativeRule45Key) :
    List (List (OfficialSparseEntry (Option AromaticCanonicalAuxiliaryLabel))) :=
  let count := aromaticCanonicalRankedLabelChildLayerCount children
  let ranked := aromaticCanonicalRankedChildren compare children
  (List.range count).map fun depth =>
    ranked.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2
        (child.1.rankedLabels.getD depth [])

/-- Compile one complete cumulative Rules-4a--5 key on the canonical occurrence zipper. -/
noncomputable def buildAromaticCanonicalCumulativeRule45Key?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel →
      Option source.AromaticCanonicalCumulativeRule45Key
  | 0, cursor => do
      let children ← source.aromaticCanonicalRerootChildren? cursor
      if children = [] then
        let label := source.aromaticCanonicalDependencyLabel target view cursor
        some
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
      else none
  | fuel + 1, cursor => do
      let children ← source.aromaticCanonicalRerootChildren? cursor
      let label := source.aromaticCanonicalDependencyLabel target view cursor
      if children = [] then
        some
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
      else
        let childKeys ← children.mapM
          (source.buildAromaticCanonicalCumulativeRule45Key?
            stage target view fuel)
        let compare := source.compareAromaticCanonicalCumulativeRule45Keys
        let sorted := sortAromaticCanonicalCumulativeRule45Keys compare childKeys
        some
          { constitutional := ExactOfficialRuleMajorKey.assemble
              (MoleculeGraph.exactOfficialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            descriptor :=
              [[([], localizedCumulativeRule45Priority stage label)]] ++
                mergeAromaticCanonicalDescriptorChildren sorted
            labels := [[([], label)]] ++ mergeAromaticCanonicalLabelChildren sorted
            rankedLabels := [[([], label)]] ++
              mergeAromaticCanonicalRankedLabelChildren compare sorted }

/-- Independent complete reading of one dependency label. -/
def DeclarativeAromaticCanonicalDependencyLabel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (label : Option AromaticCanonicalAuxiliaryLabel) : Prop :=
  (¬ source.AromaticCanonicalDepthDependency cursor.occurrence target ∧ label = none) ∨
    ∃ dependency : source.AromaticCanonicalDepthDependency cursor.occurrence target,
      view cursor.occurrence dependency = label

theorem aromaticCanonicalDependencyLabel_eq_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (label : Option AromaticCanonicalAuxiliaryLabel) :
    source.aromaticCanonicalDependencyLabel target view cursor = label ↔
      source.DeclarativeAromaticCanonicalDependencyLabel target view cursor label := by
  unfold aromaticCanonicalDependencyLabel DeclarativeAromaticCanonicalDependencyLabel
  split
  · rename_i dependency
    constructor
    · intro equality
      exact Or.inr ⟨dependency, equality⟩
    · rintro (⟨notDependency, _⟩ | ⟨other, equality⟩)
      · exact (notDependency dependency).elim
      · simpa only [Subsingleton.elim other dependency] using equality
  · rename_i notDependency
    constructor
    · intro equality
      exact Or.inl ⟨notDependency, equality.symm⟩
    · rintro (⟨_, rfl⟩ | ⟨dependency, _⟩)
      · rfl
      · exact (notDependency dependency).elim

/- Independent recursive semantics of canonical cumulative Rules-4a--5 keys and aligned child
lists. -/
mutual

inductive DeclarativeAromaticCanonicalCumulativeRule45Key
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel →
      source.AromaticCanonicalCumulativeRule45Key → Prop
  | zeroLeaf {cursor children label}
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (terminal : children = [])
      (observed : source.DeclarativeAromaticCanonicalDependencyLabel
        target view cursor label) :
      DeclarativeAromaticCanonicalCumulativeRule45Key source stage target view 0 cursor
        { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
            cursor.occurrence.1.node true
          descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
          labels := [[([], label)]]
          rankedLabels := [[([], label)]] }
  | successorLeaf {fuel cursor children label}
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (terminal : children = [])
      (observed : source.DeclarativeAromaticCanonicalDependencyLabel
        target view cursor label) :
      DeclarativeAromaticCanonicalCumulativeRule45Key source stage target view
        (fuel + 1) cursor
        { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
            cursor.occurrence.1.node true
          descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
          labels := [[([], label)]]
          rankedLabels := [[([], label)]] }
  | successorBranch {fuel cursor children label childKeys sorted}
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (nonterminal : children ≠ [])
      (observed : source.DeclarativeAromaticCanonicalDependencyLabel
        target view cursor label)
      (childDerivations : DeclarativeAromaticCanonicalCumulativeRule45KeyList
        source stage target view fuel children childKeys)
      (permutation : sorted.Perm childKeys)
      (descending : AromaticCanonicalCumulativeRule45KeysDescending
        source.compareAromaticCanonicalCumulativeRule45Keys sorted) :
      DeclarativeAromaticCanonicalCumulativeRule45Key source stage target view
        (fuel + 1) cursor
        { constitutional := ExactOfficialRuleMajorKey.assemble
            (MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node false)
            (sorted.map fun child => child.constitutional)
          descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
            mergeAromaticCanonicalDescriptorChildren sorted
          labels := [[([], label)]] ++ mergeAromaticCanonicalLabelChildren sorted
          rankedLabels := [[([], label)]] ++
            mergeAromaticCanonicalRankedLabelChildren
              source.compareAromaticCanonicalCumulativeRule45Keys sorted }

inductive DeclarativeAromaticCanonicalCumulativeRule45KeyList
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    Nat → List (source.AromaticCanonicalRerootCursor carrierFuel) →
      List source.AromaticCanonicalCumulativeRule45Key → Prop
  | nil (fuel) :
      DeclarativeAromaticCanonicalCumulativeRule45KeyList
        source stage target view fuel [] []
  | cons {fuel cursor cursors key keys}
      (head : DeclarativeAromaticCanonicalCumulativeRule45Key
        source stage target view fuel cursor key)
      (tail : DeclarativeAromaticCanonicalCumulativeRule45KeyList
        source stage target view fuel cursors keys) :
      DeclarativeAromaticCanonicalCumulativeRule45KeyList
        source stage target view fuel (cursor :: cursors) (key :: keys)

end

private theorem mapM_buildAromaticCanonicalCumulativeRule45Key?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (sound : ∀ cursor key,
      source.buildAromaticCanonicalCumulativeRule45Key?
        stage target view fuel cursor = some key →
      source.DeclarativeAromaticCanonicalCumulativeRule45Key
        stage target view fuel cursor key) :
    ∀ cursors keys,
      cursors.mapM (source.buildAromaticCanonicalCumulativeRule45Key?
        stage target view fuel) = some keys →
      DeclarativeAromaticCanonicalCumulativeRule45KeyList
        source stage target view fuel cursors keys
  | [], keys, computed => by
      simp at computed
      subst keys
      exact DeclarativeAromaticCanonicalCumulativeRule45KeyList.nil fuel
  | cursor :: cursors, keys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : source.buildAromaticCanonicalCumulativeRule45Key?
          stage target view fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (source.buildAromaticCanonicalCumulativeRule45Key?
                stage target view fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact DeclarativeAromaticCanonicalCumulativeRule45KeyList.cons
                (sound cursor head headComputed)
                (mapM_buildAromaticCanonicalCumulativeRule45Key?_sound
                  source stage target view sound cursors tail tailComputed)

/-- Every executable cumulative key satisfies the independent recursive topology, label,
permutation, and descending-order semantics. -/
theorem buildAromaticCanonicalCumulativeRule45Key?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ fuel cursor key,
      source.buildAromaticCanonicalCumulativeRule45Key?
        stage target view fuel cursor = some key →
      source.DeclarativeAromaticCanonicalCumulativeRule45Key
        stage target view fuel cursor key
  | 0, cursor, key, computed => by
      unfold buildAromaticCanonicalCumulativeRule45Key? at computed
      simp only [aromaticCanonicalRerootChildren?] at computed
      let children := source.aromaticCanonicalRerootChildren cursor
      by_cases terminal : children = []
      · simp [children, terminal] at computed
        subst key
        exact DeclarativeAromaticCanonicalCumulativeRule45Key.zeroLeaf
          (source.aromaticCanonicalRerootChildren_sound cursor) terminal
          ((source.aromaticCanonicalDependencyLabel_eq_iff target view cursor _).mp rfl)
      · simp [children, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildAromaticCanonicalCumulativeRule45Key? at computed
      simp only [aromaticCanonicalRerootChildren?] at computed
      let children := source.aromaticCanonicalRerootChildren cursor
      let label := source.aromaticCanonicalDependencyLabel target view cursor
      by_cases terminal : children = []
      · simp [children, terminal] at computed
        subst key
        exact DeclarativeAromaticCanonicalCumulativeRule45Key.successorLeaf
          (source.aromaticCanonicalRerootChildren_sound cursor) terminal
          ((source.aromaticCanonicalDependencyLabel_eq_iff target view cursor label).mp rfl)
      · cases childKeysComputed : children.mapM
            (source.buildAromaticCanonicalCumulativeRule45Key?
              stage target view fuel) with
        | none => simp [children, terminal, childKeysComputed] at computed
        | some childKeys =>
            let compare := source.compareAromaticCanonicalCumulativeRule45Keys
            let sorted := sortAromaticCanonicalCumulativeRule45Keys compare childKeys
            simp [children, terminal, childKeysComputed] at computed
            subst key
            letI : Std.TransCmp compare :=
              source.compareAromaticCanonicalCumulativeRule45Keys_transCmp
            exact DeclarativeAromaticCanonicalCumulativeRule45Key.successorBranch
              (source.aromaticCanonicalRerootChildren_sound cursor) terminal
              ((source.aromaticCanonicalDependencyLabel_eq_iff
                target view cursor label).mp rfl)
              (mapM_buildAromaticCanonicalCumulativeRule45Key?_sound
                source stage target view
                (source.buildAromaticCanonicalCumulativeRule45Key?_sound
                  stage target view fuel)
                children childKeys childKeysComputed)
              (sortAromaticCanonicalCumulativeRule45Keys_perm compare childKeys)
              (sortAromaticCanonicalCumulativeRule45Keys_descending compare childKeys)

/-- A selection-indexed compatibility wrapper makes the absence of representation dependence
explicit at old call sites. -/
noncomputable def buildAromaticCanonicalCumulativeRule45KeyForSelection?
    (source : AuthoritativeChemicalInput) (_selection : List (Nat × Nat))
    {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    Option source.AromaticCanonicalCumulativeRule45Key :=
  source.buildAromaticCanonicalCumulativeRule45Key? stage target view fuel cursor

-- Keep the exactness witnesses explicit for source-compatible named theorem applications.
set_option linter.unusedVariables false in
/-- The complete recursive cumulative key is definitionally independent of Kekule choice. -/
theorem buildAromaticCanonicalCumulativeRule45KeyForSelection?_kekule_invariant
    (source : AuthoritativeChemicalInput)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.molecule.SemanticAromaticMancudeEdgeSetExact
      (source.molecule.withAromaticKekuleSelection leftSelection))
    (rightExact : source.molecule.SemanticAromaticMancudeEdgeSetExact
      (source.molecule.withAromaticKekuleSelection rightSelection))
    {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ fuel cursor,
      source.buildAromaticCanonicalCumulativeRule45KeyForSelection?
          leftSelection stage target view fuel cursor =
        source.buildAromaticCanonicalCumulativeRule45KeyForSelection?
          rightSelection stage target view fuel cursor := by
  intro fuel cursor
  rfl

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
