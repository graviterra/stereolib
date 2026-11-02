import TetraStereo.OneCenter.LocalizedActualCanonicalConstitutionalRefinement
import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder
import TetraStereo.OneCenter.LocalizedCumulativeTreeTableReconstruction
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Observation tree read back from an actual constitutional tie

Two original-root outward arms whose actual `OfficialRuleMajorKey` comparison returns
`Ordering.eq` have the same ranked observation tree. The tree keeps parentage, atomic number,
isotope mass, and a provenance class read from Rule 1b at the address sphere
`address.length + 1`: equality is a real atom, one less is a multiple-bond duplicate of the
parent sphere, and any smaller value is a ring duplicate of that ancestor index.

The comparison hypothesis is the tie already under analysis. Build success and the key are the
adequate-fuel `OriginalRootArm`, not a supplied key. Formal charge, bond order, auxiliary
labels, and the Rules 4a–5 descriptor are not columns of this comparison.
-/

namespace TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree
open OfficialCIPNode
open OfficialCIPNodeProvenance
open OfficialCIPSourceTree
open scoped Classical

noncomputable section

/-! ## The strong tree -/

/-- Provenance visible in a constitutional key: the numeric Rule-1b class at a known sphere. -/
inductive RetainedProvenance where
  | real
  | multipleBond (ancestorIndex : ℕ)
  | ring (ancestorIndex : ℕ)
  deriving DecidableEq, Repr

/-- Ranked observation tree. Children are the actual sorted sibling subtrees. -/
inductive RetainedObservationTree where
  | node (atomicNumber isotopeMass : ℕ) (provenance : RetainedProvenance)
      (children : List RetainedObservationTree)

namespace RetainedObservationTree

def atomicNumber : RetainedObservationTree → ℕ
  | node z _ _ _ => z

def isotopeMass : RetainedObservationTree → ℕ
  | node _ mass _ _ => mass

def provenance : RetainedObservationTree → RetainedProvenance
  | node _ _ provenance _ => provenance

def children : RetainedObservationTree → List RetainedObservationTree
  | node _ _ _ children => children

/-- Ranked-sibling lookup. The address is the path of child slots, not a molecular atom name. -/
def atAddress? : RetainedObservationTree → List ℕ → Option RetainedObservationTree
  | tree, [] => some tree
  | node _ _ _ children, slot :: address =>
      match children[slot]? with
      | none => none
      | some child => atAddress? child address

end RetainedObservationTree

/-- Official provenance collapsed to the constitutional class. A placeholder arm is unused once
`GraphGenerated` is known. -/
def collapseProvenance : OfficialCIPNodeProvenance → RetainedProvenance
  | .realAtom => .real
  | .multipleBondDuplicate distance => .multipleBond distance
  | .ringDuplicate distance => .ring distance
  | .placeholder _ distance => .ring distance

/-- Class of one Rule-1b value at a known sphere. -/
def provenanceOfDistance (sphere distance : ℕ) : RetainedProvenance :=
  if distance = sphere then .real
  else if distance + 1 = sphere then .multipleBond distance
  else .ring distance

mutual
  /-- Decode a source-erased constitutional shape at a known sphere. -/
  def ofShape (sphere : ℕ) : LocalizedCumulativeBranchShape → RetainedObservationTree
    | .mk atomicNumber rule1bDistance isotopeMass siblings =>
        .node atomicNumber isotopeMass (provenanceOfDistance sphere rule1bDistance)
          (ofShapeList (sphere + 1) siblings)
  termination_by branch => sizeOf branch
  decreasing_by simp_wf

  /-- Decode a ranked sibling list one sphere below its parent. -/
  def ofShapeList (sphere : ℕ) :
      List LocalizedCumulativeBranchShape → List RetainedObservationTree
    | [] => []
    | child :: siblings => ofShape sphere child :: ofShapeList sphere siblings
  termination_by branches => sizeOf branches
  decreasing_by
    all_goals (simp_wf <;> omega)
end

theorem ofShape_mk (sphere atomicNumber rule1bDistance isotopeMass : ℕ)
    (siblings : List LocalizedCumulativeBranchShape) :
    ofShape sphere ⟨atomicNumber, rule1bDistance, isotopeMass, siblings⟩ =
      .node atomicNumber isotopeMass (provenanceOfDistance sphere rule1bDistance)
        (ofShapeList (sphere + 1) siblings) := by
  rw [ofShape]

theorem ofShapeList_nil (sphere : ℕ) :
    ofShapeList sphere ([] : List LocalizedCumulativeBranchShape) = [] := by
  rw [ofShapeList]

theorem ofShapeList_cons (sphere : ℕ) (child : LocalizedCumulativeBranchShape)
    (siblings : List LocalizedCumulativeBranchShape) :
    ofShapeList sphere (child :: siblings) =
      ofShape sphere child :: ofShapeList sphere siblings := by
  rw [ofShapeList]

/-- Parentage: the decoded children are the decoded child shapes, one sphere down. -/
theorem ofShape_children (sphere : ℕ) (branch : LocalizedCumulativeBranchShape) :
    (ofShape sphere branch).children = ofShapeList (sphere + 1) branch.children := by
  cases branch with
  | mk atomicNumber rule1bDistance isotopeMass siblings =>
      rw [ofShape_mk]
      unfold RetainedObservationTree.children LocalizedCumulativeBranchShape.children
      rfl

theorem ofShape_shape_fields {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (sphere : ℕ) (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (ofShape sphere tree.shape).atomicNumber = tree.atomicNumber ∧
      (ofShape sphere tree.shape).isotopeMass = tree.isotopeMass ∧
        (ofShape sphere tree.shape).provenance =
          provenanceOfDistance sphere tree.rule1bDistance := by
  obtain ⟨_source, atomicNumber, rule1bDistance, isotopeMass, _label, siblings⟩ := tree
  rw [shape, ofShape_mk]
  exact ⟨rfl, rfl, rfl⟩

private theorem ofShapeList_getElem? (sphere : ℕ) :
    ∀ (shapes : List LocalizedCumulativeBranchShape) (slot : ℕ),
      (ofShapeList sphere shapes)[slot]? = (shapes[slot]?).map (ofShape sphere)
  | [], _ => by rw [ofShapeList_nil]; rfl
  | _ :: _, 0 => by rw [ofShapeList_cons]; rfl
  | _ :: shapes, slot + 1 => by
      rw [ofShapeList_cons]
      exact ofShapeList_getElem? sphere shapes slot

private theorem shapeList_getElem? {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    ∀ (siblings : List (LocalizedCumulativeDecoratedTree input carrierFuel)) (slot : ℕ),
      (shapeList siblings)[slot]? = (siblings[slot]?).map shape
  | [], _ => by rw [shapeList]; rfl
  | _ :: _, 0 => by rw [shapeList]; rfl
  | _ :: siblings, slot + 1 => by
      rw [shapeList]
      exact shapeList_getElem? siblings slot

/-- A ranked address in the decorated tree is the same address in the decoded shape. -/
theorem atAddress?_ofShape_shape {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (sphere : ℕ) (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    ∀ (address : List ℕ) (subtree : LocalizedCumulativeDecoratedTree input carrierFuel),
      tree.decoratedSubtreeAt? address = some subtree →
        (ofShape sphere tree.shape).atAddress? address =
          some (ofShape (sphere + address.length) subtree.shape) := by
  intro address
  induction address generalizing tree sphere with
  | nil =>
      intro subtree lookup
      simp only [decoratedSubtreeAt?] at lookup
      have same : tree = subtree := Option.some.inj lookup
      subst same
      rw [RetainedObservationTree.atAddress?, List.length_nil, Nat.add_zero]
  | cons slot address inductionHypothesis =>
      intro subtree lookup
      obtain ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, siblings⟩ := tree
      rw [decoratedSubtreeAt?] at lookup
      cases hslot : siblings[slot]? with
      | none => simp [hslot] at lookup
      | some child =>
          simp [hslot] at lookup
          have hget : (ofShapeList (sphere + 1) (shapeList siblings))[slot]? =
              some (ofShape (sphere + 1) child.shape) := by
            rw [ofShapeList_getElem?, shapeList_getElem?, hslot]
            rfl
          rw [shape, ofShape_mk, RetainedObservationTree.atAddress?]
          have hreduced :
              (match (ofShapeList (sphere + 1) (shapeList siblings))[slot]? with
                | none => none
                | some descendant => descendant.atAddress? address) =
                (ofShape (sphere + 1) child.shape).atAddress? address := by
            rw [hget]
          have ih := inductionHypothesis (sphere + 1) child subtree lookup
          rw [hreduced, ih]
          apply congrArg some
          apply congrArg (fun n => ofShape n subtree.shape)
          rw [List.length_cons]
          omega

/-! ## Actual arms and the comparison columns -/

/-- The adequate-fuel original-root arm picked from the existing existence proof. -/
def actualOriginalRootArm (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel) :
    input.OriginalRootArm center index stage read :=
  Classical.choice (exists_originalRootArm input center index stage read)

theorem actualOriginalRootArm_built (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read
        (2 * (input.certified.input.molecule.atomCount + 1 + 1))
        (input.localizedLigandRootCursor center index) =
      some (actualOriginalRootArm input center index stage read).key :=
  (actualOriginalRootArm input center index stage read).built

/-- Any two packages for one ligand are the same actual key: both equal the adequate-fuel build. -/
theorem key_eq_of_originalRootArm {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    (arm1 arm2 : input.OriginalRootArm center index stage read) :
    arm1.key = arm2.key := by
  have same : some arm1.key = some arm2.key := by
    rw [← arm1.built, arm2.built]
  exact Option.some.inj same

/-- The three constitutional columns of an actual arm are the addressed tables of its tree. -/
theorem tree_columns_eq_key {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read) :
    table (fun node => node.atomicNumber) arm.tree = arm.key.constitutional.rule1a ∧
      table (fun node => node.rule1bDistance) arm.tree = arm.key.constitutional.rule1b ∧
        table (fun node => node.isotopeMass) arm.tree = arm.key.constitutional.rule2 := by
  rcases arm.tableMatch with ⟨h1a, h1b, h2, _descriptor⟩
  simp only [tables_rule1a, tables_rule1b, tables_rule2] at h1a h1b h2
  exact ⟨h1a, h1b, h2⟩

/-- A constitutional comparison tie is equality of the three actual addressed columns.
The descriptor column is not part of this equivalence. -/
theorem constitutionalColumns_eq_of_compare_eq {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {index1 index2 : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    (arm1 : input.OriginalRootArm center index1 stage read)
    (arm2 : input.OriginalRootArm center index2 stage read)
    (tie : OfficialRuleMajorKey.compare arm1.key.constitutional arm2.key.constitutional =
      Ordering.eq) :
    arm1.key.constitutional.rule1a = arm2.key.constitutional.rule1a ∧
      arm1.key.constitutional.rule1b = arm2.key.constitutional.rule1b ∧
        arm1.key.constitutional.rule2 = arm2.key.constitutional.rule2 :=
  (officialRuleMajorKey_compare_eq_iff arm1.key.constitutional arm2.key.constitutional).1 tie

/-- Equal constitutional columns determine the source-erased parentage shape. -/
theorem shape_eq_of_constitutional_tie {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {index1 index2 : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    (arm1 : input.OriginalRootArm center index1 stage read)
    (arm2 : input.OriginalRootArm center index2 stage read)
    (tie : OfficialRuleMajorKey.compare arm1.key.constitutional arm2.key.constitutional =
      Ordering.eq) :
    shape arm1.tree = shape arm2.tree := by
  have cols := constitutionalColumns_eq_of_compare_eq arm1 arm2 tie
  have left := tree_columns_eq_key arm1
  have right := tree_columns_eq_key arm2
  exact table_shape_eq_of_constitutional_tables_eq arm1.tree arm2.tree
    (left.1.trans (cols.1.trans right.1.symm))
    (left.2.1.trans (cols.2.1.trans right.2.1.symm))
    (left.2.2.trans (cols.2.2.trans right.2.2.symm))

/-- Occupied ranked addresses agree, with equal subtree shapes, once the shapes agree. -/
theorem map_shape_decoratedSubtreeAt? {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (t1 t2 : LocalizedCumulativeDecoratedTree input carrierFuel)
    (same : shape t1 = shape t2) :
    ∀ address : List ℕ,
      (t1.decoratedSubtreeAt? address).map shape =
        (t2.decoratedSubtreeAt? address).map shape := by
  intro address
  induction address generalizing t1 t2 with
  | nil =>
      simp [decoratedSubtreeAt?, same]
  | cons slot address inductionHypothesis =>
      obtain ⟨s1, z1, d1, m1, l1, c1⟩ := t1
      obtain ⟨s2, z2, d2, m2, l2, c2⟩ := t2
      have hs := same
      rw [shape, shape] at hs
      simp only [LocalizedCumulativeBranchShape.mk.injEq] at hs
      obtain ⟨_, _, _, hchildren⟩ := hs
      have hmap : (c1[slot]?).map shape = (c2[slot]?).map shape := by
        rw [← shapeList_getElem?, hchildren, shapeList_getElem?]
      rw [decoratedSubtreeAt?, decoratedSubtreeAt?]
      cases h1 : c1[slot]? with
      | none =>
          cases h2 : c2[slot]? with
          | none => rfl
          | some child2 => simp [h1, h2] at hmap
      | some child1 =>
          cases h2 : c2[slot]? with
          | none => simp [h1, h2] at hmap
          | some child2 =>
              simp [h1, h2] at hmap
              simpa [h1, h2] using inductionHypothesis child1 child2 hmap

/-- The observation tree of one actual original-root arm. -/
def retainedObservationTree {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read) : RetainedObservationTree :=
  ofShape 1 (shape arm.tree)

theorem retainedObservationTree_eq_of_arm_tie {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {index1 index2 : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    (arm1 : input.OriginalRootArm center index1 stage read)
    (arm2 : input.OriginalRootArm center index2 stage read)
    (tie : OfficialRuleMajorKey.compare arm1.key.constitutional arm2.key.constitutional =
      Ordering.eq) :
    retainedObservationTree arm1 = retainedObservationTree arm2 := by
  unfold retainedObservationTree
  rw [shape_eq_of_constitutional_tie arm1 arm2 tie]

/-- Facade: the tie of the two adequate-fuel arms yields the observation-tree equality. -/
theorem retainedObservationTree_eq_of_actual_tie (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index1 index2 : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (tie : OfficialRuleMajorKey.compare
        (actualOriginalRootArm input center index1 stage read).key.constitutional
        (actualOriginalRootArm input center index2 stage read).key.constitutional =
      Ordering.eq) :
    retainedObservationTree (actualOriginalRootArm input center index1 stage read) =
      retainedObservationTree (actualOriginalRootArm input center index2 stage read) :=
  retainedObservationTree_eq_of_arm_tie
    (actualOriginalRootArm input center index1 stage read)
    (actualOriginalRootArm input center index2 stage read) tie

theorem retainedObservationTree_unique {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    (arm1 arm2 : input.OriginalRootArm center index stage read) :
    retainedObservationTree arm1 = retainedObservationTree arm2 := by
  have hk := key_eq_of_originalRootArm arm1 arm2
  apply retainedObservationTree_eq_of_arm_tie arm1 arm2
  rw [hk]
  exact (officialRuleMajorKey_compare_eq_iff _ _).2 ⟨rfl, rfl, rfl⟩

/-! ## Rule 1b at the address sphere -/

/-- Numeric provenance recovered at one generated original-root node. -/
structure SphereProvenanceReadback {V : Type*} (node : OfficialCIPNode V) (sphere : ℕ) : Prop where
  graphGenerated : node.GraphGenerated
  classified : provenanceOfDistance sphere node.rule1bRootDistance =
    collapseProvenance node.provenance
  real_iff : node.rule1bRootDistance = sphere ↔ node.provenance = .realAtom
  multiple_iff : ∀ d, node.provenance = .multipleBondDuplicate d ↔
    node.rule1bRootDistance = d ∧ d + 1 = sphere
  ring_iff : ∀ d, node.provenance = .ringDuplicate d ↔
    node.rule1bRootDistance = d ∧ d + 1 < sphere

private theorem hierarchyChild_length {V : Type*} {tree : OfficialCIPSourceTree V}
    {parent node : tree.HierarchyNode} (edge : tree.HierarchyChild parent node) :
    node.1.length = parent.1.length + 1 := by
  obtain ⟨_slot, address⟩ := edge
  rw [address, List.length_append, List.length_singleton]

private theorem transGen_hierarchy_length {V : Type*} {tree : OfficialCIPSourceTree V}
    {ancestor parent : tree.HierarchyNode}
    (path : Relation.TransGen tree.HierarchyChild ancestor parent) :
    ancestor.1.length + 1 ≤ parent.1.length := by
  induction path with
  | single edge =>
      rw [hierarchyChild_length edge]
  | tail _path edge inductionHypothesis =>
      rw [hierarchyChild_length edge]
      omega

private theorem dropLast_length_succ {address : List ℕ} (hne : address ≠ []) :
    address.dropLast.length + 1 = address.length := by
  have hcat := congrArg List.length (List.dropLast_concat_getLast hne)
  rw [List.length_append, List.length_singleton] at hcat
  exact hcat

private theorem duplicate_address_ne_nil {input : CertifiedLocalizedCIPInput}
    {tree : OfficialCIPSourceTree input.Atom} {center ligand : input.Atom}
    {rootEq : tree.source = OfficialCIPNode.rootFromEdge center ligand}
    {address : List ℕ} {subtree : OfficialCIPSourceTree input.Atom}
    {lookup : tree.subtreeAt? address = some subtree} {d : ℕ}
    (hprov : subtree.source.provenance = .multipleBondDuplicate d ∨
      subtree.source.provenance = .ringDuplicate d) :
    address ≠ [] := by
  intro hempty
  subst hempty
  cases tree with
  | node sourceNode subtrees =>
      rw [OfficialCIPSourceTree.subtreeAt?.eq_def] at lookup
      have same : OfficialCIPSourceTree.node sourceNode subtrees = subtree :=
        Option.some.inj lookup
      rw [← same, rootEq, OfficialCIPNode.rootFromEdge] at hprov
      cases hprov with
      | inl h => nomatch h
      | inr h => nomatch h

private theorem childLabel_eq_toDeclarative {input : CertifiedLocalizedCIPInput}
    (tree : OfficialCIPSourceTree input.Atom) (address : List ℕ)
    (subtree : OfficialCIPSourceTree input.Atom)
    (lookup : tree.subtreeAt? address = some subtree)
    (present : address ∈ tree.hierarchyAddresses) :
    tree.declarativeLabel ⟨address, present⟩ = subtree.source.toDeclarativeLabel := by
  have hsource : tree.sourceAtAddress? address = some subtree.source := by
    simp [sourceAtAddress?, lookup]
  simp [declarativeLabel, hsource, toDeclarativeLabel]

private theorem multipleBond_succ_eq_sphere {input : CertifiedLocalizedCIPInput}
    (tree : OfficialCIPSourceTree input.Atom) (center ligand : input.Atom)
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren)
    (rootEq : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (address : List ℕ) (subtree : OfficialCIPSourceTree input.Atom)
    (lookup : tree.subtreeAt? address = some subtree) (d : ℕ)
    (hprov : subtree.source.provenance = .multipleBondDuplicate d) :
    d + 1 = address.length + 1 := by
  have address_ne : address ≠ [] :=
    duplicate_address_ne_nil (lookup := lookup) (rootEq := rootEq) (hprov := Or.inl hprov)
  have occ := mem_occurrences_of_subtreeAt?_eq_some address tree subtree lookup
  have present := mem_hierarchyAddresses_of_occurrence tree (address, subtree.source) occ
  have parentPresent := dropLast_mem_hierarchyAddresses tree present
  let parentNode : tree.HierarchyNode := ⟨address.dropLast, parentPresent⟩
  let childNode : tree.HierarchyNode := ⟨address, present⟩
  have edge : tree.HierarchyChild parentNode childNode :=
    ⟨address.getLast address_ne, (List.dropLast_concat_getLast address_ne).symm⟩
  have hdup := generatedSourceTree_duplicateDistancesCorrect input tree center ligand
    generated rootEq parentNode childNode edge
  have hlabel := childLabel_eq_toDeclarative tree address subtree lookup present
  rw [show tree.toDeclarativeDigraph.label childNode = subtree.source.toDeclarativeLabel from
    hlabel] at hdup
  rw [toDeclarativeLabel, hprov, toDeclarative] at hdup
  rw [declarativeAddressing_address] at hdup
  rw [dropLast_length_succ address_ne] at hdup
  exact congrArg Nat.succ hdup

private theorem ring_succ_lt_sphere {input : CertifiedLocalizedCIPInput}
    (tree : OfficialCIPSourceTree input.Atom) (center ligand : input.Atom)
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren)
    (rootEq : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (address : List ℕ) (subtree : OfficialCIPSourceTree input.Atom)
    (lookup : tree.subtreeAt? address = some subtree) (d : ℕ)
    (hprov : subtree.source.provenance = .ringDuplicate d) :
    d + 1 < address.length + 1 := by
  have address_ne : address ≠ [] :=
    duplicate_address_ne_nil (lookup := lookup) (rootEq := rootEq) (hprov := Or.inr hprov)
  have occ := mem_occurrences_of_subtreeAt?_eq_some address tree subtree lookup
  have present := mem_hierarchyAddresses_of_occurrence tree (address, subtree.source) occ
  have parentPresent := dropLast_mem_hierarchyAddresses tree present
  let parentNode : tree.HierarchyNode := ⟨address.dropLast, parentPresent⟩
  let childNode : tree.HierarchyNode := ⟨address, present⟩
  have edge : tree.HierarchyChild parentNode childNode :=
    ⟨address.getLast address_ne, (List.dropLast_concat_getLast address_ne).symm⟩
  have hdup := generatedSourceTree_duplicateDistancesCorrect input tree center ligand
    generated rootEq parentNode childNode edge
  have hlabel := childLabel_eq_toDeclarative tree address subtree lookup present
  rw [show tree.toDeclarativeDigraph.label childNode = subtree.source.toDeclarativeLabel from
    hlabel] at hdup
  rw [toDeclarativeLabel, hprov, toDeclarative] at hdup
  cases hcur : subtree.source.current? with
  | none =>
      rw [hcur] at hdup
      exact False.elim hdup
  | some atom =>
      rw [hcur] at hdup
      rcases hdup with ⟨_atom, hd⟩ | ⟨ancestor, hpath, _label, hd⟩
      · rw [hd]
        have hpos : 0 < address.length := List.length_pos_iff.mpr address_ne
        omega
      · rw [declarativeAddressing_address] at hd
        have hanc := transGen_hierarchy_length hpath
        have hparent : parentNode.1 = address.dropLast := by
          simp [parentNode]
        rw [hparent] at hanc
        have hdrop := dropLast_length_succ address_ne
        omega

/-- At every generated original-root address, Rule 1b and the sphere determine provenance. -/
theorem sphereProvenanceReadback_of_generatedSubtree (input : CertifiedLocalizedCIPInput)
    (tree : OfficialCIPSourceTree input.Atom) (center ligand : input.Atom)
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren)
    (rootEq : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (address : List ℕ) (subtree : OfficialCIPSourceTree input.Atom)
    (lookup : tree.subtreeAt? address = some subtree) :
    SphereProvenanceReadback subtree.source (address.length + 1) := by
  have occ := mem_occurrences_of_subtreeAt?_eq_some address tree subtree lookup
  have present := mem_hierarchyAddresses_of_occurrence tree (address, subtree.source) occ
  let childNode : tree.HierarchyNode := ⟨address, present⟩
  have hlen := generatedSourceTree_history_length input tree center ligand generated rootEq
    childNode subtree lookup
  have hgen := generatedSourceTree_source_graphGenerated input tree center ligand generated rootEq
    childNode subtree lookup
  cases hprov : subtree.source.provenance with
  | realAtom =>
      have hrule : subtree.source.rule1bRootDistance = address.length + 1 := by
        have hlenAddr : subtree.source.history.length = address.length + 2 := by
          simpa [childNode] using hlen
        simp only [rule1bRootDistance, hprov, depth, hlenAddr]
        omega
      refine ⟨hgen, ?_, ?_, ?_, ?_⟩
      · rw [hrule, hprov]
        unfold provenanceOfDistance collapseProvenance
        rw [if_pos rfl]
      · exact ⟨fun _ => hprov, fun _ => hrule⟩
      · intro d
        constructor
        · intro h
          rw [hprov] at h
          nomatch h
        · rintro ⟨hd, hs⟩
          rw [← hd, hrule] at hs
          omega
      · intro d
        constructor
        · intro h
          rw [hprov] at h
          nomatch h
        · rintro ⟨hd, hs⟩
          rw [← hd, hrule] at hs
          omega
  | multipleBondDuplicate d =>
      have hsphere := multipleBond_succ_eq_sphere tree center ligand generated rootEq address
        subtree lookup d hprov
      have hrule : subtree.source.rule1bRootDistance = d := by
        simp [rule1bRootDistance, hprov]
      have hne : d ≠ address.length + 1 := by
        intro h
        rw [h] at hsphere
        omega
      refine ⟨hgen, ?_, ?_, ?_, ?_⟩
      · rw [hrule, hprov]
        unfold provenanceOfDistance collapseProvenance
        rw [if_neg hne, if_pos hsphere]
      · constructor
        · intro hs
          rw [hrule] at hs
          exact absurd hs hne
        · intro h
          rw [hprov] at h
          nomatch h
      · intro d'
        constructor
        · intro h
          rw [hprov] at h
          cases h
          exact ⟨hrule, hsphere⟩
        · rintro ⟨hd, hs⟩
          have : d' = d := by rw [← hd, hrule]
          rw [this, hprov]
      · intro d'
        constructor
        · intro h
          rw [hprov] at h
          nomatch h
        · rintro ⟨hd, hs⟩
          rw [← hd, hrule] at hs
          omega
  | ringDuplicate d =>
      have hlt := ring_succ_lt_sphere tree center ligand generated rootEq address subtree lookup
        d hprov
      have hrule : subtree.source.rule1bRootDistance = d := by
        simp [rule1bRootDistance, hprov]
      have hne : d ≠ address.length + 1 := by
        intro h
        rw [h] at hlt
        omega
      have hneSucc : ¬ d + 1 = address.length + 1 := by
        intro h
        rw [h] at hlt
        omega
      refine ⟨hgen, ?_, ?_, ?_, ?_⟩
      · rw [hrule, hprov]
        unfold provenanceOfDistance collapseProvenance
        rw [if_neg hne, if_neg hneSucc]
      · constructor
        · intro hs
          rw [hrule] at hs
          exact absurd hs hne
        · intro h
          rw [hprov] at h
          nomatch h
      · intro d'
        constructor
        · intro h
          rw [hprov] at h
          nomatch h
        · rintro ⟨hd, hs⟩
          rw [← hd, hrule] at hs
          exact absurd hs hneSucc
      · intro d'
        constructor
        · intro h
          rw [hprov] at h
          cases h
          exact ⟨hrule, hlt⟩
        · rintro ⟨hd, _hs⟩
          have : d' = d := by rw [← hd, hrule]
          rw [this, hprov]
  | placeholder _ _ =>
      simp [GraphGenerated, hprov] at hgen

/-- One occupied address of an actual arm, decoded from that arm's official source node. -/
structure AddressedRetainedReadback {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read) (address : List ℕ)
    (subtree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)) : Prop where
  atAddress : (retainedObservationTree arm).atAddress? address =
    some (ofShape (address.length + 1) subtree.shape)
  atomicNumber_eq : (ofShape (address.length + 1) subtree.shape).atomicNumber =
    (ofLex (input.moleculeGraph.officialNodeAtomLabel subtree.source.occurrence.1.node)).1
  isotopeMass_eq : (ofShape (address.length + 1) subtree.shape).isotopeMass =
    (ofLex (input.moleculeGraph.officialNodeAtomLabel subtree.source.occurrence.1.node)).2
  provenance_eq : (ofShape (address.length + 1) subtree.shape).provenance =
    collapseProvenance subtree.source.occurrence.1.node.provenance
  sphere : SphereProvenanceReadback subtree.source.occurrence.1.node (address.length + 1)

theorem addressedRetainedReadback {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read) (address : List ℕ)
    (subtree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1))
    (lookup : arm.tree.decoratedSubtreeAt? address = some subtree) :
    AddressedRetainedReadback arm address subtree := by
  have hat := atAddress?_ofShape_shape 1 arm.tree address subtree lookup
  have hnat : 1 + address.length = address.length + 1 := by omega
  rw [hnat] at hat
  have realized := realizes_of_decoratedSubtreeAt? arm.tree arm.realizes address subtree lookup
  have hoff := toOfficialSourceTree_subtreeAt? arm.tree address
  rw [lookup] at hoff
  simp only [Option.map_some] at hoff
  have readback := sphereProvenanceReadback_of_generatedSubtree input
    (toOfficialSourceTree arm.tree) center.1 (input.canonicalLigandAtom center index)
    arm.generated arm.root address (toOfficialSourceTree subtree) hoff
  have hsource := toOfficialSourceTree_source subtree
  rw [hsource] at readback
  have fields := ofShape_shape_fields (address.length + 1) subtree
  refine ⟨?_, ?_, ?_, ?_, readback⟩
  · unfold retainedObservationTree
    exact hat
  · rw [fields.1]
    rw [realized]
    rfl
  · rw [fields.2.1]
    rw [realized]
    rfl
  · rw [fields.2.2]
    rw [realized]
    exact readback.classified

/-! ## Primitive values present in the label -/

/-- A real production label is atomic number and isotope mass. Formal charge is not a component. -/
theorem real_primitive_values {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (atom : V)
    (current : node.current? = some atom) (real : node.provenance = .realAtom) :
    (ofLex (m.officialNodeAtomLabel node)).1 = m.atomZ atom ∧
      (ofLex (m.officialNodeAtomLabel node)).2 = m.atomMass atom := by
  cases node with
  | mk current? history provenance =>
      cases current? with
      | none => simp at current
      | some atom' =>
          cases current
          cases real
          simp [MoleculeGraph.officialNodeAtomLabel, MoleculeGraph.rawCIPAtomLabel]

/-- A graph-generated duplicate keeps the represented atomic number and writes mass 0. -/
theorem duplicate_primitive_values {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (atom : V)
    (current : node.current? = some atom) (generated : node.GraphGenerated)
    (notReal : node.provenance ≠ .realAtom) :
    (ofLex (m.officialNodeAtomLabel node)).1 = m.atomZ atom ∧
      (ofLex (m.officialNodeAtomLabel node)).2 = 0 := by
  cases node with
  | mk current? history provenance =>
      cases current? with
      | none => simp at current
      | some atom' =>
          cases current
          cases provenance with
          | realAtom => exact absurd rfl notReal
          | multipleBondDuplicate _ =>
              simp [MoleculeGraph.officialNodeAtomLabel]
          | ringDuplicate _ =>
              simp [MoleculeGraph.officialNodeAtomLabel]
          | placeholder _ _ =>
              simp [GraphGenerated] at generated

end

assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback.actualOriginalRootArm_built
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback.key_eq_of_originalRootArm
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback.tree_columns_eq_key
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback.constitutionalColumns_eq_of_compare_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback.shape_eq_of_constitutional_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback.map_shape_decoratedSubtreeAt?
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback.retainedObservationTree_eq_of_arm_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback.retainedObservationTree_eq_of_actual_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback.retainedObservationTree_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback.sphereProvenanceReadback_of_generatedSubtree
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback.addressedRetainedReadback
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback.real_primitive_values
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback.duplicate_primitive_values
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback.ofShape_children

end TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback
