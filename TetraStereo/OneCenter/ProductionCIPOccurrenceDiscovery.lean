import TetraStereo.OneCenter.ProductionCIPExactExpansion

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace ProductionCIPOccurrenceDiscovery

/-!
# Exhaustive production occurrence discovery

The production occurrence carrier is computed from the molecule.  A final unit is an annotated,
ordinary tetrahedral center with exactly four production ligand entries.  There is exactly one
center root per final unit.  Its hierarchy consists of an explicit center node and four
slot-indexed canonical branches returned by `branchCanonicalKey?`.

The composite center hierarchy is intentional.  The ordinary branch compiler accepts at most
three children below a branch node, so applying it directly to a four-ligand center either refuses
or, at a three-coordinate lone-pair center, omits the phantom ligand.  Compiling the four ligand
branches independently preserves the production branch algorithm while representing the center
and its phantom slot exactly.
-/

/-! ## Molecule-derived final units and roots -/

/-- Eligibility for the occurrence-level tetrahedral fixed point.  Extended-tetrahedral parity
carriers are separate stereogenic units, and a tetrahedral descriptor equation requires exactly
four production ligand positions. -/
def FinalUnitEligible (mol : RawMolecule) (center : Fin mol.atomCount) : Prop :=
  ((mol.atomAt? center.val).any fun spec => spec.tetrahedral?.isSome) = true ∧
    mol.isExtendedTetrahedralParityCarrier center.val = false ∧
      (mol.ligandsWithLonePair center.val).length = 4

instance (mol : RawMolecule) (center : Fin mol.atomCount) :
    Decidable (FinalUnitEligible mol center) := by
  unfold FinalUnitEligible
  infer_instance

/-- The exact finite set of production tetrahedral final units. -/
def finalUnitFinset (mol : RawMolecule) : Finset (Fin mol.atomCount) :=
  Finset.univ.filter fun center => FinalUnitEligible mol center

/-- A final unit is an atom in the molecule-derived eligible-center finset. -/
abbrev FinalUnit (mol : RawMolecule) :=
  { center : Fin mol.atomCount // center ∈ finalUnitFinset mol }

/-- There is one and only one canonical center root per final unit. -/
abbrev Root (mol : RawMolecule) := FinalUnit mol

def centerAtom {mol : RawMolecule} (unit : FinalUnit mol) : Fin mol.atomCount :=
  unit.1

@[simp] theorem finalUnit_eligible {mol : RawMolecule} (unit : FinalUnit mol) :
    FinalUnitEligible mol (centerAtom unit) := by
  have membership : unit.1 ∈ finalUnitFinset mol := unit.2
  unfold finalUnitFinset at membership
  exact (Finset.mem_filter.mp membership).2

@[simp] theorem finalUnit_fourLigands {mol : RawMolecule} (unit : FinalUnit mol) :
    (mol.ligandsWithLonePair (centerAtom unit).val).length = 4 :=
  (finalUnit_eligible unit).2.2

@[simp] theorem finalUnit_annotated {mol : RawMolecule} (unit : FinalUnit mol) :
    ((mol.atomAt? (centerAtom unit).val).any fun spec => spec.tetrahedral?.isSome) = true :=
  (finalUnit_eligible unit).1

@[simp] theorem finalUnit_notExtended {mol : RawMolecule} (unit : FinalUnit mol) :
    mol.isExtendedTetrahedralParityCarrier (centerAtom unit).val = false :=
  (finalUnit_eligible unit).2.1

/-- Executable eligibility filter at one finite atom index. -/
def rootAt? (mol : RawMolecule) (center : Fin mol.atomCount) : Option (Root mol) :=
  if eligible : FinalUnitEligible mol center then
    some ⟨center, by simp [finalUnitFinset, eligible]⟩
  else none

@[simp] theorem rootAt?_center (mol : RawMolecule) (root : Root mol) :
    rootAt? mol root.1 = some root := by
  unfold rootAt?
  split
  · congr
  · rename_i ineligible
    exact (ineligible (finalUnit_eligible root)).elim

/-- Canonical executable roots in increasing atom-index order. -/
def allRoots (mol : RawMolecule) : List (Root mol) :=
  (List.finRange mol.atomCount).filterMap (rootAt? mol)

@[simp] theorem root_mem_allRoots (mol : RawMolecule) (root : Root mol) :
    root ∈ allRoots mol := by
  rw [allRoots, List.mem_filterMap]
  exact ⟨root.1, by simp, rootAt?_center mol root⟩

theorem allRoots_nodup (mol : RawMolecule) : (allRoots mol).Nodup :=
  List.Nodup.filterMap (l := List.finRange mol.atomCount) (f := rootAt? mol) (by
    intro left right root leftMem rightMem
    unfold rootAt? at leftMem rightMem
    split at leftMem
    · split at rightMem
      · simp only [Option.mem_def, Option.some.injEq] at leftMem rightMem
        exact (congrArg Subtype.val leftMem).trans
          (congrArg Subtype.val rightMem).symm
      · simp at rightMem
    · simp at leftMem) (List.nodup_finRange mol.atomCount)

@[simp] theorem root_center_injective (mol : RawMolecule) :
    Function.Injective (fun root : Root mol => centerAtom root) :=
  Subtype.val_injective

/-- The molecule-derived root list covers every eligible center exactly once. -/
theorem root_coverage_unique (mol : RawMolecule) (center : Fin mol.atomCount)
    (eligible : FinalUnitEligible mol center) :
    ∃! root : Root mol, centerAtom root = center := by
  let root : Root mol := ⟨center, by simpa [finalUnitFinset] using eligible⟩
  refine ⟨root, rfl, ?_⟩
  intro other hother
  exact Subtype.ext hother

/-! ## The four production ligand positions -/

/-- Convert a tetrahedral slot to the dependent index of the actual production ligand list. -/
def ligandListPosition {mol : RawMolecule} (root : Root mol) (slot : Fin 4) :
    Fin (mol.ligandsWithLonePair (centerAtom root).val).length :=
  ⟨slot.val, by rw [finalUnit_fourLigands root]; exact slot.isLt⟩

/-- Actual production ligand value.  It is a `Nat`, not `Fin mol.atomCount`, because the lone pair
is represented by the exact value `mol.atomCount`. -/
def ligandAtom {mol : RawMolecule} (root : Root mol) (slot : Fin 4) : Nat :=
  (mol.ligandsWithLonePair (centerAtom root).val).get (ligandListPosition root slot)

@[simp] theorem ligandAtom_mem {mol : RawMolecule} (root : Root mol) (slot : Fin 4) :
    ligandAtom root slot ∈ mol.ligandsWithLonePair (centerAtom root).val :=
  List.get_mem _ _

/-- Root node used by the production branch compiler at one tetrahedral slot. -/
def ligandRootNode {mol : RawMolecule} (root : Root mol) (slot : Fin 4) :
    RawMolecule.CanonicalBranchNode :=
  RawMolecule.canonicalRoot (centerAtom root).val (ligandAtom root slot)

/-- Lone-pair-aware four-cursor frame.  The incoming reference is the center occurrence, exactly
as for real children returned by `CanonicalRerootCursor.children`; unlike that function, this
definition also includes the phantom ligand from `ligandsWithLonePair`. -/
def ligandCursor {mol : RawMolecule} (root : Root mol) (slot : Fin 4) :
    CanonicalRerootCursor :=
  { node := ligandRootNode root slot
    previous? := some (canonicalCenterRoot (centerAtom root).val) }

def ligandCursors {mol : RawMolecule} (root : Root mol) : List CanonicalRerootCursor :=
  List.ofFn (ligandCursor root)

@[simp] theorem ligandCursors_length {mol : RawMolecule} (root : Root mol) :
    (ligandCursors root).length = 4 := by
  simp [ligandCursors]

@[simp] theorem ligandCursor_previous {mol : RawMolecule} (root : Root mol) (slot : Fin 4) :
    (ligandCursor root slot).previous? = some (canonicalCenterRoot (centerAtom root).val) :=
  rfl

@[simp] theorem ligandCursor_atom {mol : RawMolecule} (root : Root mol) (slot : Fin 4) :
    (ligandCursor root slot).node.atom = ligandAtom root slot :=
  rfl

theorem phantom_ligand_cursor {mol : RawMolecule} (root : Root mol) (slot : Fin 4)
    (phantom : ligandAtom root slot = mol.atomCount) :
    (ligandCursor root slot).node.atom = mol.atomCount ∧
      (ligandCursor root slot).previous? = some (canonicalCenterRoot (centerAtom root).val) := by
  exact ⟨phantom, rfl⟩

/-! ## Mandatory executable branch discovery -/

/-- Proof-carrying result of the actual production branch compiler.  The ligand is deliberately
natural-number valued so a phantom root is representable. -/
structure CompleteBranchDiscovery (mol : RawMolecule)
    (center : Fin mol.atomCount) (ligand : Nat) where
  key : RawMolecule.CanonicalBranchKey
  accepted : branchCanonicalKey? mol center.val ligand = some key
  complete : key.complete = true

namespace CompleteBranchDiscovery

/-- Execute production branch discovery and retain only a complete result. -/
def discover? (mol : RawMolecule) (center : Fin mol.atomCount) (ligand : Nat) :
    Option (CompleteBranchDiscovery mol center ligand) :=
  match hkey : branchCanonicalKey? mol center.val ligand with
  | none => none
  | some key =>
      if hcomplete : key.complete = true then some ⟨key, hkey, hcomplete⟩ else none

@[simp] theorem discover?_eq_some
    {mol : RawMolecule} {center : Fin mol.atomCount} {ligand : Nat}
    (discovery : CompleteBranchDiscovery mol center ligand) :
    discover? mol center ligand = some discovery := by
  unfold discover?
  split
  · rename_i hresult
    have impossible : (none : Option RawMolecule.CanonicalBranchKey) = some discovery.key :=
      hresult.symm.trans discovery.accepted
    simp at impossible
  · rename_i key hresult
    have key_eq : key = discovery.key :=
      Option.some.inj (hresult.symm.trans discovery.accepted)
    subst key
    split
    · congr
    · rename_i incomplete
      exact (incomplete discovery.complete).elim

/-- Successful executable discovery supplies the semantic complete-build derivation. -/
theorem completeBuild
    {mol : RawMolecule} {center : Fin mol.atomCount} {ligand : Nat}
    (discovery : CompleteBranchDiscovery mol center ligand) :
    RawMolecule.CanonicalCompleteBuild mol
      (RawMolecule.canonicalRoot center.val ligand) discovery.key :=
  mol.branchCanonicalKey?_completeBuild center.val ligand discovery.key
    discovery.accepted discovery.complete

@[simp] theorem rootedAt
    {mol : RawMolecule} {center : Fin mol.atomCount} {ligand : Nat}
    (discovery : CompleteBranchDiscovery mol center ligand) :
    discovery.key.RootedAt center.val ligand :=
  discovery.completeBuild.rootedAt

theorem childrenExact
    {mol : RawMolecule} {center : Fin mol.atomCount} {ligand : Nat}
    (discovery : CompleteBranchDiscovery mol center ligand) :
    discovery.key.ChildrenExact mol :=
  discovery.completeBuild.childrenExact

/-- One exact occurrence in a complete production branch, retaining its rooted source-frame
equation. -/
structure ResolvedBranchOccurrence
    {mol : RawMolecule} {center : Fin mol.atomCount} {ligand : Nat}
    (discovery : CompleteBranchDiscovery mol center ligand) where
  node : discovery.key.HierarchyNode
  source : RawMolecule.CanonicalBranchNode
  source_eq : discovery.key.sourceNodeAtAddress? node.1 = some source

/-- The resolved root of a complete production branch. -/
def resolvedRoot
    {mol : RawMolecule} {center : Fin mol.atomCount} {ligand : Nat}
    (discovery : CompleteBranchDiscovery mol center ligand) :
    ResolvedBranchOccurrence discovery where
  node := ⟨[], discovery.key.nil_mem_hierarchyAddresses⟩
  source := RawMolecule.canonicalRoot center.val ligand
  source_eq := discovery.rootedAt

/-- Select a resolved child through the exact production-child equivalence. -/
noncomputable def resolvedChild
    {mol : RawMolecule} {center : Fin mol.atomCount} {ligand : Nat}
    (discovery : CompleteBranchDiscovery mol center ligand)
    (parent : ResolvedBranchOccurrence discovery)
    (position : Fin (mol.canonicalChildren parent.source).length) :
    ResolvedBranchOccurrence discovery :=
  let exact := discovery.childrenExact parent.node parent.source parent.source_eq
  let equivalence := Classical.choose exact
  let source_eq : discovery.key.sourceNodeAtAddress? (equivalence.symm position).1.1 =
      some ((mol.canonicalChildren parent.source).get position) := by
    have raw := Classical.choose_spec exact (equivalence.symm position)
    rw [equivalence.apply_symm_apply] at raw
    exact raw
  { node := (equivalence.symm position).1
    source := (mol.canonicalChildren parent.source).get position
    source_eq := source_eq }

theorem unique
    {mol : RawMolecule} {center : Fin mol.atomCount} {ligand : Nat}
    (first second : CompleteBranchDiscovery mol center ligand) : first = second := by
  exact Option.some.inj
    ((discover?_eq_some first).symm.trans (discover?_eq_some second))

end CompleteBranchDiscovery

/-- All four production branches of one center.  The dependent field makes omission impossible. -/
structure CenterDiscovery (mol : RawMolecule) (root : Root mol) where
  branch : (slot : Fin 4) →
    CompleteBranchDiscovery mol (centerAtom root) (ligandAtom root slot)

def centerBranchesSucceeded? (mol : RawMolecule) (root : Root mol) : Bool :=
  (List.finRange 4).all fun slot =>
    (CompleteBranchDiscovery.discover? mol (centerAtom root) (ligandAtom root slot)).isSome

theorem centerBranch_isSome_of_succeeded (mol : RawMolecule) (root : Root mol)
    (accepted : centerBranchesSucceeded? mol root = true) (slot : Fin 4) :
    (CompleteBranchDiscovery.discover? mol (centerAtom root) (ligandAtom root slot)).isSome := by
  exact List.all_eq_true.mp accepted slot (by simp)

/-- Center discovery succeeds only when every one of the four actual production branches is
successfully and completely compiled. -/
def discoverCenter? (mol : RawMolecule) (root : Root mol) : Option (CenterDiscovery mol root) :=
  if accepted : centerBranchesSucceeded? mol root = true then
    let discovered := fun slot =>
      Option.get
        (CompleteBranchDiscovery.discover? mol (centerAtom root) (ligandAtom root slot))
        (centerBranch_isSome_of_succeeded mol root accepted slot)
    some { branch := discovered }
  else none

@[simp] theorem discoverCenter?_isSome (mol : RawMolecule) (root : Root mol) :
    (discoverCenter? mol root).isSome = centerBranchesSucceeded? mol root := by
  unfold discoverCenter?
  split <;> simp_all

theorem CenterDiscovery.branch_discovered {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) (slot : Fin 4) :
    CompleteBranchDiscovery.discover? mol (centerAtom root) (ligandAtom root slot) =
      some (discovery.branch slot) :=
  CompleteBranchDiscovery.discover?_eq_some (discovery.branch slot)

theorem CenterDiscovery.unique {mol : RawMolecule} {root : Root mol}
    (first second : CenterDiscovery mol root) : first = second := by
  cases first with
  | mk firstBranch =>
      cases second with
      | mk secondBranch =>
          congr
          funext slot
          exact CompleteBranchDiscovery.unique (firstBranch slot) (secondBranch slot)

theorem CenterDiscovery.branchesSucceeded {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) : centerBranchesSucceeded? mol root = true := by
  unfold centerBranchesSucceeded?
  rw [List.all_eq_true]
  intro slot _
  rw [discovery.branch_discovered slot]
  rfl

/-- Every proof-carrying center family is literally accepted by the executable all-four-branch
discovery function. -/
@[simp] theorem CenterDiscovery.discovered {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) :
    discoverCenter? mol root = some discovery := by
  unfold discoverCenter?
  split
  · exact congrArg some (CenterDiscovery.unique _ _)
  · rename_i rejected
    exact (rejected discovery.branchesSucceeded).elim

/-! ## Composite center-rooted hierarchy -/

/-- One explicit center node, followed by the nodes of each slot-indexed complete branch. -/
abbrev HierarchyNode {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) :=
  Unit ⊕ ((slot : Fin 4) ×
    ((discovery.branch slot).key.toDeclarativeDigraph mol).Node)

noncomputable instance hierarchyNodeFintype
    {mol : RawMolecule} {root : Root mol} (discovery : CenterDiscovery mol root) :
    Fintype (HierarchyNode discovery) := by
  letI (slot : Fin 4) :
      Fintype (((discovery.branch slot).key.toDeclarativeDigraph mol).Node) :=
    ((discovery.branch slot).key.toDeclarativeDigraph mol).nodeFintype
  infer_instance

noncomputable instance hierarchyNodeDecidableEq
    {mol : RawMolecule} {root : Root mol} (discovery : CenterDiscovery mol root) :
    DecidableEq (HierarchyNode discovery) :=
  Classical.decEq _

def centerNode {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) : HierarchyNode discovery :=
  Sum.inl ()

def branchNode {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) (slot : Fin 4)
    (node : ((discovery.branch slot).key.toDeclarativeDigraph mol).Node) :
    HierarchyNode discovery :=
  Sum.inr ⟨slot, node⟩

/-- Center-relative address.  `[]` denotes the physical center; a branch address is prefixed by
its tetrahedral ligand slot. -/
def address {mol : RawMolecule} {root : Root mol} {discovery : CenterDiscovery mol root} :
    HierarchyNode discovery → List Nat
  | .inl _ => []
  | .inr branch => branch.1.val :: branch.2.1

@[simp] theorem address_center {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) :
    address (centerNode discovery) = [] :=
  rfl

@[simp] theorem address_branch {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) (slot : Fin 4)
    (node : ((discovery.branch slot).key.toDeclarativeDigraph mol).Node) :
    address (branchNode discovery slot node) = slot.val :: node.1 :=
  rfl

/-- Root plus address is a complete occurrence identity. -/
theorem address_injective {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) : Function.Injective (@address mol root discovery) := by
  intro left right equal
  rcases left with center | left
  · rcases right with center | right
    · rfl
    · simp [address] at equal
  · rcases right with center | right
    · simp [address] at equal
    · rcases left with ⟨leftSlot, leftNode⟩
      rcases right with ⟨rightSlot, rightNode⟩
      simp only [address, List.cons.injEq] at equal
      have slot_eq : leftSlot = rightSlot := Fin.ext equal.1
      subst rightSlot
      have node_eq : leftNode = rightNode := Subtype.ext equal.2
      subst rightNode
      rfl

/-- Resolve a composite node to its exact production source occurrence. -/
def sourceNode? {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) :
    HierarchyNode discovery → Option RawMolecule.CanonicalBranchNode
  | .inl _ => some (canonicalCenterRoot (centerAtom root).val)
  | .inr branch =>
      (discovery.branch branch.1).key.sourceNodeAtAddress? branch.2.1

@[simp] theorem sourceNode?_center {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) :
    sourceNode? discovery (centerNode discovery) =
      some (canonicalCenterRoot (centerAtom root).val) :=
  rfl

theorem branch_source_exists {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) (slot : Fin 4)
    (node : ((discovery.branch slot).key.toDeclarativeDigraph mol).Node) :
    ∃ source, sourceNode? discovery (branchNode discovery slot node) = some source := by
  have complete := (discovery.branch slot).key.sourceComplete_of_root_and_childrenExact mol
    (RawMolecule.canonicalRoot (centerAtom root).val (ligandAtom root slot))
    (discovery.branch slot).rootedAt (discovery.branch slot).childrenExact
  exact complete node

/-- Every admitted composite occurrence has an actual production source node. -/
theorem source_exists {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) (node : HierarchyNode discovery) :
    ∃ source, sourceNode? discovery node = some source := by
  rcases node with center | branch
  · exact ⟨canonicalCenterRoot (centerAtom root).val, rfl⟩
  · rcases branch with ⟨slot, node⟩
    exact branch_source_exists discovery slot node

/-- Semantic completeness of the composite hierarchy: its distinguished root is the production
center and every one of its four branch subhierarchies has an exact complete-build derivation. -/
structure CompleteCenterHierarchy {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) : Prop where
  centerExact : sourceNode? discovery (centerNode discovery) =
    some (canonicalCenterRoot (centerAtom root).val)
  branchComplete : ∀ slot : Fin 4,
    RawMolecule.CanonicalCompleteBuild mol
      (ligandRootNode root slot) (discovery.branch slot).key

theorem completeCenterHierarchy {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) : CompleteCenterHierarchy discovery where
  centerExact := rfl
  branchComplete := fun slot => (discovery.branch slot).completeBuild

/-! ## Exhaustive discovery and occurrences -/

/-- A total discovered family over the exact molecule-derived root type.  Its dependent function
cannot omit a root, and the root type itself has no duplicate constructors. -/
structure Discovery (mol : RawMolecule) where
  center : (root : Root mol) → CenterDiscovery mol root

theorem Discovery.center_discovered {mol : RawMolecule} (discovery : Discovery mol)
    (root : Root mol) :
    discoverCenter? mol root = some (discovery.center root) :=
  (discovery.center root).discovered

theorem Discovery.unique {mol : RawMolecule} (first second : Discovery mol) : first = second := by
  cases first with
  | mk firstCenter =>
      cases second with
      | mk secondCenter =>
          congr
          funext root
          exact CenterDiscovery.unique (firstCenter root) (secondCenter root)

def allCentersSucceeded? (mol : RawMolecule) : Bool :=
  (allRoots mol).all fun root => (discoverCenter? mol root).isSome

theorem center_isSome_of_all_succeeded (mol : RawMolecule)
    (accepted : allCentersSucceeded? mol = true) (root : Root mol) :
    (discoverCenter? mol root).isSome := by
  exact List.all_eq_true.mp accepted root (root_mem_allRoots mol root)

/-- Execute complete occurrence discovery for every production root, or fail as a whole. -/
def discoverAll? (mol : RawMolecule) : Option (Discovery mol) :=
  if accepted : allCentersSucceeded? mol = true then
    some { center := fun root =>
      (discoverCenter? mol root).get (center_isSome_of_all_succeeded mol accepted root) }
  else none

theorem Discovery.allCentersSucceeded {mol : RawMolecule} (discovery : Discovery mol) :
    allCentersSucceeded? mol = true := by
  unfold allCentersSucceeded?
  rw [List.all_eq_true]
  intro root _
  rw [discovery.center_discovered root]
  rfl

/-- Every total proof-carrying family is literally returned by exhaustive executable discovery.
Together with `center_discovered`, this connects stored center and branch data to the concrete
production executions at every molecule-derived root. -/
@[simp] theorem Discovery.discovered {mol : RawMolecule} (discovery : Discovery mol) :
    discoverAll? mol = some discovery := by
  unfold discoverAll?
  split
  · exact congrArg some (Discovery.unique _ _)
  · rename_i rejected
    exact (rejected discovery.allCentersSucceeded).elim

@[simp] theorem discoverAll?_isSome (mol : RawMolecule) :
    (discoverAll? mol).isSome = allCentersSucceeded? mol := by
  unfold discoverAll?
  split <;> simp_all

/-- One root-relative occurrence in the exhaustive production family. -/
structure Occurrence {mol : RawMolecule} (discovery : Discovery mol) where
  root : Root mol
  node : HierarchyNode (discovery.center root)

def occurrenceEquivSigma {mol : RawMolecule} (discovery : Discovery mol) :
    Occurrence discovery ≃ ((root : Root mol) × HierarchyNode (discovery.center root)) where
  toFun occurrence := ⟨occurrence.root, occurrence.node⟩
  invFun occurrence := ⟨occurrence.1, occurrence.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance occurrenceFintype {mol : RawMolecule} (discovery : Discovery mol) :
    Fintype (Occurrence discovery) := by
  letI (root : Root mol) : Fintype (HierarchyNode (discovery.center root)) :=
    hierarchyNodeFintype (discovery.center root)
  exact Fintype.ofEquiv
    ((root : Root mol) × HierarchyNode (discovery.center root))
    (occurrenceEquivSigma discovery).symm

noncomputable instance occurrenceDecidableEq {mol : RawMolecule} (discovery : Discovery mol) :
    DecidableEq (Occurrence discovery) :=
  Classical.decEq _

/-- Namespace-compatible occurrence carrier for downstream production bridges. -/
abbrev Discovery.Occurrence {mol : RawMolecule} (discovery : Discovery mol) :=
  ProductionCIPOccurrenceDiscovery.Occurrence discovery

def Occurrence.address {mol : RawMolecule} {discovery : Discovery mol}
    (occurrence : Occurrence discovery) : List Nat :=
  ProductionCIPOccurrenceDiscovery.address occurrence.node

def Occurrence.sourceNode? {mol : RawMolecule} {discovery : Discovery mol}
    (occurrence : Occurrence discovery) : Option RawMolecule.CanonicalBranchNode :=
  ProductionCIPOccurrenceDiscovery.sourceNode? (discovery.center occurrence.root) occurrence.node

theorem Occurrence.source_exists {mol : RawMolecule} {discovery : Discovery mol}
    (occurrence : Occurrence discovery) :
    ∃ source, occurrence.sourceNode? = some source :=
  ProductionCIPOccurrenceDiscovery.source_exists (discovery.center occurrence.root) occurrence.node

/-- The distinguished final occurrence at one root. -/
def finalOccurrence {mol : RawMolecule} (discovery : Discovery mol) (root : Root mol) :
    Occurrence discovery :=
  ⟨root, centerNode (discovery.center root)⟩

@[simp] theorem finalOccurrence_address {mol : RawMolecule} (discovery : Discovery mol)
    (root : Root mol) :
    (finalOccurrence discovery root).address = [] :=
  rfl

@[simp] theorem finalOccurrence_source {mol : RawMolecule} (discovery : Discovery mol)
    (root : Root mol) :
    (finalOccurrence discovery root).sourceNode? =
      some (canonicalCenterRoot (centerAtom root).val) :=
  rfl

/-- Final projection is tied to the production center, not to an arbitrary unit mapping. -/
@[simp] theorem finalOccurrence_source_atom {mol : RawMolecule} (discovery : Discovery mol)
    (root : Root mol) :
    ((finalOccurrence discovery root).sourceNode?).map
      RawMolecule.CanonicalBranchNode.atom = some (centerAtom root).val := by
  rfl

/-- Root and center-relative address determine a discovered occurrence uniquely. -/
theorem Occurrence.eq_of_root_eq_address_eq
    {mol : RawMolecule} {discovery : Discovery mol}
    (left right : Occurrence discovery)
    (root_eq : left.root = right.root) (address_eq : left.address = right.address) :
    left = right := by
  rcases left with ⟨leftRoot, leftNode⟩
  rcases right with ⟨rightRoot, rightNode⟩
  dsimp only at root_eq
  subst rightRoot
  have node_eq : leftNode = rightNode :=
    address_injective (discovery.center leftRoot) address_eq
  subst rightNode
  rfl

end ProductionCIPOccurrenceDiscovery
end OneCenter
end TetraStereo
