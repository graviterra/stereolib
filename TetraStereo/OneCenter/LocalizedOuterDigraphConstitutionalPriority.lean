import TetraStereo.OneCenter.LocalizedOuterDigraphPhysicalObservations
import TetraStereo.OneCenter.LocalizedConstitutionalRootSeparation
import TetraStereo.OneCenter.LocalizedSparsePhysicalFirstDifference
import TetraStereo.OneCenter.LocalizedSparseAddressReconstruction
import TetraStereo.OneCenter.LocalizedActualTableAddressOrder
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput














































variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
variable {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}

/-! ## Comparator direction realizes the relational outcomes -/

namespace OfficialRuleMajorKey

/-- The actual natural-number comparator realizes `DescendingNatOutcome`: `gt` means the left
value is larger, `lt` means the right value is larger, `eq` means equality. -/
theorem compareNat_eq_iff_descendingNatOutcome (left right : Nat) (outcome : Ordering) :
    compareNat left right = outcome ↔ DeclarativeCIP.DescendingNatOutcome left right outcome := by
  cases outcome with
  | lt =>
      constructor
      · intro h
        exact .lt (compare_lt_iff_lt.mp (by simpa [compareNat] using h))
      · intro h
        cases h with
        | lt lower => simpa [compareNat] using (compare_lt_iff_lt.mpr lower)
  | eq =>
      constructor
      · intro h
        exact .eq (compare_eq_iff_eq.mp (by simpa [compareNat] using h))
      · intro h
        cases h with
        | eq equal => simpa [compareNat] using (compare_eq_iff_eq.mpr equal)
  | gt =>
      constructor
      · intro h
        exact .gt (compare_gt_iff_gt.mp (by simpa [compareNat] using h))
      · intro h
        cases h with
        | gt higher => simpa [compareNat] using (compare_gt_iff_gt.mpr higher)

/-- The actual Rule 1b comparator (`flip compareNat`) realizes `Rule1bDistanceOutcome`: `gt`
means the left distance is smaller (left senior), `lt` means the right distance is smaller, `eq`
means equality. -/
theorem compareRule1b_eq_iff_rule1bDistanceOutcome (left right : Nat) (outcome : Ordering) :
    compareRule1b left right = outcome ↔
      DeclarativeCIP.Rule1bDistanceOutcome left right outcome := by
  cases outcome with
  | lt =>
      constructor
      · intro h
        exact .lt (compare_lt_iff_lt.mp (by simpa [compareRule1b, compareNat, flip] using h))
      · intro h
        cases h with
        | lt higher => simpa [compareRule1b, compareNat, flip] using (compare_lt_iff_lt.mpr higher)
  | eq =>
      constructor
      · intro h
        exact .eq ((compare_eq_iff_eq (a := right) (b := left)).mp
          (by simpa [compareRule1b, compareNat, flip] using h)).symm
      · intro h
        cases h with
        | eq equal =>
            simpa [compareRule1b, compareNat, flip] using
              ((compare_eq_iff_eq (a := right) (b := left)).mpr equal.symm)
  | gt =>
      constructor
      · intro h
        exact .gt (compare_gt_iff_gt.mp (by simpa [compareRule1b, compareNat, flip] using h))
      · intro h
        cases h with
        | gt lower => simpa [compareRule1b, compareNat, flip] using (compare_gt_iff_gt.mpr lower)

/-! ## First-sphere realization of the relational outcomes -/

/-- A strict descending atomic-number outcome realizes the addressed Rule-1a sparse comparison as
`gt` (left senior). -/
theorem compare_rule1a_eq_gt_of_descendingNat_gt {V : Type*}
    {left right : OfficialRuleMajorKey V} {leftZ rightZ : Nat}
    (leftHead : left.rule1a.head? = some [([], leftZ)])
    (rightHead : right.rule1a.head? = some [([], rightZ)])
    (senior : DeclarativeCIP.DescendingNatOutcome leftZ rightZ Ordering.gt) :
    compareSparseLayers compareNat left.rule1a right.rule1a = Ordering.gt := by
  cases senior with
  | gt higher =>
      exact MoleculeGraph.officialRuleMajorKey_compare_rule1a_gt_of_heads_gt
        leftHead rightHead higher

/-- A strict descending atomic-number outcome realizes the addressed Rule-1a sparse comparison as
`lt` (right senior). -/
theorem compare_rule1a_eq_lt_of_descendingNat_lt {V : Type*}
    {left right : OfficialRuleMajorKey V} {leftZ rightZ : Nat}
    (leftHead : left.rule1a.head? = some [([], leftZ)])
    (rightHead : right.rule1a.head? = some [([], rightZ)])
    (junior : DeclarativeCIP.DescendingNatOutcome leftZ rightZ Ordering.lt) :
    compareSparseLayers compareNat left.rule1a right.rule1a = Ordering.lt := by
  cases junior with
  | lt lower =>
      exact MoleculeGraph.officialRuleMajorKey_compare_rule1a_lt_of_heads_lt
        leftHead rightHead lower

/-- A strict Rule-1b distance outcome (left nearer, hence senior) realizes the addressed Rule-1b
sparse comparison as `gt`. -/
theorem compare_rule1b_eq_gt_of_rule1bDistance_gt {V : Type*}
    {left right : OfficialRuleMajorKey V} {leftDistance rightDistance : Nat}
    (leftHead : left.rule1b.head? = some [([], leftDistance)])
    (rightHead : right.rule1b.head? = some [([], rightDistance)])
    (senior : DeclarativeCIP.Rule1bDistanceOutcome leftDistance rightDistance Ordering.gt) :
    compareSparseLayers compareRule1b left.rule1b right.rule1b = Ordering.gt := by
  cases senior with
  | gt lower =>
      rw [compareSparseLayers_compareRule1b_eq_of_head_distances leftHead rightHead
        (ne_of_lt lower)]
      exact compareRule1b_eq_gt_of_lt lower

/-- A strict Rule-1b distance outcome (right nearer, hence senior) realizes the addressed Rule-1b
sparse comparison as `lt`. -/
theorem compare_rule1b_eq_lt_of_rule1bDistance_lt {V : Type*}
    {left right : OfficialRuleMajorKey V} {leftDistance rightDistance : Nat}
    (leftHead : left.rule1b.head? = some [([], leftDistance)])
    (rightHead : right.rule1b.head? = some [([], rightDistance)])
    (junior : DeclarativeCIP.Rule1bDistanceOutcome leftDistance rightDistance Ordering.lt) :
    compareSparseLayers compareRule1b left.rule1b right.rule1b = Ordering.lt := by
  cases junior with
  | lt higher =>
      rw [compareSparseLayers_compareRule1b_eq_of_head_distances leftHead rightHead
        (ne_of_gt higher)]
      exact compareRule1b_eq_lt_of_lt higher

end OfficialRuleMajorKey

/-! ## Independent physical priority relation -/

/-- **Independent physical per-node outcome.**

For a fixed original physical `outerRoot`, the seniority of two real atoms under one
constitutional rule is exactly the existing relational outcome on the physical observation
`(graph.atomZ, graph.dist outerRoot, graph.atomMass)`:

* Rule 1a: larger atomic number is senior (`DescendingNatOutcome`);
* Rule 1b: smaller physical distance to `outerRoot` is senior (`Rule1bDistanceOutcome`);
* Rule 2: larger atomic mass is senior (`DescendingNatOutcome`).

This never reads the runtime key or compares keys for equality. -/
noncomputable def physicalConstitutionalNodeOutcome
    (outerRoot : input.Atom) (rule : DeclarativeCIP.ConstitutionalRule)
    (left right : input.Atom) (outcome : Ordering) : Prop :=
  match rule with
  | DeclarativeCIP.ConstitutionalRule.rule1aAtomicNumber =>
      DeclarativeCIP.DescendingNatOutcome
        (input.moleculeGraph.atomZ left) (input.moleculeGraph.atomZ right) outcome
  | DeclarativeCIP.ConstitutionalRule.rule1bDuplicateNodeProximity =>
      DeclarativeCIP.Rule1bDistanceOutcome
        (input.moleculeGraph.underlyingSimpleGraph.dist outerRoot left)
        (input.moleculeGraph.underlyingSimpleGraph.dist outerRoot right) outcome
  | DeclarativeCIP.ConstitutionalRule.rule2AtomicMass =>
      DeclarativeCIP.DescendingNatOutcome
        (input.moleculeGraph.atomMass left) (input.moleculeGraph.atomMass right) outcome

/-- **Independent physical hierarchy outcome.**

The independent semantic priority of two outer-digraph nodes is the existing
`DeclarativeCIP.FirstDifferenceOutcome` over the physical observation schedule
`(graph.atomZ, graph.dist outerRoot, graph.atomMass)` for the single rule `rule`.  This is
transparent and compositional: it is exactly the declared first-difference specification, with
no runtime reader or key comparison. -/
noncomputable def physicalConstitutionalHierarchyOutcome
    (outerRoot : input.Atom) (rule : DeclarativeCIP.ConstitutionalRule)
    (schedule : List Nat → input.Atom × input.Atom) (outcome : Ordering) : Prop :=
  DeclarativeCIP.FirstDifferenceOutcome
    (fun address oc =>
      physicalConstitutionalNodeOutcome outerRoot rule
        (schedule address).1 (schedule address).2 oc)
    outcome

/-! ## Constitutional projection of the actual cumulative sort -/

namespace CertifiedLocalizedCIPInput

/-- A strict constitutional comparison decides the full cumulative Rule 4/5 comparison before any
descriptor is read; later stages cannot alter it. -/
theorem compareLocalizedRerootCumulativeRule45Keys_eq_of_constitutional_decisive
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (decisive : OfficialRuleMajorKey.compare left.constitutional right.constitutional ≠
      Ordering.eq) :
    input.compareLocalizedRerootCumulativeRule45Keys left right =
      OfficialRuleMajorKey.compare left.constitutional right.constitutional := by
  unfold compareLocalizedRerootCumulativeRule45Keys compareLex
  simp only [Ordering.byKey]
  rw [ConstitutionalLexAlgebra.then_eq_left_of_left_ne_eq decisive]

/-- The full cumulative descending sibling order projects to descending constitutional order. -/
theorem officialRuleMajorKey_Descending_of_localizedRerootCumulativeRule45KeysDescending
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootCumulativeRule45Key)
    (descending : input.LocalizedRerootCumulativeRule45KeysDescending keys) :
    OfficialRuleMajorKey.Descending (keys.map fun key => key.constitutional) := by
  unfold OfficialRuleMajorKey.Descending
  induction keys with
  | nil => simp
  | cons head tail ih =>
      rw [List.map_cons, List.pairwise_cons]
      have headOverTail := (List.pairwise_cons.mp descending).1
      have tailDescending := (List.pairwise_cons.mp descending).2
      constructor
      · intro observed present
        rw [List.mem_map] at present
        rcases present with ⟨tailKey, tailPresent, rfl⟩
        by_contra constitutionalLt
        have cumulativeLt :
            input.compareLocalizedRerootCumulativeRule45Keys head tailKey = Ordering.lt := by
          rw [input.compareLocalizedRerootCumulativeRule45Keys_eq_of_constitutional_decisive
            head tailKey (by simp [constitutionalLt])]
          exact constitutionalLt
        exact headOverTail tailKey tailPresent cumulativeLt
      · exact ih tailDescending

/-- The actual production sibling sort is constitutionally descending: the actual hierarchy's
sibling address order is descending for the constitutional relation. -/
theorem sortLocalizedRerootCumulativeRule45Keys_constitutional_descending
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootCumulativeRule45Key) :
    OfficialRuleMajorKey.Descending
      ((input.sortLocalizedRerootCumulativeRule45Keys keys).map fun key => key.constitutional) :=
  input.officialRuleMajorKey_Descending_of_localizedRerootCumulativeRule45KeysDescending
    (input.sortLocalizedRerootCumulativeRule45Keys keys)
    (input.sortLocalizedRerootCumulativeRule45Keys_descending keys)

/-! ## Actual builder root observations -/

/-- The actual builder's produced key always records the raw official root-node observations
(`rule1bRootDistance` for Rule 1b, the official node label components for Rules 1a and 2) in the
head of its three constitutional sparse layers, at every fuel, terminal or not. -/
theorem buildLocalizedRerootCumulativeRule45Key?_constitutional_root_heads
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel cursor = some key →
      key.constitutional.rule1a.head? =
          some [([], (ofLex
            (input.moleculeGraph.officialNodeAtomLabel cursor.occurrence.1.node)).1)] ∧
        key.constitutional.rule1b.head? =
          some [([], cursor.occurrence.1.node.rule1bRootDistance)] ∧
        key.constitutional.rule2.head? =
          some [([], (ofLex
            (input.moleculeGraph.officialNodeAtomLabel cursor.occurrence.1.node)).2)] := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor key computed
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            refine ⟨rfl, rfl, rfl⟩
          · simp [childrenComputed, terminal] at computed
  | succ fuel ih =>
      intro cursor key computed
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            refine ⟨rfl, rfl, rfl⟩
          · cases childKeysComputed :
              (children.mapM fun child => input.buildLocalizedRerootCumulativeRule45Key?
                stage target view fuel child) with
            | none => simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
                subst key
                simp [OfficialRuleMajorKey.assemble]

end CertifiedLocalizedCIPInput

/-! ## Realized-tree source-label alignment -/

/-- A realized decorated tree stores the atomic number of its source node's official label. -/
theorem localizedRootTree_atomicNumber_eq_sourceLabel
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    tree.atomicNumber =
      (ofLex (input.moleculeGraph.officialNodeAtomLabel tree.source.occurrence.1.node)).1 := by
  cases realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize => rfl

/-- A realized decorated tree stores the isotope mass of its source node's official label. -/
theorem localizedRootTree_isotopeMass_eq_sourceLabel
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    tree.isotopeMass =
      (ofLex (input.moleculeGraph.officialNodeAtomLabel tree.source.occurrence.1.node)).2 := by
  cases realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize => rfl

/-! ## The actual builder root observations are physical -/









theorem buildLocalizedRerootCumulativeRule45Key?_root_observations_physical
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (fuel : Nat) (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel
      tree.source = some key) :
    key.constitutional.rule1a.head? =
        some [([], input.moleculeGraph.atomZ
          (positionAtom singleBonded acyclic (rootPosition tree)))] ∧
      key.constitutional.rule1b.head? =
        some [([], input.moleculeGraph.underlyingSimpleGraph.dist
          tree.source.occurrence.1.root
          (positionAtom singleBonded acyclic (rootPosition tree)))] ∧
      key.constitutional.rule2.head? =
        some [([], input.moleculeGraph.atomMass
          (positionAtom singleBonded acyclic (rootPosition tree)))] := by
  obtain ⟨h1a, h1b, h2⟩ :=
    input.buildLocalizedRerootCumulativeRule45Key?_constitutional_root_heads
      stage target view fuel tree.source key computed
  refine ⟨?_, ?_, ?_⟩
  · rw [h1a]
    have hatom := positionAtomicNumber_eq_atomZ singleBonded acyclic realizes (rootPosition tree)
    rw [positionNode_rootPosition] at hatom
    rw [← localizedRootTree_atomicNumber_eq_sourceLabel realizes, hatom]
  · rw [h1b]
    have hdist := positionNode_rule1bDistance_eq_outerRoot_dist singleBonded acyclic realizes
      (rootPosition tree)
    rw [positionNode_rootPosition] at hdist
    rw [← localizedRootTree_rule1bDistance_eq_source realizes, hdist]
  · rw [h2]
    have hmass := positionIsotopeMass_eq_atomMass singleBonded acyclic realizes (rootPosition tree)
    rw [positionNode_rootPosition] at hmass
    rw [← localizedRootTree_isotopeMass_eq_sourceLabel realizes, hmass]

/-! ## Physical cut inventory: reading the addressed table at every present position -/

/-- `init` is bounded by any foldl of `max` over a natural-valued function: the accumulator
never decreases, so the starting bound is preserved along the list. -/
private theorem le_foldl_max_init {β : Type*} (f : β → Nat) :
    ∀ (values : List β) (init : Nat),
      init ≤ values.foldl (fun longest value => max longest (f value)) init := by
  intro values
  induction values with
  | nil => intro init; simp
  | cons head tail ih =>
      intro init
      rw [List.foldl_cons]
      exact le_trans (Nat.le_max_left init (f head)) (ih (max init (f head)))

/-- The `max`-foldl is monotone in its accumulator. -/
private theorem le_foldl_max_step {β : Type*} (f : β → Nat) :
    ∀ (values : List β) (init next : Nat),
      init ≤ next →
        values.foldl (fun longest value => max longest (f value)) init ≤
          values.foldl (fun longest value => max longest (f value)) next := by
  intro values
  induction values with
  | nil => intro init next h; exact h
  | cons head tail ih =>
      intro init next h
      rw [List.foldl_cons]
      exact ih (max init (f head)) (max next (f head))
        (max_le_max h (le_rfl : f head ≤ f head))

/-- Every layer is no longer than the `max`-foldl used by `localizedTreeChildLayerCount`, so a
member layer always has a bound in the merge. -/
private theorem length_le_foldl_max {α : Type*} :
    ∀ (tables : List (List (List (OfficialSparseEntry α)))),
      ∀ table, table ∈ tables →
        table.length ≤ tables.foldl (fun longest table => max longest table.length) 0 := by
  intro tables
  refine List.rec ?nil ?cons tables
  · intro table present
    cases present
  · intro hd tl ih table present
    rw [List.foldl_cons]
    rcases List.mem_cons.mp present with hEq | later
    · subst table
      exact le_trans (Nat.le_max_right 0 (List.length hd))
        (le_foldl_max_init (fun table : List (List (OfficialSparseEntry α)) => List.length table)
          tl (max 0 (List.length hd)))
    · exact le_trans (ih table later)
        (le_foldl_max_step (fun table : List (List (OfficialSparseEntry α)) => List.length table)
          tl 0 (max 0 (List.length hd)) (Nat.le_max_left 0 (List.length hd)))

/-- Reading a sparse layer at a `slot :: rest` address is the same as reading the slot-selected,
head-dropped layer at `rest`: the address head is stripped when the entry begins with that slot,
and entries that do not begin with it do not contribute. -/
private theorem rowValueAt_cons (slot : Nat) (rest : List Nat) :
    ∀ layer : List (OfficialSparseEntry Nat),
      SparsePhysicalFirstDifference.rowValueAt layer (slot :: rest) =
        SparsePhysicalFirstDifference.rowValueAt
          (SparseAddress.dropAddressHeadLayer (SparseAddress.entriesAtSlot slot layer)) rest := by
  intro layer
  induction layer with
  | nil => rfl
  | cons entry tail ih =>
      by_cases headIs : entry.1.head? = some slot
      · have headEq : entry.1 = slot :: entry.1.tail := by
          revert headIs
          cases entry.1 with
          | nil => intro headIs; cases headIs
          | cons h t => intro headIs; simp only [List.head?_cons, Option.some.injEq] at headIs; simp [headIs]
        have entriesEq : SparseAddress.entriesAtSlot slot (entry :: tail) =
            entry :: SparseAddress.entriesAtSlot slot tail := by
          dsimp only [SparseAddress.entriesAtSlot]
          rw [List.filter_cons]
          simp [headIs]
        have dropEq : SparseAddress.dropAddressHeadLayer (entry :: SparseAddress.entriesAtSlot slot tail) =
            (entry.1.tail, entry.2) :: SparseAddress.dropAddressHeadLayer (SparseAddress.entriesAtSlot slot tail) := by
          change List.map SparseAddress.dropAddressHead (entry :: SparseAddress.entriesAtSlot slot tail) =
            (entry.1.tail, entry.2) :: List.map SparseAddress.dropAddressHead (SparseAddress.entriesAtSlot slot tail)
          rw [List.map_cons]
          rfl
        rw [entriesEq, dropEq]
        by_cases tailIs : entry.1.tail = rest
        · have headEq' : entry.1 = slot :: rest := by rw [headEq, tailIs]
          simp [SparsePhysicalFirstDifference.rowValueAt, headEq']
        · have notHead : entry.1 ≠ slot :: rest := by
            intro same
            exact tailIs (by rw [headEq] at same; simpa using congrArg List.tail same)
          simp [SparsePhysicalFirstDifference.rowValueAt, notHead, tailIs]
          exact ih
      · have entriesEq : SparseAddress.entriesAtSlot slot (entry :: tail) =
            SparseAddress.entriesAtSlot slot tail := by
          dsimp only [SparseAddress.entriesAtSlot]
          rw [List.filter_cons]
          simp [headIs]
        have notHead : entry.1 ≠ slot :: rest := by
          intro same
          exact headIs (by simp [same])
        rw [entriesEq]
        simp [SparsePhysicalFirstDifference.rowValueAt, notHead]
        exact ih

/-- The addressed table compiled from a realized tree reads, at every reachable node path, exactly
that node's observation.  This is the actual physical cut inventory: the sparse-table address is
precisely the `Position` slot path, so the root slot and the recursive child merge line up. -/
private theorem tableValue_eq_observe_of_subtreeAt?
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → Nat) :
    ∀ (path : List Nat) (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
      (node : LocalizedCumulativeDecoratedTree input carrierFuel),
      subtreeAt? tree path = some node →
        SparsePhysicalFirstDifference.tableValue
          (LocalizedCumulativeDecoratedTree.table observe tree) path = observe node := by
  intro path
  induction path with
  | nil =>
      intro tree node lookup
      have nodeEq : node = tree := by
        have someEq : some tree = some node := (subtreeAt?_nil tree).symm.trans lookup
        exact (Option.some.inj someEq).symm
      rw [nodeEq]
      rw [LocalizedCumulativeDecoratedTree.table_eq_root_merge]
      simp [SparsePhysicalFirstDifference.tableValue, SparsePhysicalFirstDifference.rowValueAt]
  | cons slot rest ih =>
      intro tree node lookup
      rw [subtreeAt?_cons_eq_some_iff] at lookup
      obtain ⟨child, childLookup, restLookup⟩ := lookup
      have ihChild := ih child node restLookup
      unfold SparsePhysicalFirstDifference.tableValue
      calc
        SparsePhysicalFirstDifference.rowValueAt
            ((LocalizedCumulativeDecoratedTree.table observe tree).getD (slot :: rest).length [])
            (slot :: rest)
          = SparsePhysicalFirstDifference.rowValueAt
            ((LocalizedCumulativeDecoratedTree.table observe tree).getD (rest.length + 1) [])
            (slot :: rest) := by
              simp only [List.length_cons]
        _ = SparsePhysicalFirstDifference.rowValueAt
            ((LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
              (tree.children.map (LocalizedCumulativeDecoratedTree.table observe))).getD rest.length [])
            (slot :: rest) := by
              rw [LocalizedCumulativeDecoratedTree.table_eq_root_merge]
              simp only [List.singleton_append, List.getD_cons_succ]
        _ = SparsePhysicalFirstDifference.rowValueAt
            ((LocalizedCumulativeDecoratedTree.table observe child).getD rest.length []) rest := by
              have mergeEq : LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
                    (tree.children.map (LocalizedCumulativeDecoratedTree.table observe)) =
                  SparseAddress.mergePairTable tree.children.zipIdx
                    (fun child => LocalizedCumulativeDecoratedTree.table observe child)
                    (LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
                      (tree.children.map (LocalizedCumulativeDecoratedTree.table observe))) := by
                unfold LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
                rw [LocalizedCumulativeDecoratedTree.mergePairTable_zipIdx_map_gen]
                simp
              have chosenBound :
                  (LocalizedCumulativeDecoratedTree.table observe child).length ≤
                    LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
                      (tree.children.map (LocalizedCumulativeDecoratedTree.table observe)) :=
                length_le_foldl_max
                  (tree.children.map (LocalizedCumulativeDecoratedTree.table observe))
                  (LocalizedCumulativeDecoratedTree.table observe child)
                  (List.mem_map.mpr ⟨child, List.mem_of_getElem? childLookup, rfl⟩)
              have reconEq : SparseAddress.dropAddressHeadLayer
                    (SparseAddress.entriesAtSlot slot
                      ((LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
                        (tree.children.map (LocalizedCumulativeDecoratedTree.table observe))).getD rest.length [])) =
                  (LocalizedCumulativeDecoratedTree.table observe child).getD rest.length [] := by
                rw [mergeEq]
                exact SparseAddress.mergePairTable_getD_entriesAtSlot_zipIdx
                  tree.children (fun child => LocalizedCumulativeDecoratedTree.table observe child)
                  (LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
                    (tree.children.map (LocalizedCumulativeDecoratedTree.table observe)))
                  rest.length slot child chosenBound childLookup
              rw [rowValueAt_cons slot rest
                ((LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
                  (tree.children.map (LocalizedCumulativeDecoratedTree.table observe))).getD rest.length [])]
              rw [reconEq]
        _ = observe node := by
              simpa [SparsePhysicalFirstDifference.tableValue] using ihChild

/-- At every present position, the observation column of a realized tree reads that position's
node observation: the actual physical cut inventory and addressing, not a runtime key read. -/
theorem tableValue_eq_observe_positionNode
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → Nat)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel} (p : Position tree) :
    SparsePhysicalFirstDifference.tableValue
      (LocalizedCumulativeDecoratedTree.table observe tree) p.val = observe (positionNode p) :=
  tableValue_eq_observe_of_subtreeAt? observe p.val tree (positionNode p) (positionNode_spec p)

/-- All-position observation alignment for Rule 1a: the atomic-number column of a realized tree,
read at any present position, is the physical atomic number of the atom at that position. -/
theorem tableValue_atomicNumber_eq_atomZ
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    SparsePhysicalFirstDifference.tableValue
      (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) tree) p.val =
      input.moleculeGraph.atomZ (positionAtom singleBonded acyclic p) := by
  rw [tableValue_eq_observe_positionNode (fun node => node.atomicNumber) p]
  exact positionAtomicNumber_eq_atomZ singleBonded acyclic realizes p

/-- All-position observation alignment for Rule 1b: the rule-1b distance column of a realized
tree, read at any present position, is the physical distance from the original outer root to the
atom at that position. -/
theorem tableValue_rule1bDistance_eq_outerRoot_dist
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    SparsePhysicalFirstDifference.tableValue
      (LocalizedCumulativeDecoratedTree.table (fun node => node.rule1bDistance) tree) p.val =
      input.moleculeGraph.underlyingSimpleGraph.dist tree.source.occurrence.1.root
        (positionAtom singleBonded acyclic p) := by
  rw [tableValue_eq_observe_positionNode (fun node => node.rule1bDistance) p]
  exact positionNode_rule1bDistance_eq_outerRoot_dist singleBonded acyclic realizes p

/-- All-position observation alignment for Rule 2: the isotope-mass column of a realized tree,
read at any present position, is the physical atom mass of the atom at that position. -/
theorem tableValue_isotopeMass_eq_atomMass
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    SparsePhysicalFirstDifference.tableValue
      (LocalizedCumulativeDecoratedTree.table (fun node => node.isotopeMass) tree) p.val =
      input.moleculeGraph.atomMass (positionAtom singleBonded acyclic p) := by
  rw [tableValue_eq_observe_positionNode (fun node => node.isotopeMass) p]
  exact positionIsotopeMass_eq_atomMass singleBonded acyclic realizes p

/-- Key-level all-position alignment for Rule 1a: the actual built key's Rule-1a sparse layer,
read at any present position, is the physical atomic number of that atom. -/
theorem key_tableValue_rule1a_eq_atomZ
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {stage : LocalizedCumulativeRule45Stage}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (matched : LocalizedCumulativeTreeTableMatch stage tree key) (p : Position tree) :
    SparsePhysicalFirstDifference.tableValue key.constitutional.rule1a p.val =
      input.moleculeGraph.atomZ (positionAtom singleBonded acyclic p) := by
  have keyEq : key.constitutional.rule1a =
      LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) tree := by
    simpa using matched.1.symm
  rw [keyEq]
  exact tableValue_atomicNumber_eq_atomZ singleBonded acyclic realizes p

/-- Key-level all-position alignment for Rule 1b: the actual built key's Rule-1b sparse layer,
read at any present position, is the physical distance from the original outer root. -/
theorem key_tableValue_rule1b_eq_outerRoot_dist
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {stage : LocalizedCumulativeRule45Stage}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (matched : LocalizedCumulativeTreeTableMatch stage tree key) (p : Position tree) :
    SparsePhysicalFirstDifference.tableValue key.constitutional.rule1b p.val =
      input.moleculeGraph.underlyingSimpleGraph.dist tree.source.occurrence.1.root
        (positionAtom singleBonded acyclic p) := by
  have keyEq : key.constitutional.rule1b =
      LocalizedCumulativeDecoratedTree.table (fun node => node.rule1bDistance) tree := by
    simpa using matched.2.1.symm
  rw [keyEq]
  exact tableValue_rule1bDistance_eq_outerRoot_dist singleBonded acyclic realizes p

/-- Key-level all-position alignment for Rule 2: the actual built key's Rule-2 sparse layer,
read at any present position, is the physical atom mass of that atom. -/
theorem key_tableValue_rule2_eq_atomMass
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {stage : LocalizedCumulativeRule45Stage}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (matched : LocalizedCumulativeTreeTableMatch stage tree key) (p : Position tree) :
    SparsePhysicalFirstDifference.tableValue key.constitutional.rule2 p.val =
      input.moleculeGraph.atomMass (positionAtom singleBonded acyclic p) := by
  have keyEq : key.constitutional.rule2 =
      LocalizedCumulativeDecoratedTree.table (fun node => node.isotopeMass) tree := by
    simpa using matched.2.2.1.symm
  rw [keyEq]
  exact tableValue_isotopeMass_eq_atomMass singleBonded acyclic realizes p

/-! ## Physical Rule-1a schedule: totalized observation and first-difference direction -/

/-- **Physical Rule-1a observation schedule**, totalized at absent addresses by zero.

This is the independent physical criterion's Rule-1a observation at every raw address: at a
present position it is the physical atomic number of the atom living there
(`graph.atomZ` of the position atom), and at an absent position it is zero, matching the
sparse-table convention that absent addresses read zero.  It never reads a runtime key. -/
def physicalAtomicNumberAt (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (position : List Nat) : Nat :=
  ((subtreeAt? tree position).map fun node =>
    input.moleculeGraph.atomZ (nodeAtom singleBonded acyclic node)).getD 0

/-- When a slot is absent from a value list, no `zipIdx` pair selects that slot. -/
private theorem zipIdx_filter_eq_nil_of_getElem?_none {β : Type*}
    (values : List β) (slot : Nat) (absent : values[slot]? = none) :
    (values.zipIdx.filter fun pair => pair.2 == slot) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro pair present selected
  cases pair with
  | mk x i =>
      have indexEq : i = slot := by simpa using selected
      have lookup := (List.mk_mem_zipIdx_iff_getElem? (i := i) (x := x) (l := values)).mp present
      rw [indexEq] at lookup
      cases absent.symm.trans lookup

/-- **Absent-direction physical cut inventory.**  An address that is not a node path of the tree
reads zero from the addressed table, exactly matching the zero totalization of the physical
schedule at absent positions. -/
theorem tableValue_eq_zero_of_subtreeAt?_none
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → Nat) :
    ∀ (position : List Nat) (tree : LocalizedCumulativeDecoratedTree input carrierFuel),
      subtreeAt? tree position = none →
        SparsePhysicalFirstDifference.tableValue
          (LocalizedCumulativeDecoratedTree.table observe tree) position = 0 := by
  intro position
  induction position with
  | nil =>
      intro tree absent
      rw [subtreeAt?_nil] at absent
      cases absent
  | cons slot rest ih =>
      intro tree absent
      rw [subtreeAt?_cons] at absent
      unfold SparsePhysicalFirstDifference.tableValue
      calc
        SparsePhysicalFirstDifference.rowValueAt
            ((LocalizedCumulativeDecoratedTree.table observe tree).getD (slot :: rest).length [])
            (slot :: rest)
          = SparsePhysicalFirstDifference.rowValueAt
            ((LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
              (tree.children.map (LocalizedCumulativeDecoratedTree.table observe))).getD rest.length [])
            (slot :: rest) := by
              rw [LocalizedCumulativeDecoratedTree.table_eq_root_merge]
              simp only [List.length_cons, List.singleton_append, List.getD_cons_succ]
        _ = 0 := by
            cases hChild : tree.children[slot]? with
            | none =>
                have mapAbsent :
                    (tree.children.map (LocalizedCumulativeDecoratedTree.table observe))[slot]? = none := by
                  rw [List.getElem?_map, hChild]
                  rfl
                have filterEmpty :
                    ((tree.children.map (LocalizedCumulativeDecoratedTree.table observe)).zipIdx.filter
                      fun pair => pair.2 == slot) = [] :=
                  zipIdx_filter_eq_nil_of_getElem?_none
                    (tree.children.map (LocalizedCumulativeDecoratedTree.table observe)) slot mapAbsent
                have layerEmpty : SparseAddress.entriesAtSlot slot
                      ((LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
                        (tree.children.map (LocalizedCumulativeDecoratedTree.table observe))).getD
                        rest.length []) = [] := by
                  unfold LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
                  rw [SparseAddress.mergePairTable_getD]
                  by_cases inRange : rest.length <
                      LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
                        (tree.children.map (LocalizedCumulativeDecoratedTree.table observe))
                  · rw [if_pos inRange]
                    dsimp only [SparseAddress.mergePairs]
                    rw [SparseAddress.entriesAtSlot_flatMap_prefixLayer
                      ((tree.children.map (LocalizedCumulativeDecoratedTree.table observe)).zipIdx)
                      (fun value => (id value).getD rest.length [])
                      slot]
                    rw [filterEmpty]
                    rfl
                  · rw [if_neg inRange]
                    rfl
                rw [rowValueAt_cons slot rest
                  ((LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
                    (tree.children.map (LocalizedCumulativeDecoratedTree.table observe))).getD
                    rest.length [])]
                rw [layerEmpty]
                rfl
            | some child =>
                have childAbsent : subtreeAt? child rest = none := by
                  rw [hChild] at absent
                  simpa using absent
                have mergeEq : LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
                      (tree.children.map (LocalizedCumulativeDecoratedTree.table observe)) =
                    SparseAddress.mergePairTable tree.children.zipIdx
                      (fun child => LocalizedCumulativeDecoratedTree.table observe child)
                      (LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
                        (tree.children.map (LocalizedCumulativeDecoratedTree.table observe))) := by
                  unfold LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
                  rw [LocalizedCumulativeDecoratedTree.mergePairTable_zipIdx_map_gen]
                  simp
                have chosenBound :
                    (LocalizedCumulativeDecoratedTree.table observe child).length ≤
                      LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
                        (tree.children.map (LocalizedCumulativeDecoratedTree.table observe)) :=
                  length_le_foldl_max
                    (tree.children.map (LocalizedCumulativeDecoratedTree.table observe))
                    (LocalizedCumulativeDecoratedTree.table observe child)
                    (List.mem_map.mpr ⟨child, List.mem_of_getElem? hChild, rfl⟩)
                have reconEq : SparseAddress.dropAddressHeadLayer
                      (SparseAddress.entriesAtSlot slot
                        ((LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
                          (tree.children.map (LocalizedCumulativeDecoratedTree.table observe))).getD
                          rest.length [])) =
                    (LocalizedCumulativeDecoratedTree.table observe child).getD rest.length [] := by
                  rw [mergeEq]
                  exact SparseAddress.mergePairTable_getD_entriesAtSlot_zipIdx
                    tree.children (fun child => LocalizedCumulativeDecoratedTree.table observe child)
                    (LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
                      (tree.children.map (LocalizedCumulativeDecoratedTree.table observe)))
                    rest.length slot child chosenBound hChild
                rw [rowValueAt_cons slot rest
                  ((LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
                    (tree.children.map (LocalizedCumulativeDecoratedTree.table observe))).getD
                    rest.length [])]
                rw [reconEq]
                simpa [SparsePhysicalFirstDifference.tableValue] using (ih child childAbsent)

/-- **All-position physical schedule alignment for Rule 1a.**  The compiled atomic-number table of
a realized tree, read at any address, is the totalized physical Rule-1a observation: the physical
atomic number at present positions and zero at absent positions. -/
theorem tableValue_atomicNumber_eq_physicalAtomicNumberAt
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input r tree) (position : List Nat) :
    SparsePhysicalFirstDifference.tableValue
      (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) tree) position =
      physicalAtomicNumberAt singleBonded acyclic tree position := by
  cases hLookup : subtreeAt? tree position with
  | some node =>
      rw [physicalAtomicNumberAt]
      rw [hLookup]
      simp
      rw [tableValue_eq_observe_of_subtreeAt? (fun node => node.atomicNumber) position tree node hLookup]
      exact atomicNumber_eq_atomZ singleBonded acyclic (realizes_of_subtree realizes hLookup)
  | none =>
      rw [physicalAtomicNumberAt]
      rw [hLookup]
      simp
      exact tableValue_eq_zero_of_subtreeAt?_none (fun node => node.atomicNumber) position tree hLookup

/-- **Physical Rule-1a direction.**  For two realized trees of the same certified input, the
executed Rule-1a comparison of the compiled atomic-number tables realizes the independent physical
Rule-1a first difference: the decisive address carries the physical atomic numbers of the atoms
there, absent addresses read zero, and earlier addresses agree. -/
theorem table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {readLeft readRight : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizesLeft : LocalizedCumulativeTreeRealizes input readLeft leftTree)
    (realizesRight : LocalizedCumulativeTreeRealizes input readRight rightTree)
    (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree)
        (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree) =
          outcome ↔
      DeclarativeCIP.FirstDifferenceOutcome
        (fun position result =>
          DeclarativeCIP.DescendingNatOutcome
            (physicalAtomicNumberAt singleBonded acyclic leftTree position)
            (physicalAtomicNumberAt singleBonded acyclic rightTree position)
            result)
        outcome := by
  rw [LocalizedActualTableAddressOrder.table_atomicNumber_compareSparseLayers_eq_firstDifference
    singleBonded acyclic realizesLeft realizesRight outcome]
  apply DeclarativeCIP.FirstDifferenceOutcome.congr
  intro position result
  constructor
  · intro h
    rw [tableValue_atomicNumber_eq_physicalAtomicNumberAt singleBonded acyclic realizesLeft position,
        tableValue_atomicNumber_eq_physicalAtomicNumberAt singleBonded acyclic realizesRight position] at h
    exact h
  · intro h
    rw [tableValue_atomicNumber_eq_physicalAtomicNumberAt singleBonded acyclic realizesLeft position,
        tableValue_atomicNumber_eq_physicalAtomicNumberAt singleBonded acyclic realizesRight position]
    exact h

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compareNat_eq_iff_descendingNatOutcome
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compareRule1b_eq_iff_rule1bDistanceOutcome
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compare_rule1a_eq_gt_of_descendingNat_gt
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compare_rule1a_eq_lt_of_descendingNat_lt
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compare_rule1b_eq_gt_of_rule1bDistance_gt
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compare_rule1b_eq_lt_of_rule1bDistance_lt
assert_kernel_only TetraStereo.OneCenter.physicalConstitutionalNodeOutcome
assert_kernel_only TetraStereo.OneCenter.physicalConstitutionalHierarchyOutcome
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys_eq_of_constitutional_decisive
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.officialRuleMajorKey_Descending_of_localizedRerootCumulativeRule45KeysDescending
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sortLocalizedRerootCumulativeRule45Keys_constitutional_descending
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_constitutional_root_heads
assert_kernel_only TetraStereo.OneCenter.localizedRootTree_atomicNumber_eq_sourceLabel
assert_kernel_only TetraStereo.OneCenter.localizedRootTree_isotopeMass_eq_sourceLabel
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCumulativeRule45Key?_root_observations_physical
assert_kernel_only TetraStereo.OneCenter.tableValue_eq_observe_positionNode
assert_kernel_only TetraStereo.OneCenter.tableValue_atomicNumber_eq_atomZ
assert_kernel_only TetraStereo.OneCenter.tableValue_rule1bDistance_eq_outerRoot_dist
assert_kernel_only TetraStereo.OneCenter.tableValue_isotopeMass_eq_atomMass
assert_kernel_only TetraStereo.OneCenter.key_tableValue_rule1a_eq_atomZ
assert_kernel_only TetraStereo.OneCenter.key_tableValue_rule1b_eq_outerRoot_dist
assert_kernel_only TetraStereo.OneCenter.key_tableValue_rule2_eq_atomMass
assert_kernel_only TetraStereo.OneCenter.physicalAtomicNumberAt
assert_kernel_only TetraStereo.OneCenter.tableValue_eq_zero_of_subtreeAt?_none
assert_kernel_only TetraStereo.OneCenter.tableValue_atomicNumber_eq_physicalAtomicNumberAt
assert_kernel_only TetraStereo.OneCenter.table_atomicNumber_compareSparseLayers_eq_physical_firstDifference

end TetraStereo.OneCenter
