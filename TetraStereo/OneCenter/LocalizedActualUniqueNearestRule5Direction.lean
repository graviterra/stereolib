import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder
import TetraStereo.OneCenter.Rule4c5SparseSourceDecisionFidelity
import TetraStereo.OneCenter.LocalizedRule5SwapAndSignal
import TetraStereo.OneCenter.LocalizedSparseSupportAlignment
import TetraStereo.OneCenter.LocalizedCumulativeTreeTableReconstruction
import TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction
import TetraStereo.OneCenter.LocalizedRule4bSparseLabelDecoding
import TetraStereo.OneCenter.LocalizedActualNearestCompoundReadings
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput





















































































namespace LocalizedActualUniqueNearestRule5Direction

open Rule4c5SourceDecision
open SparseSupportAlignment
open SparsePhysicalFirstDifference

/-! ## A. Stage pairing and the absent-observation tie -/

/-- The two common-reference stages selected for one ligand have the same earlier-priority prefix;
they differ only in the Rule-5 probe. -/
theorem stagePriorityPrefix_stageFor_eq (own : Option RS) (probeR probeS : RS)
    (label : Option LocalizedAuxiliaryLabel) :
    Rule4c5SourceDecision.stagePriorityPrefix (localizedRule5StageFor own probeR) label =
      Rule4c5SourceDecision.stagePriorityPrefix (localizedRule5StageFor own probeS) label := by
  cases own <;> rfl

/-- The stage selected for one ligand and one common reference really carries that Rule-5 probe. -/
theorem stageRule5Probe_stageFor (own : Option RS) (probe : RS) :
    Rule4c5SourceDecision.stageRule5Probe? (localizedRule5StageFor own probe) = some probe := by
  cases own <;> rfl

/-- The priority vectors of an absent observation coincide across the two common-reference
stages: the earlier Rules-4a/4b/4c prefix is shared and the Rule-5 bit is zero in both.  This is
the value-level form of "every observation before the nearest depth is `none`, hence ties". -/
theorem cumulativePriority_none_eq_stageFor (own : Option RS) :
    localizedCumulativeRule45Priority (localizedRule5StageFor own .R) none =
      localizedCumulativeRule45Priority (localizedRule5StageFor own .S) none := by
  cases own <;> rfl

/-! ## B. Signed single-entry direction -/

/-- **Signed one-observation direction.**  At a single shared address, the same uppercase chiral
descriptor read under the common-`R` stage is strictly senior to its common-`S` reading: `R` gives
`gt`, `S` gives `lt`.  The earlier-priority tie is derived from the stage pairing, not assumed. -/
theorem comparePriority_stageFor_R_S_chiral_sign (own : Option RS) (descriptor : RS) :
    compareLocalizedCumulativeRule45Priority
        (localizedCumulativeRule45Priority (localizedRule5StageFor own .R)
          (some (.chiral descriptor)))
        (localizedCumulativeRule45Priority (localizedRule5StageFor own .S)
          (some (.chiral descriptor))) =
      if descriptor = RS.R then Ordering.gt else Ordering.lt := by
  have prefixEq := stagePriorityPrefix_stageFor_eq own .R .S (some (.chiral descriptor))
  rw [Rule4c5SourceDecision.cumulativePriority_eq_prefix_append_rule5
        (localizedRule5StageFor own .R) .R (stageRule5Probe_stageFor own .R)
        (some (.chiral descriptor)),
    Rule4c5SourceDecision.cumulativePriority_eq_prefix_append_rule5
        (localizedRule5StageFor own .S) .S (stageRule5Probe_stageFor own .S)
        (some (.chiral descriptor)),
    ← prefixEq]
  unfold compareLocalizedCumulativeRule45Priority
  rw [Rule4c5SourceDecision.compareLex_compareNat_append_singleton]
  cases descriptor <;> rfl

/-- The sparse addressed form of the signed one-observation direction: one shared address, one
observed uppercase chiral label, common-`R` stage versus common-`S` stage. -/
theorem compareSparseLayers_stageFor_R_S_chiral_sign
    (own : Option RS) (address : List Nat) (descriptor : RS) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (Rule4c5SourceDecision.actualStageObservation (localizedRule5StageFor own .R)
          address (some (.chiral descriptor)))
        (Rule4c5SourceDecision.actualStageObservation (localizedRule5StageFor own .S)
          address (some (.chiral descriptor))) =
      if descriptor = RS.R then Ordering.gt else Ordering.lt := by
  unfold Rule4c5SourceDecision.actualStageObservation
  rw [Rule4c5SourceDecision.compareSparseLayers_liftSparseObservation,
    Rule4c5SourceDecision.sourcePathDecision_self]
  exact comparePriority_stageFor_R_S_chiral_sign own descriptor

/-! ## C. Generic first-difference sign lemmas -/

/-- **Strict decision after a common reflexive prefix.**  If `cmp` is reflexive on the (common)
prefix entries and decides `headL` against `headR` strictly as `outcome`, then the whole
`List.compareLex` comparison equals `outcome`, independently of the tails. -/
theorem compareLex_eq_of_prefix_cons {α : Type*} (cmp : α → α → Ordering)
    (stem : List α) (headL headR : α) (tailL tailR : List α) (outcome : Ordering)
    (reflexive : ∀ a, cmp a a = Ordering.eq)
    (decision : cmp headL headR = outcome) (strict : outcome ≠ Ordering.eq) :
    List.compareLex cmp (stem ++ headL :: tailL) (stem ++ headR :: tailR) = outcome := by
  induction stem with
  | nil =>
      change List.compareLex cmp (headL :: tailL) (headR :: tailR) = outcome
      rw [List.compareLex_cons_cons, decision]
      cases outcome with
      | lt => rfl
      | gt => rfl
      | eq => exact (strict rfl).elim
  | cons head tail ih =>
      rw [List.cons_append, List.cons_append, List.compareLex_cons_cons, reflexive head]
      change List.compareLex cmp (tail ++ headL :: tailL) (tail ++ headR :: tailR) = outcome
      exact ih

/-- The cumulative node-vector comparator is reflexive. -/
theorem comparePriority_refl (vector : List Nat) :
    compareLocalizedCumulativeRule45Priority vector vector = Ordering.eq :=
  (compareLocalizedCumulativeRule45Priority_eq_iff vector vector).mpr rfl

/-! ## D. Signed first difference under a common address alignment -/












theorem compareSparseLayers_stageFor_R_S_signed_of_alignment
    (own : Option RS) (descriptor : RS)
    {left right : List (List (OfficialSparseEntry (List Nat)))}
    (alignment : SparseAlignment left right)
    (stem : List (List Nat)) (tailL tailR : List (List Nat))
    (leftValues : left.flatten.map Prod.snd =
      stem ++ localizedCumulativeRule45Priority (localizedRule5StageFor own .R)
        (some (.chiral descriptor)) :: tailL)
    (rightValues : right.flatten.map Prod.snd =
      stem ++ localizedCumulativeRule45Priority (localizedRule5StageFor own .S)
        (some (.chiral descriptor)) :: tailR) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        left right =
      if descriptor = RS.R then Ordering.gt else Ordering.lt := by
  rw [compareSparseLayers_eq_compareLex_of_alignment
    compareLocalizedCumulativeRule45Priority alignment]
  rw [leftValues, rightValues]
  exact compareLex_eq_of_prefix_cons compareLocalizedCumulativeRule45Priority
    stem
    (localizedCumulativeRule45Priority (localizedRule5StageFor own .R) (some (.chiral descriptor)))
    (localizedCumulativeRule45Priority (localizedRule5StageFor own .S) (some (.chiral descriptor)))
    tailL tailR
    (if descriptor = RS.R then Ordering.gt else Ordering.lt)
    comparePriority_refl
    (comparePriority_stageFor_R_S_chiral_sign own descriptor)
    (by cases descriptor <;> decide)

/-! ## E. Reading-level signed direction under mirror crossing -/

/-- The common-`R` reading comparison of two singleton reading lists equals a supplied signed
common-`R`-versus-common-`S` descriptor decision of the left branch, via the mirror-crossed
descriptor equality.  This is the *signed* refinement of the strictness-only statement in the
conditional algebra. -/
theorem compareRule5Readings_R_sign_of_singleton_mirror
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (leftReading rightReading : input.LocalizedRerootRule5Reading)
    (leftEq : left.rule5Readings = [leftReading])
    (rightEq : right.rule5Readings = [rightReading])
    (mirror : LocalizedRule5SwapAndSignal.MirrorReading input leftReading rightReading)
    (outcome : Ordering)
    (signed : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        leftReading.commonR.descriptor leftReading.commonS.descriptor = outcome) :
    input.compareLocalizedRerootCompoundRule5Readings .R
        left.rule5Readings right.rule5Readings = outcome := by
  rw [leftEq, rightEq,
    Rule4c5SourceDecision.compareLocalizedRerootCompoundRule5Readings_singleton]
  rw [Rule4c5SourceDecision.localizedRerootRule5Descriptor_R_eq_commonR,
    Rule4c5SourceDecision.localizedRerootRule5Descriptor_R_eq_commonR]
  rw [← mirror.2]
  exact signed

/-! ## F. Through-Rule-5 signed ordering with the pseudo flag -/

/-- **Through-Rule-5 signed direction from singleton mirror readings and a derived prior tie.**

Under a complete prior Rules-4b/4c tie, mirror-crossed singleton readings and a signed common-`R`
reading decision, the actual through-Rule-5 comparison reports exactly that ordering and
`pseudo = true`.  This is the signed form of the `±2` enantiomorphic signal of the physical mirror
pair, stated at the actual comparator. -/
theorem throughRule5_signed_pseudo_of_singleton_mirror
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (leftReading rightReading : input.LocalizedRerootRule5Reading)
    (leftEq : left.rule5Readings = [leftReading])
    (rightEq : right.rule5Readings = [rightReading])
    (mirror : LocalizedRule5SwapAndSignal.MirrorReading input leftReading rightReading)
    (priorTie : input.compareLocalizedRerootCompoundRule4bcKeys
      left.prior right.prior = Ordering.eq)
    (outcome : Ordering)
    (signedR : input.compareLocalizedRerootCompoundRule5Readings .R
      left.rule5Readings right.rule5Readings = outcome)
    (strict : outcome ≠ Ordering.eq) :
    (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering = outcome ∧
      (input.compareLocalizedRerootCompoundThroughRule5 left right).pseudo = true := by
  have ordering : (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering =
      outcome := by
    rw [input.compareLocalizedRerootCompoundThroughRule5_ordering]
    unfold compareLocalizedRerootCompoundRule45Keys
    simp only [compareLex, Ordering.byKey, priorTie, signedR]
    rfl
  have pseudo : (input.compareLocalizedRerootCompoundThroughRule5 left right).pseudo = true := by
    have mirrorReadings : LocalizedRule5SwapAndSignal.MirrorReadings input
        left.rule5Readings right.rule5Readings := by
      rw [leftEq, rightEq]
      exact List.Forall₂.cons mirror List.Forall₂.nil
    rw [LocalizedRule5SwapAndSignal.compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff_of_mirror_of_prior_tie
      input left right mirrorReadings priorTie]
    rw [signedR]
    exact strict
  exact ⟨ordering, pseudo⟩

/-! ## G. The address skeleton of a tree table is independent of the observed column -/

/-- `prefixLayer` prefixes the sibling slot to the address and keeps the observation. -/
theorem prefixLayer_map_fst {α : Type*} (slot : Nat)
    (row : List (OfficialSparseEntry α)) :
    (OfficialRuleMajorKey.prefixLayer slot row).map Prod.fst =
      (row.map Prod.fst).map (fun address => slot :: address) := by
  simp only [OfficialRuleMajorKey.prefixLayer, List.map_map]
  rfl

/-- `zipIdx` commutes with mapping the values. -/
theorem zipIdx_map_eq {γ δ : Type*} (values : List γ) (embed : γ → δ) :
    (values.map embed).zipIdx = values.zipIdx.map (fun pair => (embed pair.1, pair.2)) := by
  rw [List.zipIdx_map]
  exact List.map_congr_left (fun pair _ => by cases pair with | mk value slot => rfl)

/-- The slot-indexed merge only prepends slots to addresses: its flat map is the flat map of the
slot-prefixed blocks at the embedded value. -/
theorem mergePairs_map_zipIdx {γ δ α : Type*} (values : List γ) (embed : γ → δ)
    (block : δ → List (OfficialSparseEntry α)) :
    SparseAddress.mergePairs (values.map embed).zipIdx block =
      values.zipIdx.flatMap
        (fun pair => OfficialRuleMajorKey.prefixLayer pair.2 (block (embed pair.1))) := by
  unfold SparseAddress.mergePairs
  rw [zipIdx_map_eq, List.flatMap_map]

/-- The first component of a `zipIdx` pair is one of the zipped values. -/
theorem mem_fst_of_mem_zipIdx {γ : Type*} :
    ∀ (values : List γ) (start : Nat) (pair : γ × Nat),
      pair ∈ values.zipIdx start → pair.1 ∈ values
  | [], _, _, present => by simp at present
  | value :: rest, start, pair, present => by
      rw [List.zipIdx_cons] at present
      rcases List.mem_cons.mp present with same | later
      · rw [same]
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem value
          (mem_fst_of_mem_zipIdx rest (start + 1) pair later)

/-- One merged sphere has the same address list for any two observed columns whose child rows have
the same addresses.  Values are never inspected. -/
theorem mergePairs_children_map_map_fst_eq {γ α β : Type*} (children : List γ)
    (leftTable : γ → List (List (OfficialSparseEntry α)))
    (rightTable : γ → List (List (OfficialSparseEntry β)))
    (rows : ∀ child ∈ children, ∀ depth,
      ((leftTable child).getD depth []).map Prod.fst =
        ((rightTable child).getD depth []).map Prod.fst)
    (depth : Nat) :
    (SparseAddress.mergePairs (children.map leftTable).zipIdx
        (fun table => table.getD depth [])).map Prod.fst =
      (SparseAddress.mergePairs (children.map rightTable).zipIdx
        (fun table => table.getD depth [])).map Prod.fst := by
  rw [mergePairs_map_zipIdx children leftTable (fun table => table.getD depth []),
    mergePairs_map_zipIdx children rightTable (fun table => table.getD depth [])]
  simp only [List.map_flatMap]
  apply List.flatMap_congr
  intro pair present
  have childMem : pair.1 ∈ children := mem_fst_of_mem_zipIdx children 0 pair present
  simp only [prefixLayer_map_fst, rows pair.1 childMem depth]

/-- The merged layer count of a list of mapped child tables only depends on the children's
heights, through a general fold seed. -/
theorem localizedTreeChildLayerCount_foldl_eq {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} {α : Type*}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α) :
    ∀ (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) (seed : Nat),
      (children.map (LocalizedCumulativeDecoratedTree.table observe)).foldl
          (fun longest table => max longest table.length) seed =
        children.foldl (fun longest child =>
          max longest (LocalizedCumulativeDecoratedTree.height child)) seed
  | [], _ => rfl
  | child :: rest, seed => by
      simp only [List.map_cons, List.foldl_cons]
      rw [LocalizedCumulativeDecoratedTree.table_length_eq_height]
      exact localizedTreeChildLayerCount_foldl_eq observe rest
        (max seed (LocalizedCumulativeDecoratedTree.height child))

/-- Child layer counts, and hence the number of merged spheres, agree between any two observed
columns of the same tree. -/
theorem localizedTreeChildLayerCount_eq {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} {α β : Type*}
    (leftObserve : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (rightObserve : LocalizedCumulativeDecoratedTree input carrierFuel → β)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
        (children.map (LocalizedCumulativeDecoratedTree.table leftObserve)) =
      LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
        (children.map (LocalizedCumulativeDecoratedTree.table rightObserve)) := by
  unfold LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
  rw [localizedTreeChildLayerCount_foldl_eq leftObserve children 0,
    localizedTreeChildLayerCount_foldl_eq rightObserve children 0]

/-- **The addresses in every sphere of a tree table are independent of the observed column.**
Sphere zero is the root address; sphere `depth + 1` is the slot-prefixed merge whose addresses
depend only on the child list and the child rows at `depth`. -/
theorem table_addresses_getD {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {α β : Type*}
    (leftObserve : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (rightObserve : LocalizedCumulativeDecoratedTree input carrierFuel → β)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (depth : Nat) :
    ((LocalizedCumulativeDecoratedTree.table leftObserve tree).getD depth []).map Prod.fst =
      ((LocalizedCumulativeDecoratedTree.table rightObserve tree).getD depth []).map
        Prod.fst := by
  have main : ∀ n : Nat, ∀ candidate : LocalizedCumulativeDecoratedTree input carrierFuel,
      LocalizedCumulativeDecoratedTree.height candidate ≤ n → ∀ depth,
        ((LocalizedCumulativeDecoratedTree.table leftObserve candidate).getD depth []).map
            Prod.fst =
          ((LocalizedCumulativeDecoratedTree.table rightObserve candidate).getD depth []).map
            Prod.fst := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k ih candidate bound depth
    cases depth with
    | zero =>
        rw [LocalizedCumulativeDecoratedTree.table_getD_zero leftObserve candidate,
          LocalizedCumulativeDecoratedTree.table_getD_zero rightObserve candidate]
        rfl
    | succ depth =>
        rw [LocalizedCumulativeDecoratedTree.table_eq_root_merge leftObserve candidate,
          LocalizedCumulativeDecoratedTree.table_eq_root_merge rightObserve candidate,
          LocalizedCumulativeDecoratedTree.getD_root_cons,
          LocalizedCumulativeDecoratedTree.getD_root_cons]
        unfold LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
        simp only [SparseAddress.mergePairTable_getD]
        have countEq :=
          localizedTreeChildLayerCount_eq leftObserve rightObserve candidate.children
        simp only [countEq]
        by_cases inside : depth <
            LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
              (candidate.children.map
                (LocalizedCumulativeDecoratedTree.table rightObserve))
        · simp only [if_pos inside]
          exact mergePairs_children_map_map_fst_eq candidate.children
            (LocalizedCumulativeDecoratedTree.table leftObserve)
            (LocalizedCumulativeDecoratedTree.table rightObserve)
            (fun child childMem childDepth =>
              ih (LocalizedCumulativeDecoratedTree.height child)
                (by
                  have smaller :=
                    LocalizedCumulativeDecoratedTree.height_lt_height_of_mem candidate childMem
                  omega)
                child (le_refl _) childDepth)
            depth
        · simp only [if_neg inside]
          rfl
  exact main (LocalizedCumulativeDecoratedTree.height tree) tree (le_refl _) depth

/-- A non-empty sphere at index `depth` forces that index below the table length. -/
theorem getD_ne_nil_imp_lt_length {γ : Type*} :
    ∀ (list : List (List γ)) (depth : Nat), list.getD depth [] ≠ [] → depth < list.length
  | [], _, nonempty => by simp at nonempty
  | _ :: _, 0, _ => by simp
  | _ :: tail, depth + 1, nonempty => by
      have step := getD_ne_nil_imp_lt_length tail depth (by simpa using nonempty)
      simpa using step

/-- Lengths of flat maps are equal when all blocks have equal lengths. -/
theorem flatMap_length_eq_of_length_eq {γ α β : Type*} (values : List γ)
    (leftBlock : γ → List α) (rightBlock : γ → List β)
    (same : ∀ value ∈ values, (leftBlock value).length = (rightBlock value).length) :
    (values.flatMap leftBlock).length = (values.flatMap rightBlock).length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      rw [List.flatMap_cons, List.flatMap_cons, List.length_append, List.length_append,
        same value (by simp), ih (fun other present => same other (by simp [present]))]

/-- The number of observations at one tree depth is independent of the observed column. -/
theorem observationsAtDepth_length_eq {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} {α β : Type*}
    (leftObserve : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (rightObserve : LocalizedCumulativeDecoratedTree input carrierFuel → β) :
    ∀ (depth : Nat) (tree : LocalizedCumulativeDecoratedTree input carrierFuel),
      (LocalizedCumulativeDecoratedTree.observationsAtDepth leftObserve depth tree).length =
        (LocalizedCumulativeDecoratedTree.observationsAtDepth rightObserve depth tree).length := by
  intro depth
  induction depth with
  | zero => intro tree; rfl
  | succ depth ih =>
      intro tree
      exact flatMap_length_eq_of_length_eq tree.children
        (fun child => LocalizedCumulativeDecoratedTree.observationsAtDepth leftObserve depth child)
        (fun child => LocalizedCumulativeDecoratedTree.observationsAtDepth rightObserve depth child)
        (fun child _ => ih child)

/-- **The two observed columns of one tree are `SparseAlignment`-related.**  The layer count, every
sphere cardinality and the flattened address sequence are read off the tree shape alone, so they
coincide for any two observation types. -/
theorem table_sparseAlignment {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {α : Type*}
    (leftObserve : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (rightObserve : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    SparseAlignment (LocalizedCumulativeDecoratedTree.table leftObserve tree)
      (LocalizedCumulativeDecoratedTree.table rightObserve tree) where
  lengthEq := by
    rw [LocalizedCumulativeDecoratedTree.table_length_eq_height,
      LocalizedCumulativeDecoratedTree.table_length_eq_height]
  cardinality := by
    intro depth
    rw [← List.length_map Prod.snd, ← List.length_map Prod.snd,
      LocalizedCumulativeDecoratedTree.table_getD_map_snd,
      LocalizedCumulativeDecoratedTree.table_getD_map_snd]
    exact observationsAtDepth_length_eq leftObserve rightObserve depth tree
  sameAddresses := flattenAddresses_eq_of_rows
    (by
      rw [LocalizedCumulativeDecoratedTree.table_length_eq_height,
        LocalizedCumulativeDecoratedTree.table_length_eq_height])
    (table_addresses_getD leftObserve rightObserve tree)

/-! ## H. Non-chiral observations and the first chiral sphere -/

/-- Non-chiral labels carry the same cumulative priority vector under the two common-reference
stages of one ligand. -/
theorem priority_stageFor_eq_of_not_chiral (own : Option RS)
    (label : Option LocalizedAuxiliaryLabel)
    (notChiral : ∀ descriptor, label ≠ some (.chiral descriptor)) :
    localizedCumulativeRule45Priority (localizedRule5StageFor own .R) label =
      localizedCumulativeRule45Priority (localizedRule5StageFor own .S) label := by
  cases own with
  | none =>
      cases label with
      | none => rfl
      | some label =>
          cases label with
          | pseudoasymmetric descriptor => cases descriptor <;> rfl
          | chiral descriptor => exact absurd rfl (notChiral descriptor)
  | some reference =>
      cases label with
      | none => rfl
      | some label =>
          cases label with
          | pseudoasymmetric descriptor => cases descriptor <;> rfl
          | chiral descriptor => exact absurd rfl (notChiral descriptor)

/-- A list of observations with no uppercase chiral entry has the same cumulative priority vector
list under the two common-reference stages. -/
theorem map_priority_eq_of_chiralDescriptors_nil (own : Option RS) :
    ∀ (labels : List (Option LocalizedAuxiliaryLabel)),
      LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations labels = [] →
      labels.map (localizedCumulativeRule45Priority (localizedRule5StageFor own .R)) =
        labels.map (localizedCumulativeRule45Priority (localizedRule5StageFor own .S))
  | [], _ => rfl
  | none :: rest, empty => by
      simp only [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations] at empty
      rw [List.map_cons, List.map_cons,
        priority_stageFor_eq_of_not_chiral own none (fun descriptor chiral => by cases chiral),
        map_priority_eq_of_chiralDescriptors_nil own rest empty]
  | some label :: rest, empty => by
      cases label with
      | pseudoasymmetric descriptor =>
          simp only [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations] at empty
          rw [List.map_cons, List.map_cons,
            priority_stageFor_eq_of_not_chiral own (some (.pseudoasymmetric descriptor))
              (fun other chiral => by cases chiral),
            map_priority_eq_of_chiralDescriptors_nil own rest empty]
      | chiral descriptor =>
          simp only [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations] at empty
          exact absurd empty (by simp)

/-- A depth sphere with exactly one uppercase chiral observation splits around that observation,
and everything before it is non-chiral. -/
theorem observations_split_of_chiralDescriptors_singleton :
    ∀ (observations : List (Option LocalizedAuxiliaryLabel)) (descriptor : RS),
      LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations observations =
          [descriptor] →
      ∃ pre post, observations = pre ++ some (.chiral descriptor) :: post ∧
        LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations pre = []
  | [], descriptor, unique => by
      simp [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations] at unique
  | none :: rest, descriptor, unique => by
      simp only [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations] at unique
      obtain ⟨pre, post, split, preEmpty⟩ :=
        observations_split_of_chiralDescriptors_singleton rest descriptor unique
      exact ⟨none :: pre, post, by rw [split]; rfl,
        by simp only [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations, preEmpty]⟩
  | some label :: rest, descriptor, unique => by
      cases label with
      | pseudoasymmetric pseudoDescriptor =>
          simp only [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations] at unique
          obtain ⟨pre, post, split, preEmpty⟩ :=
            observations_split_of_chiralDescriptors_singleton rest descriptor unique
          exact ⟨some (.pseudoasymmetric pseudoDescriptor) :: pre, post,
            by rw [split]; rfl,
            by simp only [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations,
              preEmpty]⟩
      | chiral chiralDescriptor =>
          simp only [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations,
            List.cons.injEq] at unique
          obtain ⟨chiralEq, _restEmpty⟩ := unique
          subst chiralEq
          exact ⟨[], rest, rfl, rfl⟩

/-- The comparison of the two priority observation lists at one depth that contains exactly one
uppercase chiral observation.  Everything before it is common to the two stages; at the chiral
observation the signed one-entry direction decides. -/
theorem compareLex_map_priority_chiral_singleton (own : Option RS) (descriptor : RS)
    (pre postR postS : List (Option LocalizedAuxiliaryLabel))
    (preEmpty : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations pre = []) :
    List.compareLex compareLocalizedCumulativeRule45Priority
        (pre.map (localizedCumulativeRule45Priority (localizedRule5StageFor own .R)) ++
          localizedCumulativeRule45Priority (localizedRule5StageFor own .R)
              (some (.chiral descriptor)) ::
            postR.map (localizedCumulativeRule45Priority (localizedRule5StageFor own .R)))
        (pre.map (localizedCumulativeRule45Priority (localizedRule5StageFor own .S)) ++
          localizedCumulativeRule45Priority (localizedRule5StageFor own .S)
              (some (.chiral descriptor)) ::
            postS.map (localizedCumulativeRule45Priority (localizedRule5StageFor own .S))) =
      (if descriptor = RS.R then Ordering.gt else Ordering.lt) := by
  rw [← map_priority_eq_of_chiralDescriptors_nil own pre preEmpty]
  exact compareLex_eq_of_prefix_cons compareLocalizedCumulativeRule45Priority
    (pre.map (localizedCumulativeRule45Priority (localizedRule5StageFor own .R)))
    (localizedCumulativeRule45Priority (localizedRule5StageFor own .R)
      (some (.chiral descriptor)))
    (localizedCumulativeRule45Priority (localizedRule5StageFor own .S)
      (some (.chiral descriptor)))
    (postR.map (localizedCumulativeRule45Priority (localizedRule5StageFor own .R)))
    (postS.map (localizedCumulativeRule45Priority (localizedRule5StageFor own .S)))
    (if descriptor = RS.R then Ordering.gt else Ordering.lt)
    comparePriority_refl
    (comparePriority_stageFor_R_S_chiral_sign own descriptor)
    (by cases descriptor <;> decide)

/-- `List.compareLex` is reflexive on a list when the entry comparator is reflexive. -/
theorem compareLex_self_of_refl {α : Type*} {compare : α → α → Ordering}
    (refl : ∀ a, compare a a = Ordering.eq) :
    ∀ list : List α, List.compareLex compare list list = Ordering.eq
  | [] => rfl
  | a :: rest => by
      rw [List.compareLex_cons_cons, refl a]
      exact compareLex_self_of_refl refl rest

/-- **The sphere at a chiral-free depth compares equal across the two common-reference stages.** -/
theorem compareSparseLayer_getD_eq_of_chiralDescriptors_nil
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} (own : Option RS)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (depth : Nat)
    (empty : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      (LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label)
        depth tree) = []) :
    List.compareLex
        (OfficialRuleMajorKey.compareSparseEntry compareLocalizedCumulativeRule45Priority)
        ((LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority
            (localizedRule5StageFor own .R) node.label) tree).getD depth [])
        ((LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority
            (localizedRule5StageFor own .S) node.label) tree).getD depth []) =
      Ordering.eq := by
  have addresses := table_addresses_getD
    (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .R) node.label)
    (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .S) node.label)
    tree depth
  rw [compareLex_flatten_eq_compareLex_observations compareLocalizedCumulativeRule45Priority
    _ _ addresses]
  rw [LocalizedUniqueNearestRule5Direction.descriptorTable_getD_map_snd,
    LocalizedUniqueNearestRule5Direction.descriptorTable_getD_map_snd,
    map_priority_eq_of_chiralDescriptors_nil own _ empty]
  exact compareLex_self_of_refl comparePriority_refl _

/-- **The sphere containing the unique chiral observation decides with the signed direction.** -/
theorem compareSparseLayer_getD_sign_of_chiralSingleton
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} (own : Option RS)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (depth : Nat) (descriptor : RS)
    (unique : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      (LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label)
        depth tree) = [descriptor]) :
    List.compareLex
        (OfficialRuleMajorKey.compareSparseEntry compareLocalizedCumulativeRule45Priority)
        ((LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority
            (localizedRule5StageFor own .R) node.label) tree).getD depth [])
        ((LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority
            (localizedRule5StageFor own .S) node.label) tree).getD depth []) =
      (if descriptor = RS.R then Ordering.gt else Ordering.lt) := by
  have addresses := table_addresses_getD
    (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .R) node.label)
    (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .S) node.label)
    tree depth
  rw [compareLex_flatten_eq_compareLex_observations compareLocalizedCumulativeRule45Priority
    _ _ addresses]
  rw [LocalizedUniqueNearestRule5Direction.descriptorTable_getD_map_snd,
    LocalizedUniqueNearestRule5Direction.descriptorTable_getD_map_snd]
  obtain ⟨pre, post, split, preEmpty⟩ :=
    observations_split_of_chiralDescriptors_singleton
      (LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label)
        depth tree) descriptor unique
  rw [split, List.map_append, List.map_append, List.map_cons, List.map_cons]
  exact compareLex_map_priority_chiral_singleton own descriptor pre post post preEmpty

/-! ## I. Layer-prefix comparison and the signed same-tree endpoint -/

/-- **First strict layer decides.**  If the two tables agree on every sphere before `depth` and the
sphere at `depth` decides strictly as `outcome`, then the whole sparse layered comparison is
`outcome`. -/
theorem compareSparseLayers_eq_of_layer_prefix {α : Type*}
    (compare : α → α → Ordering)
    (left right : List (List (OfficialSparseEntry α)))
    (depth : Nat) (outcome : Ordering)
    (lengthEq : left.length = right.length)
    (depthLt : depth < left.length)
    (prefixEq : ∀ e, e < depth →
      List.compareLex (OfficialRuleMajorKey.compareSparseEntry compare)
        (left.getD e []) (right.getD e []) = Ordering.eq)
    (decides : List.compareLex (OfficialRuleMajorKey.compareSparseEntry compare)
      (left.getD depth []) (right.getD depth []) = outcome)
    (strict : outcome ≠ Ordering.eq) :
    OfficialRuleMajorKey.compareSparseLayers compare left right = outcome := by
  unfold OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareSparseLayer
  induction left generalizing right depth with
  | nil => simp at depthLt
  | cons head tail ih =>
      cases right with
      | nil => simp at lengthEq
      | cons rightHead rightTail =>
          cases depth with
          | zero =>
              have headDecides :
                  List.compareLex (OfficialRuleMajorKey.compareSparseEntry compare)
                    head rightHead = outcome := by
                simpa using decides
              rw [List.compareLex_cons_cons, headDecides]
              cases outcome with
              | lt => rfl
              | gt => rfl
              | eq => exact absurd rfl strict
          | succ depth =>
              have headEq :
                  List.compareLex (OfficialRuleMajorKey.compareSparseEntry compare)
                    head rightHead = Ordering.eq := by
                have zero := prefixEq 0 (Nat.zero_lt_succ depth)
                simpa using zero
              have tailPrefix : ∀ e, e < depth →
                  List.compareLex (OfficialRuleMajorKey.compareSparseEntry compare)
                    (tail.getD e []) (rightTail.getD e []) = Ordering.eq := by
                intro e before
                have step := prefixEq (e + 1) (by omega)
                simpa using step
              have tailDecides :
                  List.compareLex (OfficialRuleMajorKey.compareSparseEntry compare)
                    (tail.getD depth []) (rightTail.getD depth []) = outcome := by
                simpa using decides
              rw [List.compareLex_cons_cons, headEq]
              exact ih rightTail depth (by simpa using lengthEq)
                (by simpa using depthLt) tailPrefix tailDecides

/-- **Signed same-tree endpoint at an arbitrary unique chiral depth.**

If one decorated tree has no uppercase chiral observation at any depth before `distance`, and its
depth-`distance` sphere contains exactly the uppercase descriptor `w`, then the actual sparse
comparator on the two common-reference cumulative stage tables of that one tree reports `gt` when
`w = R` and `lt` when `w = S`.  The depth is arbitrary and the deeper spheres are unrestricted. -/
theorem compareSparseLayers_stageFor_R_S_signed_of_uniqueChiral
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} (own : Option RS)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (distance : Nat) (descriptor : RS)
    (earlier : ∀ e, e < distance →
      LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        (LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label)
          e tree) = [])
    (unique : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      (LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label)
        distance tree) = [descriptor]) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority
            (localizedRule5StageFor own .R) node.label) tree)
        (LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority
            (localizedRule5StageFor own .S) node.label) tree) =
      (if descriptor = RS.R then Ordering.gt else Ordering.lt) := by
  have observationsNonempty :
      LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label)
        distance tree ≠ [] := by
    intro empty
    rw [empty] at unique
    exact absurd unique
      (by simp [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations])
  have tableRNonempty :
      (LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority
          (localizedRule5StageFor own .R) node.label) tree).getD distance [] ≠ [] := by
    intro empty
    apply observationsNonempty
    have mapped := LocalizedUniqueNearestRule5Direction.descriptorTable_getD_map_snd
      (localizedRule5StageFor own .R) tree distance
    rw [empty] at mapped
    exact List.map_eq_nil_iff.mp mapped.symm
  have depthLt : distance < (LocalizedCumulativeDecoratedTree.table
      (fun node => localizedCumulativeRule45Priority
        (localizedRule5StageFor own .R) node.label) tree).length :=
    getD_ne_nil_imp_lt_length _ distance tableRNonempty
  have lengthEq : (LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority
          (localizedRule5StageFor own .R) node.label) tree).length =
      (LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority
          (localizedRule5StageFor own .S) node.label) tree).length := by
    rw [LocalizedCumulativeDecoratedTree.table_length_eq_height,
      LocalizedCumulativeDecoratedTree.table_length_eq_height]
  exact compareSparseLayers_eq_of_layer_prefix compareLocalizedCumulativeRule45Priority
    _ _ distance (if descriptor = RS.R then Ordering.gt else Ordering.lt)
    lengthEq depthLt
    (fun e before => compareSparseLayer_getD_eq_of_chiralDescriptors_nil own tree e
      (earlier e before))
    (compareSparseLayer_getD_sign_of_chiralSingleton own tree distance descriptor unique)
    (by cases descriptor <;> decide)

/-- The `tables`-projection form of the signed same-tree endpoint: the descriptor columns of the
two stage table records of one decorated tree compare with the signed direction. -/
theorem tables_descriptor_stageFor_signed_of_uniqueChiral
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} (own : Option RS)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (distance : Nat) (descriptor : RS)
    (earlier : ∀ e, e < distance →
      LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        (LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label)
          e tree) = [])
    (unique : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      (LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label)
        distance tree) = [descriptor]) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        ((LocalizedCumulativeDecoratedTree.tables
          (localizedRule5StageFor own .R) tree).descriptor)
        ((LocalizedCumulativeDecoratedTree.tables
          (localizedRule5StageFor own .S) tree).descriptor) =
      (if descriptor = RS.R then Ordering.gt else Ordering.lt) := by
  simpa only [LocalizedCumulativeDecoratedTree.tables_descriptor] using
    compareSparseLayers_stageFor_R_S_signed_of_uniqueChiral own tree distance descriptor
      earlier unique

/-- **Cross-tree signed endpoint from a shared prefix through the unique nearest sphere.**

This is the exact interface needed for two *separate* common-reference stage builds.  The two
decorated trees need not be equal: it suffices that

* the two tables have the same sphere count (`lengthEq`) and a real sphere at `distance`,
* every sphere up to and including `distance` has the **same addresses** in the two tables
  (`addresses`; this is nearest-position/address stability),
* every depth sphere up to and including `distance` has the **same label observations**
  (`observations`; this is the shared prefix through the unique nearest mark),
* the shared observations are chiral-free before `distance` and contain exactly `descriptor` at
  `distance`.

Then the actual sparse comparator between the common-`R` table of the first tree and the
common-`S` table of the second tree reports `gt` for `descriptor = R` and `lt` for `descriptor = S`.
Deeper spheres, deeper detected centres and the trees above the shared prefix are unrestricted. -/
theorem compareSparseLayers_stageFor_R_S_signed_of_sharedThroughNearest
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} (own : Option RS)
    (leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (distance : Nat) (descriptor : RS)
    (lengthEq : (LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority
          (localizedRule5StageFor own .R) node.label) leftTree).length =
      (LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority
          (localizedRule5StageFor own .S) node.label) rightTree).length)
    (depthLt : distance < (LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority
          (localizedRule5StageFor own .R) node.label) leftTree).length)
    (addresses : ∀ d, d ≤ distance →
      ((LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority
          (localizedRule5StageFor own .R) node.label) leftTree).getD d []).map Prod.fst =
      ((LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority
          (localizedRule5StageFor own .S) node.label) rightTree).getD d []).map Prod.fst)
    (observations : ∀ d, d ≤ distance →
      LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label)
        d leftTree =
      LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label)
        d rightTree)
    (earlier : ∀ e, e < distance →
      LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        (LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label)
          e leftTree) = [])
    (unique : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      (LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label)
        distance leftTree) = [descriptor]) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority
            (localizedRule5StageFor own .R) node.label) leftTree)
        (LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority
            (localizedRule5StageFor own .S) node.label) rightTree) =
      (if descriptor = RS.R then Ordering.gt else Ordering.lt) := by
  refine compareSparseLayers_eq_of_layer_prefix compareLocalizedCumulativeRule45Priority
    _ _ distance (if descriptor = RS.R then Ordering.gt else Ordering.lt)
    lengthEq depthLt ?_ ?_ (by cases descriptor <;> decide)
  · intro e before
    rw [compareLex_flatten_eq_compareLex_observations compareLocalizedCumulativeRule45Priority
      _ _ (addresses e (le_of_lt before))]
    rw [LocalizedUniqueNearestRule5Direction.descriptorTable_getD_map_snd,
      LocalizedUniqueNearestRule5Direction.descriptorTable_getD_map_snd,
      ← observations e (le_of_lt before),
      map_priority_eq_of_chiralDescriptors_nil own _ (earlier e before)]
    exact compareLex_self_of_refl comparePriority_refl _
  · rw [compareLex_flatten_eq_compareLex_observations compareLocalizedCumulativeRule45Priority
      _ _ (addresses distance le_rfl)]
    rw [LocalizedUniqueNearestRule5Direction.descriptorTable_getD_map_snd,
      LocalizedUniqueNearestRule5Direction.descriptorTable_getD_map_snd,
      ← observations distance le_rfl]
    obtain ⟨pre, post, split, preEmpty⟩ :=
      observations_split_of_chiralDescriptors_singleton
        (LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label)
          distance leftTree) descriptor unique
    rw [split, List.map_append, List.map_append, List.map_cons, List.map_cons]
    exact compareLex_map_priority_chiral_singleton own descriptor pre post post preEmpty

/-! ## J. The actual production tree at the actual frame cursor -/

/-- **Signed actual-tree endpoint at a physically unique nearest centre.**

The tree is the actual Rule-4a build output `actualSlotTree` at the actual detected-inventory frame
cursor.  Both common-reference Rule-5 stage tables are evaluated on that one tree, so the address
alignment is derived (`table_sparseAlignment`) rather than assumed.  The unique chiral depth is the
physical simple-walk `distance` produced by `PhysicalBranchUniqueNearest`, and the descriptor is the
actual derived mark of the centre.  The conclusion is the signed direction itself: `gt` for `R`,
`lt` for `S`.  There is no reader law, no supplied reference, no per-depth label hypothesis, no
alignment premise and no sortedness assumption; deeper detected centres remain unrestricted and the
outer root, frame and configuration are the actual ones. -/
theorem actualSlotTree_stageFor_descriptorTable_signed_of_physicalUniqueNearest
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (own : Option RS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    ∃ descriptor : RS,
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          ((actualSlotTree input c frame frameComputed slot).tables
            (localizedRule5StageFor own .R)).descriptor
          ((actualSlotTree input c frame frameComputed slot).tables
            (localizedRule5StageFor own .S)).descriptor =
        (if descriptor = RS.R then Ordering.gt else Ordering.lt) ∧
      LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic
        (actualSlotTree input c frame frameComputed slot) center = some descriptor := by
  obtain ⟨descriptor, earlier, uniqueAt, mark⟩ :=
    LocalizedUniqueNearestRule5Direction.tree_observations_of_physicalBranchUniqueNearest
      input c frame frameComputed slot singleBonded acyclic hcharge noDouble cfg domain
      (oAtom := oAtom) oObserved
      (tree := actualSlotTree input c frame frameComputed slot)
      (sourceEq := actualSlotTree_source input c frame frameComputed slot)
      (realizes := actualSlotTree_realizes input c frame frameComputed slot)
      unique
  exact ⟨descriptor,
    tables_descriptor_stageFor_signed_of_uniqueChiral own
      (actualSlotTree input c frame frameComputed slot) distance descriptor earlier uniqueAt,
    mark⟩







theorem actualSlotTree_stageFor_descriptorTable_signed_of_actualGeneralRigidPhysicalDomain
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfgPhys : input.certified.detectedMultiCenterMolecule.Configuration)
    (physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfgPhys c)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (own : Option RS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    ∃ descriptor : RS,
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          ((actualSlotTree input c frame frameComputed slot).tables
            (localizedRule5StageFor own .R)).descriptor
          ((actualSlotTree input c frame frameComputed slot).tables
            (localizedRule5StageFor own .S)).descriptor =
        (if descriptor = RS.R then Ordering.gt else Ordering.lt) ∧
      LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic
        (actualSlotTree input c frame frameComputed slot) center = some descriptor :=
  actualSlotTree_stageFor_descriptorTable_signed_of_physicalUniqueNearest input c frame
    frameComputed slot singleBonded acyclic hcharge noDouble
    (cfg := input.certified.canonicalReindexConfiguration cfgPhys)
    (domain := actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
      input.certified cfgPhys c physicalDomain)
    oAtom oObserved own unique

/-! ## K. Nearest-prefix label stability and the signed descriptor endpoint

Sections G--J compare the two stage tables of **one** tree.  The actual through-Rule-5 endpoint
compares two keys produced by two *separate* stage builds, so the remaining question is exactly how
much of the tree shape must be shared.  This section proves that only the **label rows through the
unique nearest sphere** are needed: the descriptor table of a completed build is the priority image
of its label table, and a first strict difference between the two priority images is forced at the
unique uppercase chiral observation.  Nothing about addresses, sibling order or the spheres beyond
the nearest one enters the endpoint. -/

/-- The Rule-4a unit-kind bit `2` of an uppercase chiral label exceeds its `0`/`1` value under
**every** cumulative stage, so the first priority coordinate of a chiral label against a
non-chiral one decides `gt` independently of the common reference.  (This is the algebraic
ingredient of the nearest-position stability route: a constitutionally tied sibling that does not
contain the unique nearest chiral observation can never outrank the one that does.) -/
theorem comparePriority_chiral_gt_of_not_chiral
    (stage : LocalizedCumulativeRule45Stage) (descriptor : RS)
    (label : Option LocalizedAuxiliaryLabel)
    (notChiral : ∀ other : RS, label ≠ some (.chiral other)) :
    compareLocalizedCumulativeRule45Priority
        (localizedCumulativeRule45Priority stage (some (.chiral descriptor)))
        (localizedCumulativeRule45Priority stage label) = Ordering.gt := by
  cases stage <;>
    (cases label with
     | none => rfl
     | some inner =>
        cases inner with
        | pseudoasymmetric pseudo => cases pseudo <;> rfl
        | chiral other => exact absurd rfl (notChiral other))

/-- A chiral descriptor occurring in a label list occurs in its chiral-observation projection. -/
theorem mem_chiralDescriptorsOfObservations_of_mem :
    ∀ {labels : List (Option LocalizedAuxiliaryLabel)}
      {label : Option LocalizedAuxiliaryLabel}, label ∈ labels →
      ∀ {descriptor : RS}, label = some (.chiral descriptor) →
        descriptor ∈ LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations labels
  | [], _, present, _, _ => by simp at present
  | head :: rest, label, present, descriptor, chiral => by
      rcases List.mem_cons.mp present with same | later
      · subst same
        rw [chiral]
        simp only [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations]
        exact List.mem_cons_self ..
      · cases head with
        | none =>
            simp only [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations]
            exact mem_chiralDescriptorsOfObservations_of_mem later chiral
        | some inner =>
            cases inner with
            | pseudoasymmetric pseudo =>
                simp only [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations]
                exact mem_chiralDescriptorsOfObservations_of_mem later chiral
            | chiral other =>
                simp only [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations]
                exact List.mem_cons_of_mem other
                  (mem_chiralDescriptorsOfObservations_of_mem later chiral)

/-- A chiral-free label list contains no uppercase chiral label at all. -/
theorem not_chiral_of_chiralDescriptorsOfObservations_eq_nil
    {labels : List (Option LocalizedAuxiliaryLabel)}
    (empty : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations labels = [])
    {label : Option LocalizedAuxiliaryLabel} (present : label ∈ labels)
    {descriptor : RS} (chiral : label = some (.chiral descriptor)) : False := by
  have member := mem_chiralDescriptorsOfObservations_of_mem present chiral
  rw [empty] at member
  simp at member

/-- A single addressed entry carries equal priority images under the two common-reference stages
when its label is not uppercase chiral. -/
theorem mapObservation_stageFor_eq_of_not_chiral (own : Option RS)
    (entry : OfficialSparseEntry (Option LocalizedAuxiliaryLabel))
    (notChiral : ∀ other : RS, entry.2 ≠ some (.chiral other)) :
    OfficialRuleMajorKey.mapObservation
        (localizedCumulativeRule45Priority (localizedRule5StageFor own .R)) entry =
      OfficialRuleMajorKey.mapObservation
        (localizedCumulativeRule45Priority (localizedRule5StageFor own .S)) entry := by
  obtain ⟨address, label⟩ := entry
  show (address,
      localizedCumulativeRule45Priority (localizedRule5StageFor own .R) label) =
    (address, localizedCumulativeRule45Priority (localizedRule5StageFor own .S) label)
  rw [priority_stageFor_eq_of_not_chiral own label notChiral]

/-- A chiral-free addressed sphere has equal priority images under the two common-reference
stages. -/
theorem map_mapObservation_stageFor_eq_of_chiralDescriptors_nil (own : Option RS)
    (row : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))
    (empty : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      (row.map Prod.snd) = []) :
    row.map (OfficialRuleMajorKey.mapObservation
        (localizedCumulativeRule45Priority (localizedRule5StageFor own .R))) =
      row.map (OfficialRuleMajorKey.mapObservation
        (localizedCumulativeRule45Priority (localizedRule5StageFor own .S))) := by
  apply List.map_congr_left
  intro entry present
  exact mapObservation_stageFor_eq_of_not_chiral own entry fun other chiralEq =>
    not_chiral_of_chiralDescriptorsOfObservations_eq_nil empty
      (List.mem_map.mpr ⟨entry, present, chiralEq⟩) rfl

/-- `compareSparseEntry` is reflexive on any entry when the observation comparator is. -/
theorem compareSparseEntry_self {α : Type*}
    (compare : α → α → Ordering) (refl : ∀ value, compare value value = Ordering.eq) :
    ∀ entry : OfficialSparseEntry α,
      OfficialRuleMajorKey.compareSparseEntry compare entry entry = Ordering.eq := by
  intro entry
  obtain ⟨address, value⟩ := entry
  have same := compareSparseEntry_eq_of_address_eq compare
    (left := (address, value)) (right := (address, value)) rfl
  rw [same]
  exact refl value

/-- Comparing one shared address under the two stages reduces to comparing the two priority
vectors of its label. -/
theorem compareSparseEntry_mapObservation_stageFor
    (observeL observeR : Option LocalizedAuxiliaryLabel → List Nat)
    (address : List Nat) (label : Option LocalizedAuxiliaryLabel) :
    OfficialRuleMajorKey.compareSparseEntry compareLocalizedCumulativeRule45Priority
        (OfficialRuleMajorKey.mapObservation observeL (address, label))
        (OfficialRuleMajorKey.mapObservation observeR (address, label)) =
      compareLocalizedCumulativeRule45Priority (observeL label) (observeR label) := by
  show OfficialRuleMajorKey.compareSparseEntry compareLocalizedCumulativeRule45Priority
      (address, observeL label) (address, observeR label) =
    compareLocalizedCumulativeRule45Priority (observeL label) (observeR label)
  exact compareSparseEntry_eq_of_address_eq compareLocalizedCumulativeRule45Priority rfl

/-- The shared-address comparison at the unique uppercase chiral label reports the signed
direction. -/
theorem compareSparseEntry_mapObservation_stageFor_chiral (own : Option RS)
    (address : List Nat) (descriptor : RS) :
    OfficialRuleMajorKey.compareSparseEntry compareLocalizedCumulativeRule45Priority
        (OfficialRuleMajorKey.mapObservation
          (localizedCumulativeRule45Priority (localizedRule5StageFor own .R))
          (address, some (.chiral descriptor)))
        (OfficialRuleMajorKey.mapObservation
          (localizedCumulativeRule45Priority (localizedRule5StageFor own .S))
          (address, some (.chiral descriptor))) =
      (if descriptor = RS.R then Ordering.gt else Ordering.lt) := by
  rw [compareSparseEntry_mapObservation_stageFor]
  exact comparePriority_stageFor_R_S_chiral_sign own descriptor

/-- A chiral-free addressed sphere compares equal under the two common-reference stages. -/
theorem compareSparseLayer_map_stageFor_eq_of_chiralDescriptors_nil (own : Option RS)
    (row : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))
    (empty : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      (row.map Prod.snd) = []) :
    List.compareLex (OfficialRuleMajorKey.compareSparseEntry
        compareLocalizedCumulativeRule45Priority)
      (row.map (OfficialRuleMajorKey.mapObservation
        (localizedCumulativeRule45Priority (localizedRule5StageFor own .R))))
      (row.map (OfficialRuleMajorKey.mapObservation
        (localizedCumulativeRule45Priority (localizedRule5StageFor own .S)))) =
      Ordering.eq := by
  rw [map_mapObservation_stageFor_eq_of_chiralDescriptors_nil own row empty]
  exact compareLex_self_of_refl
    (compareSparseEntry_self compareLocalizedCumulativeRule45Priority comparePriority_refl) _

/-- An addressed sphere with exactly one uppercase chiral observation splits into a chiral-free
prefix, that observation, and an arbitrary suffix.  Addresses are never inspected. -/
theorem entries_split_of_chiralDescriptors_singleton :
    ∀ (row : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) (descriptor : RS),
      LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
          (row.map Prod.snd) = [descriptor] →
      ∃ (pre : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))
        (address : List Nat)
        (post : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))),
        row = pre ++ (address, some (.chiral descriptor)) :: post ∧
          LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
            (pre.map Prod.snd) = []
  | [], descriptor, unique => by
      simp [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations] at unique
  | (address, label) :: rest, descriptor, unique => by
      simp only [List.map_cons] at unique
      cases label with
      | none =>
          obtain ⟨pre, headAddress, post, split, preEmpty⟩ :=
            entries_split_of_chiralDescriptors_singleton rest descriptor (by
              simpa only [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations]
                using unique)
          exact ⟨(address, none) :: pre, headAddress, post, by rw [split]; rfl,
            by simp only [List.map_cons,
              LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations, preEmpty]⟩
      | some inner =>
          cases inner with
          | pseudoasymmetric pseudo =>
              obtain ⟨pre, headAddress, post, split, preEmpty⟩ :=
                entries_split_of_chiralDescriptors_singleton rest descriptor (by
                  simpa only [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations]
                    using unique)
              exact ⟨(address, some (.pseudoasymmetric pseudo)) :: pre, headAddress, post,
                by rw [split]; rfl,
                by simp only [List.map_cons,
                  LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations, preEmpty]⟩
          | chiral other =>
              simp only [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations,
                List.cons.injEq] at unique
              obtain ⟨otherEq, _⟩ := unique
              subst otherEq
              exact ⟨[], address, rest, rfl, rfl⟩

/-- The addressed sphere containing the unique uppercase chiral observation compares with the
signed direction, whatever the surrounding non-chiral observations are. -/
theorem compareSparseLayer_map_stageFor_signed_of_chiralDescriptors_singleton
    (own : Option RS)
    (row : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))
    (descriptor : RS)
    (unique : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      (row.map Prod.snd) = [descriptor]) :
    List.compareLex (OfficialRuleMajorKey.compareSparseEntry
        compareLocalizedCumulativeRule45Priority)
      (row.map (OfficialRuleMajorKey.mapObservation
        (localizedCumulativeRule45Priority (localizedRule5StageFor own .R))))
      (row.map (OfficialRuleMajorKey.mapObservation
        (localizedCumulativeRule45Priority (localizedRule5StageFor own .S)))) =
      (if descriptor = RS.R then Ordering.gt else Ordering.lt) := by
  obtain ⟨pre, address, post, split, preEmpty⟩ :=
    entries_split_of_chiralDescriptors_singleton row descriptor unique
  rw [split, List.map_append, List.map_append, List.map_cons, List.map_cons]
  rw [← map_mapObservation_stageFor_eq_of_chiralDescriptors_nil own pre preEmpty]
  exact compareLex_eq_of_prefix_cons
    (OfficialRuleMajorKey.compareSparseEntry compareLocalizedCumulativeRule45Priority)
    (pre.map (OfficialRuleMajorKey.mapObservation
      (localizedCumulativeRule45Priority (localizedRule5StageFor own .R))))
    (OfficialRuleMajorKey.mapObservation
      (localizedCumulativeRule45Priority (localizedRule5StageFor own .R))
      (address, some (.chiral descriptor)))
    (OfficialRuleMajorKey.mapObservation
      (localizedCumulativeRule45Priority (localizedRule5StageFor own .S))
      (address, some (.chiral descriptor)))
    (post.map (OfficialRuleMajorKey.mapObservation
      (localizedCumulativeRule45Priority (localizedRule5StageFor own .R))))
    (post.map (OfficialRuleMajorKey.mapObservation
      (localizedCumulativeRule45Priority (localizedRule5StageFor own .S))))
    (if descriptor = RS.R then Ordering.gt else Ordering.lt)
    (compareSparseEntry_self compareLocalizedCumulativeRule45Priority comparePriority_refl)
    (compareSparseEntry_mapObservation_stageFor_chiral own address descriptor)
    (by cases descriptor <;> decide)

/-- An addressed row is determined by its length and its two projections. -/
theorem sparseEntry_row_eq_of_columns_eq {α : Type*} :
    ∀ (left right : List (OfficialSparseEntry α)),
      left.length = right.length →
      left.map Prod.fst = right.map Prod.fst →
      left.map Prod.snd = right.map Prod.snd → left = right
  | [], [], _, _, _ => rfl
  | [], _ :: _, lengthEq, _, _ => by simp at lengthEq
  | _ :: _, [], lengthEq, _, _ => by simp at lengthEq
  | (leftAddress, leftValue) :: leftTail, (rightAddress, rightValue) :: rightTail,
      lengthEq, fstEq, sndEq => by
      simp only [List.map_cons, List.cons.injEq] at fstEq sndEq
      obtain ⟨addressEq, tailFstEq⟩ := fstEq
      obtain ⟨valueEq, tailSndEq⟩ := sndEq
      have addressEq' : leftAddress = rightAddress := addressEq
      have valueEq' : leftValue = rightValue := valueEq
      rw [addressEq', valueEq']
      exact congrArg (fun rest => (rightAddress, rightValue) :: rest)
        (sparseEntry_row_eq_of_columns_eq leftTail rightTail
          (by simpa using lengthEq) tailFstEq tailSndEq)

/-- **Label-row prefix from address alignment and label-observation agreement.**

This is the bridge from the section-I `sharedThroughNearest` form (same address rows and same label
observations through the nearest sphere) to the label-**row** prefix consumed by the signed
endpoint: equal addresses and equal labels entrywise reconstruct the equal rows. -/
theorem labelRowPrefix_of_addresses_and_observations
    (leftLabels rightLabels :
      List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (distance : Nat)
    (addresses : ∀ d, d ≤ distance →
      (leftLabels.getD d []).map Prod.fst = (rightLabels.getD d []).map Prod.fst)
    (observations : ∀ d, d ≤ distance →
      (leftLabels.getD d []).map Prod.snd = (rightLabels.getD d []).map Prod.snd) :
    ∀ d, d ≤ distance → leftLabels.getD d [] = rightLabels.getD d [] := by
  intro d within
  exact sparseEntry_row_eq_of_columns_eq _
    _
    (by
      have same := congrArg List.length (addresses d within)
      simpa only [List.length_map] using same)
    (addresses d within) (observations d within)

/-- **Signed descriptor direction from nearest-prefix label stability.**

Two label tables need not come from the same tree.  If they have the same sphere count, a real
sphere at `distance`, equal label rows at every depth up to and including `distance`, and the
shared rows are chiral-free before `distance` with exactly the uppercase descriptor `w` at
`distance`, then the actual sparse comparator between the common-`R` priority image of the first
and the common-`S` priority image of the second reports `gt` for `w = R` and `lt` for `w = S`.
Deeper spheres, addresses and sibling order are unrestricted: the labels are compared directly. -/
theorem compareSparseLayers_stageFor_signed_of_labelPrefix
    (own : Option RS)
    (leftLabels rightLabels :
      List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (distance : Nat) (descriptor : RS)
    (lengthEq : leftLabels.length = rightLabels.length)
    (leftLt : distance < leftLabels.length)
    (rowPrefix : ∀ d, d ≤ distance →
      leftLabels.getD d [] = rightLabels.getD d [])
    (earlier : ∀ e, e < distance →
      LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        ((leftLabels.getD e []).map Prod.snd) = [])
    (unique : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      ((leftLabels.getD distance []).map Prod.snd) = [descriptor]) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (OfficialRuleMajorKey.mapSourceLayers
          (localizedCumulativeRule45Priority (localizedRule5StageFor own .R)) leftLabels)
        (OfficialRuleMajorKey.mapSourceLayers
          (localizedCumulativeRule45Priority (localizedRule5StageFor own .S)) rightLabels) =
      (if descriptor = RS.R then Ordering.gt else Ordering.lt) := by
  refine compareSparseLayers_eq_of_layer_prefix compareLocalizedCumulativeRule45Priority
    _ _ distance (if descriptor = RS.R then Ordering.gt else Ordering.lt)
    ?_ ?_ ?_ ?_ (by cases descriptor <;> decide)
  · simpa only [OfficialRuleMajorKey.mapSourceLayers, List.length_map] using lengthEq
  · simpa only [OfficialRuleMajorKey.mapSourceLayers, List.length_map] using leftLt
  · intro e before
    rw [OfficialRuleMajorKey.mapSourceLayers_getD,
      OfficialRuleMajorKey.mapSourceLayers_getD,
      ← rowPrefix e (le_of_lt before)]
    exact compareSparseLayer_map_stageFor_eq_of_chiralDescriptors_nil own
      (leftLabels.getD e []) (earlier e before)
  · rw [OfficialRuleMajorKey.mapSourceLayers_getD,
      OfficialRuleMajorKey.mapSourceLayers_getD,
      ← rowPrefix distance le_rfl]
    exact compareSparseLayer_map_stageFor_signed_of_chiralDescriptors_singleton own
      (leftLabels.getD distance []) descriptor unique

/-- The descriptor table of any completed cumulative build is the priority image of its label
table.  This transfers the label-level algebra to the actual production builder outputs. -/
theorem buildLocalizedRerootCumulativeRule45Key?_descriptor_eq_labels
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key) :
    key.descriptor =
      key.labels.map (List.map fun entry =>
        (entry.1, localizedCumulativeRule45Priority stage entry.2)) := by
  have withRead : input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
      (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor =
        some key := by
    rw [input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
      stage target view fuel cursor]
    exact computed
  exact input.buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptor_eq_labels
    stage _ fuel cursor key withRead

/-- **Builder-level signed descriptor direction from nearest-prefix label stability.**

The two keys are the actual outputs of the two common-reference stage builds at the same
target/view/fuel/cursor.  Only the length and the label rows through `distance` are required;
their descriptor tables are the priority images of those rows by the builder coherence above. -/
theorem buildLocalizedRerootCumulativeRule45Key?_stageFor_descriptor_signed_of_labelPrefix
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} (own : Option RS)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (keyR keyS : input.LocalizedRerootCumulativeRule45Key)
    (computedR : input.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .R) target view fuel cursor = some keyR)
    (computedS : input.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .S) target view fuel cursor = some keyS)
    (distance : Nat) (descriptor : RS)
    (lengthEq : keyR.labels.length = keyS.labels.length)
    (leftLt : distance < keyR.labels.length)
    (rowPrefix : ∀ d, d ≤ distance →
      keyR.labels.getD d [] = keyS.labels.getD d [])
    (earlier : ∀ e, e < distance →
      LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        ((keyR.labels.getD e []).map Prod.snd) = [])
    (unique : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      ((keyR.labels.getD distance []).map Prod.snd) = [descriptor]) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        keyR.descriptor keyS.descriptor =
      (if descriptor = RS.R then Ordering.gt else Ordering.lt) := by
  rw [buildLocalizedRerootCumulativeRule45Key?_descriptor_eq_labels input
        (localizedRule5StageFor own .R) target view fuel cursor keyR computedR,
      buildLocalizedRerootCumulativeRule45Key?_descriptor_eq_labels input
        (localizedRule5StageFor own .S) target view fuel cursor keyS computedS]
  exact compareSparseLayers_stageFor_signed_of_labelPrefix own keyR.labels keyS.labels
    distance descriptor lengthEq leftLt rowPrefix earlier unique

/-- **Physical transfer to the actual build's label table.**

For the actual cumulative build at the actual frame cursor, the pure physical predicate
`PhysicalBranchUniqueNearest` forces the actual key's label rows to be chiral-free before the
physical distance and to carry exactly the unique descriptor at it.  The build output is connected
to the realized decorated tree by `exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key?`
and its exact label table. -/
theorem key_labels_chiralObservations_of_physicalUniqueNearest
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (stage : LocalizedCumulativeRule45Stage)
    (key : input.certified.LocalizedRerootCumulativeRule45Key)
    (computed : input.certified.buildLocalizedRerootCumulativeRule45Key? stage
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) = some key)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    ∃ descriptor : RS,
      (∀ e, e < distance →
        LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
          ((key.labels.getD e []).map Prod.snd) = []) ∧
      LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        ((key.labels.getD distance []).map Prod.snd) = [descriptor] := by
  obtain ⟨tree, treeSource, _tableMatch, labelTable, realizes⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key? input.certified stage
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) key computed
  have realizesReader : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) tree := realizes
  obtain ⟨descriptor, earlier, uniqueAt, _mark⟩ :=
    LocalizedUniqueNearestRule5Direction.tree_observations_of_physicalBranchUniqueNearest
      input c frame frameComputed slot singleBonded acyclic hcharge noDouble cfg domain
      (oAtom := oAtom) oObserved (tree := tree) (sourceEq := treeSource)
      (realizes := realizesReader) unique
  refine ⟨descriptor, fun e before => ?_, ?_⟩
  · rw [← labelTable, LocalizedCumulativeDecoratedTree.labelTable_getD_map_snd]
    exact earlier e before
  · rw [← labelTable, LocalizedCumulativeDecoratedTree.labelTable_getD_map_snd]
    exact uniqueAt

/-- **Signed descriptor endpoint on the two actual common-reference stage builds at a physically
unique nearest centre.**

The two keys are arbitrary outputs of the two actual stage builders at the same actual frame
cursor.  The physical predicate supplies the unique nearest chiral observation of the common-`R`
build; the only remaining hypothesis is the nearest-prefix label stability of the two builds (equal
label-row count and equal label rows at every depth up to and including the physical distance).
Then the actual sparse comparator on the two descriptor tables reports the signed direction of the
physically derived descriptor.  No address or sortedness hypothesis is used. -/
theorem buildLocalizedRerootCumulativeRule45Key?_stageFor_signed_of_physicalUniqueNearest
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (own : Option RS)
    (keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key)
    (computedR : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) = some keyR)
    (computedS : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) = some keyS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance)
    (lengthEq : keyR.labels.length = keyS.labels.length)
    (rowPrefix : ∀ d, d ≤ distance →
      keyR.labels.getD d [] = keyS.labels.getD d []) :
    ∃ descriptor : RS,
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          keyR.descriptor keyS.descriptor =
        (if descriptor = RS.R then Ordering.gt else Ordering.lt) := by
  obtain ⟨descriptor, earlier, uniqueAt⟩ :=
    key_labels_chiralObservations_of_physicalUniqueNearest input c frame frameComputed slot
      singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved
      (localizedRule5StageFor own .R) keyR computedR unique
  have leftLt : distance < keyR.labels.length :=
    getD_ne_nil_imp_lt_length keyR.labels distance (by
      intro empty
      rw [empty] at uniqueAt
      simp [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations] at uniqueAt)
  exact ⟨descriptor,
    buildLocalizedRerootCumulativeRule45Key?_stageFor_descriptor_signed_of_labelPrefix
      input.certified own _ _ _ _ keyR keyS computedR computedS distance descriptor
      lengthEq leftLt rowPrefix earlier uniqueAt⟩














theorem actualSlot_compoundReading_stageFor_signed_of_physicalUniqueNearest
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance)
    (prefixStable : ∀ (r : RS)
      (keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key),
      input.certified.buildLocalizedRerootCumulativeRule45Key?
        (localizedRule5StageFor (some r) .R)
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (referenceDependencyView input c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt slot) = some keyR →
      input.certified.buildLocalizedRerootCumulativeRule45Key?
        (localizedRule5StageFor (some r) .S)
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (referenceDependencyView input c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt slot) = some keyS →
      keyR.labels.length = keyS.labels.length ∧
        ∀ d, d ≤ distance →
          keyR.labels.getD d [] = keyS.labels.getD d []) :
    ∃ (r : RS)
      (priorReading : input.certified.LocalizedRerootRule4bcReading)
      (reading : input.certified.LocalizedRerootRule5Reading)
      (keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key)
      (descriptor : RS),
      input.certified.buildLocalizedRerootCompoundRule45Key?
          (ActualReaderPhysicalBranchInverse.topTarget input c)
          (referenceDependencyView input c)
          (localizedOccurrenceRerootEvaluationFuel
            (LocalizedUniversalReference.carrierFuel input))
          (frame.cursorAt slot) =
        some (actualSlotCompoundKey input c frame frameComputed slot) ∧
      (actualSlotCompoundKey input c frame frameComputed slot).prior.references = [r] ∧
      (actualSlotCompoundKey input c frame frameComputed slot).prior.readings = [priorReading] ∧
      priorReading.reference? = some r ∧
      (actualSlotCompoundKey input c frame frameComputed slot).rule5Readings = [reading] ∧
      reading.prior = priorReading ∧
      reading.commonR = keyR ∧
      reading.commonS = keyS ∧
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          keyR.descriptor keyS.descriptor =
        (if descriptor = RS.R then Ordering.gt else Ordering.lt) := by
  obtain ⟨r, priorReading, reading, keyR, keyS, compoundBuilt, referencesSingleton,
    readingsSingleton, referenceSome, keyReadingsSingleton, priorEq, builtR, builtS,
    commonREq, commonSEq, _descriptorNe⟩ :=
    actualSlot_compoundReading_singleton_aligned_of_physicalUniqueNearest input c frame
      frameComputed slot singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved
      unique
  obtain ⟨lengthEq, rowPrefix⟩ := prefixStable r keyR keyS builtR builtS
  obtain ⟨descriptor, signed⟩ :=
    buildLocalizedRerootCumulativeRule45Key?_stageFor_signed_of_physicalUniqueNearest
      input c frame frameComputed slot singleBonded acyclic hcharge noDouble cfg domain
      oAtom oObserved (own := some r) keyR keyS builtR builtS unique lengthEq rowPrefix
  exact ⟨r, priorReading, reading, keyR, keyS, descriptor, compoundBuilt,
    referencesSingleton, readingsSingleton, referenceSome, keyReadingsSingleton, priorEq,
    commonREq, commonSEq, signed⟩

end LocalizedActualUniqueNearestRule5Direction

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.stagePriorityPrefix_stageFor_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.stageRule5Probe_stageFor
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.cumulativePriority_none_eq_stageFor
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.comparePriority_stageFor_R_S_chiral_sign
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareSparseLayers_stageFor_R_S_chiral_sign
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareLex_eq_of_prefix_cons
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.comparePriority_refl
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareSparseLayers_stageFor_R_S_signed_of_alignment
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareRule5Readings_R_sign_of_singleton_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.throughRule5_signed_pseudo_of_singleton_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.prefixLayer_map_fst
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.zipIdx_map_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.mergePairs_map_zipIdx
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.mem_fst_of_mem_zipIdx
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.mergePairs_children_map_map_fst_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.localizedTreeChildLayerCount_foldl_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.localizedTreeChildLayerCount_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.table_addresses_getD
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.getD_ne_nil_imp_lt_length
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.flatMap_length_eq_of_length_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.observationsAtDepth_length_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.table_sparseAlignment
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.priority_stageFor_eq_of_not_chiral
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.map_priority_eq_of_chiralDescriptors_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.observations_split_of_chiralDescriptors_singleton
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareLex_map_priority_chiral_singleton
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareLex_self_of_refl
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareSparseLayer_getD_eq_of_chiralDescriptors_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareSparseLayer_getD_sign_of_chiralSingleton
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareSparseLayers_eq_of_layer_prefix
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareSparseLayers_stageFor_R_S_signed_of_uniqueChiral
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.tables_descriptor_stageFor_signed_of_uniqueChiral
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareSparseLayers_stageFor_R_S_signed_of_sharedThroughNearest
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.actualSlotTree_stageFor_descriptorTable_signed_of_physicalUniqueNearest
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.actualSlotTree_stageFor_descriptorTable_signed_of_actualGeneralRigidPhysicalDomain
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.comparePriority_chiral_gt_of_not_chiral
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.mem_chiralDescriptorsOfObservations_of_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.not_chiral_of_chiralDescriptorsOfObservations_eq_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.mapObservation_stageFor_eq_of_not_chiral
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.map_mapObservation_stageFor_eq_of_chiralDescriptors_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareSparseEntry_self
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareSparseEntry_mapObservation_stageFor
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareSparseEntry_mapObservation_stageFor_chiral
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareSparseLayer_map_stageFor_eq_of_chiralDescriptors_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.entries_split_of_chiralDescriptors_singleton
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareSparseLayer_map_stageFor_signed_of_chiralDescriptors_singleton
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.sparseEntry_row_eq_of_columns_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.labelRowPrefix_of_addresses_and_observations
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.compareSparseLayers_stageFor_signed_of_labelPrefix
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.buildLocalizedRerootCumulativeRule45Key?_descriptor_eq_labels
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.buildLocalizedRerootCumulativeRule45Key?_stageFor_descriptor_signed_of_labelPrefix
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.key_labels_chiralObservations_of_physicalUniqueNearest
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.buildLocalizedRerootCumulativeRule45Key?_stageFor_signed_of_physicalUniqueNearest
assert_kernel_only TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction.actualSlot_compoundReading_stageFor_signed_of_physicalUniqueNearest
