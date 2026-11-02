import TetraStereo.OneCenter.LocalizedOuterDigraphConstitutionalPriority
import TetraStereo.OneCenter.LocalizedActualRecursiveSortTrace
import TetraStereo.OneCenter.LocalizedSparseSupportAlignment
import TetraStereo.OneCenter.DeclarativeCIPFirstDifferenceSchedule
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput






















































variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-! ## A. Totalized physical observation schedule -/

/-- **Totalized physical Rule-1b observation.**  The graph distance from the fixed original
`outerRoot` to the atom living at a present position; zero at absent positions.  Distance may
legitimately be zero at a present position (the outer root itself); no positivity is assumed. -/
noncomputable def physicalOuterRootDistanceAt
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (outerRoot : input.Atom)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (position : List Nat) : Nat :=
  ((subtreeAt? tree position).map fun node =>
    input.moleculeGraph.underlyingSimpleGraph.dist outerRoot (nodeAtom singleBonded acyclic node)).getD 0

/-- **Totalized physical Rule-2 observation.**  The graph atom mass of the atom living at a
present position; zero at absent positions.  Mass may legitimately be zero at a present position;
no positivity is assumed. -/
noncomputable def physicalAtomMassAt
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (position : List Nat) : Nat :=
  ((subtreeAt? tree position).map fun node =>
    input.moleculeGraph.atomMass (nodeAtom singleBonded acyclic node)).getD 0

/-! ## B. All-position alignment of the later columns with the physical schedule -/




theorem physicalOuterRootDistanceAt_eq_tableValue_rule1bDistance
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input r tree)
    (outerRoot : input.Atom)
    (root : tree.source.occurrence.1.root = outerRoot)
    (position : List Nat) :
    physicalOuterRootDistanceAt singleBonded acyclic outerRoot tree position =
      SparsePhysicalFirstDifference.tableValue
        (LocalizedCumulativeDecoratedTree.table (fun node => node.rule1bDistance) tree) position := by
  cases hLookup : subtreeAt? tree position with
  | some node =>
      rw [physicalOuterRootDistanceAt, hLookup]
      simp only [Option.map_some, Option.getD_some]
      have nodeEq : node =
          positionNode (⟨position, by rw [hLookup]; simp⟩ : Position tree) := by
        have spec : subtreeAt? tree position =
            some (positionNode (⟨position, by rw [hLookup]; simp⟩ : Position tree)) := by
          exact positionNode_spec (⟨position, by rw [hLookup]; simp⟩ : Position tree)
        exact Option.some.inj (hLookup.symm.trans spec)
      rw [nodeEq]
      rw [tableValue_rule1bDistance_eq_outerRoot_dist singleBonded acyclic realizes
        (⟨position, by rw [hLookup]; simp⟩ : Position tree)]
      rw [root]
      rfl
  | none =>
      rw [physicalOuterRootDistanceAt, hLookup]
      simp only [Option.map_none, Option.getD_none]
      rw [← tableValue_eq_zero_of_subtreeAt?_none (fun node => node.rule1bDistance) position tree hLookup]

/-- The totalized physical Rule-2 observation at every address equals the compiled isotope-mass
table: graph atom mass at present positions, zero at absent positions. -/
theorem physicalAtomMassAt_eq_tableValue_isotopeMass
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input r tree)
    (position : List Nat) :
    physicalAtomMassAt singleBonded acyclic tree position =
      SparsePhysicalFirstDifference.tableValue
        (LocalizedCumulativeDecoratedTree.table (fun node => node.isotopeMass) tree) position := by
  cases hLookup : subtreeAt? tree position with
  | some node =>
      rw [physicalAtomMassAt, hLookup]
      simp only [Option.map_some, Option.getD_some]
      have nodeEq : node =
          positionNode (⟨position, by rw [hLookup]; simp⟩ : Position tree) := by
        have spec : subtreeAt? tree position =
            some (positionNode (⟨position, by rw [hLookup]; simp⟩ : Position tree)) := by
          exact positionNode_spec (⟨position, by rw [hLookup]; simp⟩ : Position tree)
        exact Option.some.inj (hLookup.symm.trans spec)
      rw [nodeEq]
      rw [tableValue_isotopeMass_eq_atomMass singleBonded acyclic realizes
        (⟨position, by rw [hLookup]; simp⟩ : Position tree)]
      rfl
  | none =>
      rw [physicalAtomMassAt, hLookup]
      simp only [Option.map_none, Option.getD_none]
      rw [← tableValue_eq_zero_of_subtreeAt?_none (fun node => node.isotopeMass) position tree hLookup]

/-! ## C. Common sphere-major address schedule -/

/-- Reading a row at the address of a member entry returns the stored observation; the strictly
increasing row order rules out earlier same-address entries. -/
private theorem rowValueAt_eq_snd_of_mem {row : List (OfficialSparseEntry ℕ)}
    (sorted : row.Pairwise fun left right =>
      SparsePhysicalFirstDifference.AddressCompare left.1 right.1 = Ordering.lt)
    {entry : OfficialSparseEntry ℕ} (present : entry ∈ row) :
    SparsePhysicalFirstDifference.rowValueAt row entry.1 = entry.2 := by
  induction row with
  | nil => cases present
  | cons head tail ih =>
      rcases List.mem_cons.mp present with rfl | later
      · simp
      · have headBefore : SparsePhysicalFirstDifference.AddressCompare head.1 entry.1 =
            Ordering.lt := (List.pairwise_cons.mp sorted).1 entry later
        have headNe : head.1 ≠ entry.1 := by
          intro same
          rw [same, SparsePhysicalFirstDifference.AddressCompare_refl] at headBefore
          exact Ordering.noConfusion headBefore
        rw [SparsePhysicalFirstDifference.rowValueAt_cons_of_ne head tail entry.1 headNe]
        exact ih (List.pairwise_cons.mp sorted).2 later

/-- Reading a well-formed table at the address of a member entry returns the stored observation. -/
private theorem tableValue_eq_snd_of_mem_flatten
    {table : List (List (OfficialSparseEntry ℕ))}
    (depthExact : SparsePhysicalFirstDifference.RowsAtDepth 0 table)
    (increasing : SparsePhysicalFirstDifference.RowsIncreasing table)
    {depth : Nat} {entry : OfficialSparseEntry ℕ}
    (present : entry ∈ table.getD depth []) :
    SparsePhysicalFirstDifference.tableValue table entry.1 = entry.2 := by
  have lengthEq : entry.1.length = depth := by
    simpa using (depthExact depth entry present)
  unfold SparsePhysicalFirstDifference.tableValue
  rw [lengthEq]
  exact rowValueAt_eq_snd_of_mem (increasing depth) present

/-- The flattened address sequence of a well-formed table is strictly sphere-major ordered. -/
private theorem flatten_addresses_pairwise
    {table : List (List (OfficialSparseEntry ℕ))} :
    ∀ {offset : Nat}, (depthExact : SparsePhysicalFirstDifference.RowsAtDepth offset table) →
      (increasing : SparsePhysicalFirstDifference.RowsIncreasing table) →
      (table.flatten.map Prod.fst).Pairwise DeclarativeCIP.HierarchyAddressBefore := by
  intro offset
  induction table generalizing offset with
  | nil =>
      intro depthExact increasing
      simp
  | cons head tail ih =>
      intro depthExact increasing
      rw [List.flatten_cons, List.map_append, List.pairwise_append]
      have tailDepthExact : SparsePhysicalFirstDifference.RowsAtDepth (offset + 1) tail :=
        SparsePhysicalFirstDifference.RowsAtDepth.tail depthExact
      have tailIncreasing : SparsePhysicalFirstDifference.RowsIncreasing tail :=
        SparsePhysicalFirstDifference.RowsIncreasing.tail increasing
      refine ⟨?_, ?_, ?_⟩
      · exact SparsePhysicalFirstDifference.pairwise_map_fst_of_row head
          (SparsePhysicalFirstDifference.RowsAtDepth.head depthExact) (increasing 0)
      · exact ih tailDepthExact tailIncreasing
      · intro leftPosition leftPresent rightPosition rightPresent
        obtain ⟨leftEntry, leftEntryMem, rfl⟩ := List.mem_map.mp leftPresent
        obtain ⟨rightEntry, rightEntryMem, rfl⟩ := List.mem_map.mp rightPresent
        have leftLength : leftEntry.1.length = offset :=
          SparsePhysicalFirstDifference.RowsAtDepth.head depthExact leftEntry leftEntryMem
        obtain ⟨rightRow, rightRowMem, rightEntryInRow⟩ := List.mem_flatten.mp rightEntryMem
        obtain ⟨rightDepth, rightRowLookup⟩ := List.mem_iff_getElem?.mp rightRowMem
        have rightRowEq : tail.getD rightDepth [] = rightRow := by
          rw [List.getD_eq_getElem?_getD, rightRowLookup]
          rfl
        have inTailRow : rightEntry ∈ tail.getD rightDepth [] := by
          rw [rightRowEq]
          exact rightEntryInRow
        have rightLength : rightEntry.1.length = offset + 1 + rightDepth :=
          tailDepthExact rightDepth rightEntry inTailRow
        exact SparsePhysicalFirstDifference.hierarchyAddressBefore_of_length_lt (by
          rw [leftLength, rightLength]
          omega)

/-- The flattened observation sequence of a well-formed table is the table read at the flattened
address sequence. -/
private theorem flatten_snd_eq_map_tableValue
    {table : List (List (OfficialSparseEntry ℕ))}
    (depthExact : SparsePhysicalFirstDifference.RowsAtDepth 0 table)
    (increasing : SparsePhysicalFirstDifference.RowsIncreasing table) :
    table.flatten.map Prod.snd =
      (table.flatten.map Prod.fst).map (SparsePhysicalFirstDifference.tableValue table) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro entry present
  obtain ⟨row, rowMem, entryMem⟩ := List.mem_flatten.mp present
  obtain ⟨depth, rowLookup⟩ := List.mem_iff_getElem?.mp rowMem
  have rowEq : table.getD depth [] = row := by
    rw [List.getD_eq_getElem?_getD, rowLookup]
    rfl
  rw [← rowEq] at entryMem
  exact (tableValue_eq_snd_of_mem_flatten depthExact increasing entryMem).symm

/-- The address of every entry of every layer is a member of the flattened address sequence. -/
private theorem mem_flatten_map_fst_of_getD
    {table : List (List (OfficialSparseEntry ℕ))}
    {depth : Nat} {entry : OfficialSparseEntry ℕ}
    (present : entry ∈ table.getD depth []) :
    entry.1 ∈ table.flatten.map Prod.fst := by
  have rowInTable : table.getD depth [] ∈ table := by
    cases hd : table[depth]? with
    | some row =>
        rw [List.getD_eq_getElem?_getD, hd]
        exact List.mem_iff_getElem?.mpr ⟨depth, hd⟩
    | none =>
        have empty : table.getD depth [] = [] := by
          rw [List.getD_eq_getElem?_getD, hd]
          rfl
        have inNil : entry ∈ ([] : List (OfficialSparseEntry ℕ)) := by
          rw [← empty]
          exact present
        exact False.elim (List.not_mem_nil inNil)
  exact List.mem_map.mpr ⟨entry, List.mem_flatten.mpr ⟨table.getD depth [], rowInTable, present⟩, rfl⟩

/-! ## D. Later-column first differences -/

/-- **Physical Rule-1b direction.**  After a Rule-1a tie, the executed Rule-1b comparison of the
compiled distance tables realizes the independent physical Rule-1b first difference on the common
sphere-major address schedule: the decisive address carries the graph distances from the original
`outerRoot`, absent addresses read zero, and earlier addresses tie. -/
theorem table_rule1b_compareSparseLayers_eq_physical_firstDifference
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {readLeft readRight : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizesLeft : LocalizedCumulativeTreeRealizes input readLeft leftTree)
    (realizesRight : LocalizedCumulativeTreeRealizes input readRight rightTree)
    (outerRoot : input.Atom)
    (leftRoot : leftTree.source.occurrence.1.root = outerRoot)
    (rightRoot : rightTree.source.occurrence.1.root = outerRoot)
    (rule1aTie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree)
      (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree) =
        Ordering.eq)
    (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
        (LocalizedCumulativeDecoratedTree.table (fun node => node.rule1bDistance) leftTree)
        (LocalizedCumulativeDecoratedTree.table (fun node => node.rule1bDistance) rightTree) =
          outcome ↔
      DeclarativeCIP.FirstDifferenceOutcome
        (fun position result =>
          DeclarativeCIP.Rule1bDistanceOutcome
            (physicalOuterRootDistanceAt singleBonded acyclic outerRoot leftTree position)
            (physicalOuterRootDistanceAt singleBonded acyclic outerRoot rightTree position)
            result)
        outcome := by
  let leftTable : List (List (OfficialSparseEntry ℕ)) :=
    LocalizedCumulativeDecoratedTree.table (fun node => node.rule1bDistance) leftTree
  let rightTable : List (List (OfficialSparseEntry ℕ)) :=
    LocalizedCumulativeDecoratedTree.table (fun node => node.rule1bDistance) rightTree
  have leftWellFormed : SparsePhysicalFirstDifference.SparseTableWellFormed leftTable :=
    LocalizedActualTableAddressOrder.table_wellFormed (fun node => node.rule1bDistance) leftTree
  have rightWellFormed : SparsePhysicalFirstDifference.SparseTableWellFormed rightTable :=
    LocalizedActualTableAddressOrder.table_wellFormed (fun node => node.rule1bDistance) rightTree
  rw [LocalizedActualTableAddressOrder.laterTable_compareSparseLayers_eq_compareLex_of_atomicNumberTie
    singleBonded acyclic realizesLeft realizesRight rule1aTie
    (fun node => node.rule1bDistance) (fun node => node.rule1bDistance)
    OfficialRuleMajorKey.compareRule1b]
  have leftFlatten : leftTable.flatten.map Prod.snd =
      (leftTable.flatten.map Prod.fst).map (SparsePhysicalFirstDifference.tableValue leftTable) :=
    flatten_snd_eq_map_tableValue leftWellFormed.depthExact leftWellFormed.increasing
  have rightFlatten : rightTable.flatten.map Prod.snd =
      (rightTable.flatten.map Prod.fst).map (SparsePhysicalFirstDifference.tableValue rightTable) :=
    flatten_snd_eq_map_tableValue rightWellFormed.depthExact rightWellFormed.increasing
  rw [leftFlatten, rightFlatten]
  have align1a : SparseSupportAlignment.SparseAlignment
      (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree)
      (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree) :=
    SparseSupportAlignment.alignment_of_compareSparseLayers_eq
      (LocalizedActualTableAddressOrder.table_wellFormed (fun node => node.atomicNumber) leftTree)
      (LocalizedActualTableAddressOrder.table_wellFormed (fun node => node.atomicNumber) rightTree)
      (LocalizedActualTableAddressOrder.table_atomicNumber_positive_of_realizes
        singleBonded acyclic realizesLeft)
      (LocalizedActualTableAddressOrder.table_atomicNumber_positive_of_realizes
        singleBonded acyclic realizesRight)
      rule1aTie
  have sameAddresses : leftTable.flatten.map Prod.fst = rightTable.flatten.map Prod.fst :=
    (SparseSupportAlignment.SparseAlignment.ofSameAddressRows align1a
      (LocalizedActualTableAddressOrder.SameAddressRows_table
        (fun node => node.rule1bDistance) (fun node => node.atomicNumber) leftTree)
      (LocalizedActualTableAddressOrder.SameAddressRows_table
        (fun node => node.rule1bDistance) (fun node => node.atomicNumber) rightTree)).sameAddresses
  rw [← sameAddresses]
  refine (DeclarativeCIP.compareLex_map_iff_firstDifference
    OfficialRuleMajorKey.compareRule1b
    (fun position => SparsePhysicalFirstDifference.tableValue leftTable position)
    (fun position => SparsePhysicalFirstDifference.tableValue rightTable position)
    (leftTable.flatten.map Prod.fst)
    (flatten_addresses_pairwise leftWellFormed.depthExact leftWellFormed.increasing)
    ?outside outcome).trans ?congr
  · intro position absent
    have leftZero : SparsePhysicalFirstDifference.tableValue leftTable position = 0 :=
      SparsePhysicalFirstDifference.tableValue_eq_zero_of_absent leftTable position (by
        intro depth entry present same
        exact absent (by simpa [same] using mem_flatten_map_fst_of_getD present))
    have rightAbsent : position ∉ rightTable.flatten.map Prod.fst := by
      rw [← sameAddresses]
      exact absent
    have rightZero : SparsePhysicalFirstDifference.tableValue rightTable position = 0 :=
      SparsePhysicalFirstDifference.tableValue_eq_zero_of_absent rightTable position (by
        intro depth entry present same
        exact rightAbsent (by simpa [same] using mem_flatten_map_fst_of_getD present))
    change OfficialRuleMajorKey.compareRule1b
      (SparsePhysicalFirstDifference.tableValue leftTable position)
      (SparsePhysicalFirstDifference.tableValue rightTable position) = Ordering.eq
    rw [leftZero, rightZero]
    unfold OfficialRuleMajorKey.compareRule1b
    exact SparsePhysicalFirstDifference.compareNat_zero_zero
  · apply DeclarativeCIP.FirstDifferenceOutcome.congr
    intro position result
    rw [physicalOuterRootDistanceAt_eq_tableValue_rule1bDistance singleBonded acyclic
        realizesLeft outerRoot leftRoot position,
      physicalOuterRootDistanceAt_eq_tableValue_rule1bDistance singleBonded acyclic
        realizesRight outerRoot rightRoot position]
    exact OfficialRuleMajorKey.compareRule1b_eq_iff_rule1bDistanceOutcome
      (SparsePhysicalFirstDifference.tableValue leftTable position)
      (SparsePhysicalFirstDifference.tableValue rightTable position) result

/-- **Physical Rule-2 direction.**  After a Rule-1a tie, the executed Rule-2 comparison of the
compiled mass tables realizes the independent physical Rule-2 first difference on the common
sphere-major address schedule: larger mass is senior, absent addresses read zero. -/
theorem table_rule2_compareSparseLayers_eq_physical_firstDifference
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {readLeft readRight : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizesLeft : LocalizedCumulativeTreeRealizes input readLeft leftTree)
    (realizesRight : LocalizedCumulativeTreeRealizes input readRight rightTree)
    (outerRoot : input.Atom)
    (_leftRoot : leftTree.source.occurrence.1.root = outerRoot)
    (_rightRoot : rightTree.source.occurrence.1.root = outerRoot)
    (rule1aTie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree)
      (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree) =
        Ordering.eq)
    (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (LocalizedCumulativeDecoratedTree.table (fun node => node.isotopeMass) leftTree)
        (LocalizedCumulativeDecoratedTree.table (fun node => node.isotopeMass) rightTree) =
          outcome ↔
      DeclarativeCIP.FirstDifferenceOutcome
        (fun position result =>
          DeclarativeCIP.DescendingNatOutcome
            (physicalAtomMassAt singleBonded acyclic leftTree position)
            (physicalAtomMassAt singleBonded acyclic rightTree position)
            result)
        outcome := by
  let leftTable : List (List (OfficialSparseEntry ℕ)) :=
    LocalizedCumulativeDecoratedTree.table (fun node => node.isotopeMass) leftTree
  let rightTable : List (List (OfficialSparseEntry ℕ)) :=
    LocalizedCumulativeDecoratedTree.table (fun node => node.isotopeMass) rightTree
  have leftWellFormed : SparsePhysicalFirstDifference.SparseTableWellFormed leftTable :=
    LocalizedActualTableAddressOrder.table_wellFormed (fun node => node.isotopeMass) leftTree
  have rightWellFormed : SparsePhysicalFirstDifference.SparseTableWellFormed rightTable :=
    LocalizedActualTableAddressOrder.table_wellFormed (fun node => node.isotopeMass) rightTree
  rw [LocalizedActualTableAddressOrder.laterTable_compareSparseLayers_eq_compareLex_of_atomicNumberTie
    singleBonded acyclic realizesLeft realizesRight rule1aTie
    (fun node => node.isotopeMass) (fun node => node.isotopeMass)
    OfficialRuleMajorKey.compareNat]
  have leftFlatten : leftTable.flatten.map Prod.snd =
      (leftTable.flatten.map Prod.fst).map (SparsePhysicalFirstDifference.tableValue leftTable) :=
    flatten_snd_eq_map_tableValue leftWellFormed.depthExact leftWellFormed.increasing
  have rightFlatten : rightTable.flatten.map Prod.snd =
      (rightTable.flatten.map Prod.fst).map (SparsePhysicalFirstDifference.tableValue rightTable) :=
    flatten_snd_eq_map_tableValue rightWellFormed.depthExact rightWellFormed.increasing
  rw [leftFlatten, rightFlatten]
  have align1a : SparseSupportAlignment.SparseAlignment
      (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree)
      (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree) :=
    SparseSupportAlignment.alignment_of_compareSparseLayers_eq
      (LocalizedActualTableAddressOrder.table_wellFormed (fun node => node.atomicNumber) leftTree)
      (LocalizedActualTableAddressOrder.table_wellFormed (fun node => node.atomicNumber) rightTree)
      (LocalizedActualTableAddressOrder.table_atomicNumber_positive_of_realizes
        singleBonded acyclic realizesLeft)
      (LocalizedActualTableAddressOrder.table_atomicNumber_positive_of_realizes
        singleBonded acyclic realizesRight)
      rule1aTie
  have sameAddresses : leftTable.flatten.map Prod.fst = rightTable.flatten.map Prod.fst :=
    (SparseSupportAlignment.SparseAlignment.ofSameAddressRows align1a
      (LocalizedActualTableAddressOrder.SameAddressRows_table
        (fun node => node.isotopeMass) (fun node => node.atomicNumber) leftTree)
      (LocalizedActualTableAddressOrder.SameAddressRows_table
        (fun node => node.isotopeMass) (fun node => node.atomicNumber) rightTree)).sameAddresses
  rw [← sameAddresses]
  refine (DeclarativeCIP.compareLex_map_iff_firstDifference
    OfficialRuleMajorKey.compareNat
    (fun position => SparsePhysicalFirstDifference.tableValue leftTable position)
    (fun position => SparsePhysicalFirstDifference.tableValue rightTable position)
    (leftTable.flatten.map Prod.fst)
    (flatten_addresses_pairwise leftWellFormed.depthExact leftWellFormed.increasing)
    ?outside outcome).trans ?congr
  · intro position absent
    have leftZero : SparsePhysicalFirstDifference.tableValue leftTable position = 0 :=
      SparsePhysicalFirstDifference.tableValue_eq_zero_of_absent leftTable position (by
        intro depth entry present same
        exact absent (by simpa [same] using mem_flatten_map_fst_of_getD present))
    have rightAbsent : position ∉ rightTable.flatten.map Prod.fst := by
      rw [← sameAddresses]
      exact absent
    have rightZero : SparsePhysicalFirstDifference.tableValue rightTable position = 0 :=
      SparsePhysicalFirstDifference.tableValue_eq_zero_of_absent rightTable position (by
        intro depth entry present same
        exact rightAbsent (by simpa [same] using mem_flatten_map_fst_of_getD present))
    change OfficialRuleMajorKey.compareNat
      (SparsePhysicalFirstDifference.tableValue leftTable position)
      (SparsePhysicalFirstDifference.tableValue rightTable position) = Ordering.eq
    rw [leftZero, rightZero]
    exact SparsePhysicalFirstDifference.compareNat_zero_zero
  · apply DeclarativeCIP.FirstDifferenceOutcome.congr
    intro position result
    rw [physicalAtomMassAt_eq_tableValue_isotopeMass singleBonded acyclic
        realizesLeft position,
      physicalAtomMassAt_eq_tableValue_isotopeMass singleBonded acyclic
        realizesRight position]
    exact OfficialRuleMajorKey.compareNat_eq_iff_descendingNatOutcome
      (SparsePhysicalFirstDifference.tableValue leftTable position)
      (SparsePhysicalFirstDifference.tableValue rightTable position) result

/-! ## E. Runtime algebra of the rule-major comparator -/

private theorem compare_constitutional_eq_iff_columns {V : Type*}
    (left right : OfficialRuleMajorKey V) :
    OfficialRuleMajorKey.compare left right = Ordering.eq ↔
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          left.rule1a right.rule1a = Ordering.eq ∧
        OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
          left.rule1b right.rule1b = Ordering.eq ∧
          OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            left.rule2 right.rule2 = Ordering.eq := by
  unfold OfficialRuleMajorKey.compare compareLex
  simp only [Ordering.byKey, Ordering.then_eq_eq]

private theorem compare_constitutional_lt_iff_columns {V : Type*}
    (left right : OfficialRuleMajorKey V) :
    OfficialRuleMajorKey.compare left right = Ordering.lt ↔
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          left.rule1a right.rule1a = Ordering.lt ∨
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          left.rule1a right.rule1a = Ordering.eq ∧
          OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
            left.rule1b right.rule1b = Ordering.lt) ∨
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          left.rule1a right.rule1a = Ordering.eq ∧
          OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
            left.rule1b right.rule1b = Ordering.eq ∧
          OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            left.rule2 right.rule2 = Ordering.lt) := by
  unfold OfficialRuleMajorKey.compare compareLex
  simp only [Ordering.byKey]
  rw [Ordering.then_eq_lt, Ordering.then_eq_lt]
  tauto

private theorem compare_constitutional_gt_iff_columns {V : Type*}
    (left right : OfficialRuleMajorKey V) :
    OfficialRuleMajorKey.compare left right = Ordering.gt ↔
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          left.rule1a right.rule1a = Ordering.gt ∨
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          left.rule1a right.rule1a = Ordering.eq ∧
          OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
            left.rule1b right.rule1b = Ordering.gt) ∨
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          left.rule1a right.rule1a = Ordering.eq ∧
          OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
            left.rule1b right.rule1b = Ordering.eq ∧
          OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            left.rule2 right.rule2 = Ordering.gt) := by
  unfold OfficialRuleMajorKey.compare compareLex
  simp only [Ordering.byKey]
  rw [Ordering.then_eq_gt, Ordering.then_eq_gt]
  tauto

/-! ## F. The independent physical rule-major outcome -/

/-- The constitutional-comparator-visible record built from a realized tree: the three compiled
observation tables, with the source-node column and completeness flag passed through. -/
def constitutionalTablesKey
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (sourceNodes : List (List (OfficialSparseEntry (OfficialCIPNode input.Atom))))
    (complete : Bool)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    OfficialRuleMajorKey input.Atom where
  rule1a := LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) tree
  rule1b := LocalizedCumulativeDecoratedTree.table (fun node => node.rule1bDistance) tree
  rule2 := LocalizedCumulativeDecoratedTree.table (fun node => node.isotopeMass) tree
  sourceNodes := sourceNodes
  complete := complete

/-- **The independent physical rule-major outcome.**

For the fixed original `outerRoot`, one relational outcome summarizes the three constitutional
rules in normative order:

* equality: the physical Rule-1a, Rule-1b, and Rule-2 first differences all tie;
* strictness: either the physical Rule-1a first difference is strict, or Rule 1a ties and the
  physical Rule-1b first difference is strict, or Rule 1a and Rule 1b tie and the physical Rule-2
  first difference is strict.

The branches inspect the independent semantic ties, never the runtime key. -/
noncomputable def physicalRuleMajorOutcome
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (outerRoot : input.Atom)
    (leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (outcome : Ordering) : Prop :=
  match outcome with
  | Ordering.eq =>
      DeclarativeCIP.FirstDifferenceOutcome
        (fun position result =>
          DeclarativeCIP.DescendingNatOutcome
            (physicalAtomicNumberAt singleBonded acyclic leftTree position)
            (physicalAtomicNumberAt singleBonded acyclic rightTree position)
            result)
        Ordering.eq ∧
        DeclarativeCIP.FirstDifferenceOutcome
          (fun position result =>
            DeclarativeCIP.Rule1bDistanceOutcome
              (physicalOuterRootDistanceAt singleBonded acyclic outerRoot leftTree position)
              (physicalOuterRootDistanceAt singleBonded acyclic outerRoot rightTree position)
              result)
          Ordering.eq ∧
          DeclarativeCIP.FirstDifferenceOutcome
            (fun position result =>
              DeclarativeCIP.DescendingNatOutcome
                (physicalAtomMassAt singleBonded acyclic leftTree position)
                (physicalAtomMassAt singleBonded acyclic rightTree position)
                result)
            Ordering.eq
  | Ordering.lt =>
      DeclarativeCIP.FirstDifferenceOutcome
        (fun position result =>
          DeclarativeCIP.DescendingNatOutcome
            (physicalAtomicNumberAt singleBonded acyclic leftTree position)
            (physicalAtomicNumberAt singleBonded acyclic rightTree position)
            result)
        Ordering.lt ∨
        (DeclarativeCIP.FirstDifferenceOutcome
          (fun position result =>
            DeclarativeCIP.DescendingNatOutcome
              (physicalAtomicNumberAt singleBonded acyclic leftTree position)
              (physicalAtomicNumberAt singleBonded acyclic rightTree position)
              result)
          Ordering.eq ∧
          DeclarativeCIP.FirstDifferenceOutcome
            (fun position result =>
              DeclarativeCIP.Rule1bDistanceOutcome
                (physicalOuterRootDistanceAt singleBonded acyclic outerRoot leftTree position)
                (physicalOuterRootDistanceAt singleBonded acyclic outerRoot rightTree position)
                result)
            Ordering.lt) ∨
          (DeclarativeCIP.FirstDifferenceOutcome
            (fun position result =>
              DeclarativeCIP.DescendingNatOutcome
                (physicalAtomicNumberAt singleBonded acyclic leftTree position)
                (physicalAtomicNumberAt singleBonded acyclic rightTree position)
                result)
            Ordering.eq ∧
            DeclarativeCIP.FirstDifferenceOutcome
              (fun position result =>
                DeclarativeCIP.Rule1bDistanceOutcome
                  (physicalOuterRootDistanceAt singleBonded acyclic outerRoot leftTree position)
                  (physicalOuterRootDistanceAt singleBonded acyclic outerRoot rightTree position)
                  result)
              Ordering.eq ∧
              DeclarativeCIP.FirstDifferenceOutcome
                (fun position result =>
                  DeclarativeCIP.DescendingNatOutcome
                    (physicalAtomMassAt singleBonded acyclic leftTree position)
                    (physicalAtomMassAt singleBonded acyclic rightTree position)
                    result)
                Ordering.lt)
  | Ordering.gt =>
      DeclarativeCIP.FirstDifferenceOutcome
        (fun position result =>
          DeclarativeCIP.DescendingNatOutcome
            (physicalAtomicNumberAt singleBonded acyclic leftTree position)
            (physicalAtomicNumberAt singleBonded acyclic rightTree position)
            result)
        Ordering.gt ∨
        (DeclarativeCIP.FirstDifferenceOutcome
          (fun position result =>
            DeclarativeCIP.DescendingNatOutcome
              (physicalAtomicNumberAt singleBonded acyclic leftTree position)
              (physicalAtomicNumberAt singleBonded acyclic rightTree position)
              result)
          Ordering.eq ∧
          DeclarativeCIP.FirstDifferenceOutcome
            (fun position result =>
              DeclarativeCIP.Rule1bDistanceOutcome
                (physicalOuterRootDistanceAt singleBonded acyclic outerRoot leftTree position)
                (physicalOuterRootDistanceAt singleBonded acyclic outerRoot rightTree position)
                result)
            Ordering.gt) ∨
          (DeclarativeCIP.FirstDifferenceOutcome
            (fun position result =>
              DeclarativeCIP.DescendingNatOutcome
                (physicalAtomicNumberAt singleBonded acyclic leftTree position)
                (physicalAtomicNumberAt singleBonded acyclic rightTree position)
                result)
            Ordering.eq ∧
            DeclarativeCIP.FirstDifferenceOutcome
              (fun position result =>
                DeclarativeCIP.Rule1bDistanceOutcome
                  (physicalOuterRootDistanceAt singleBonded acyclic outerRoot leftTree position)
                  (physicalOuterRootDistanceAt singleBonded acyclic outerRoot rightTree position)
                  result)
              Ordering.eq ∧
              DeclarativeCIP.FirstDifferenceOutcome
                (fun position result =>
                  DeclarativeCIP.DescendingNatOutcome
                    (physicalAtomMassAt singleBonded acyclic leftTree position)
                    (physicalAtomMassAt singleBonded acyclic rightTree position)
                    result)
                Ordering.gt)

/-- **Tree-table level: the executed rule-major comparator realizes the physical outcome.** -/
theorem compare_tables_eq_iff_physicalRuleMajorOutcome
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {readLeft readRight : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizesLeft : LocalizedCumulativeTreeRealizes input readLeft leftTree)
    (realizesRight : LocalizedCumulativeTreeRealizes input readRight rightTree)
    {leftSourceNodes rightSourceNodes :
      List (List (OfficialSparseEntry (OfficialCIPNode input.Atom)))}
    {leftComplete rightComplete : Bool}
    (outerRoot : input.Atom)
    (leftRoot : leftTree.source.occurrence.1.root = outerRoot)
    (rightRoot : rightTree.source.occurrence.1.root = outerRoot)
    (outcome : Ordering) :
    OfficialRuleMajorKey.compare
        (constitutionalTablesKey leftSourceNodes leftComplete leftTree)
        (constitutionalTablesKey rightSourceNodes rightComplete rightTree) = outcome ↔
      physicalRuleMajorOutcome singleBonded acyclic outerRoot leftTree rightTree outcome := by
  cases outcome with
  | eq =>
      rw [compare_constitutional_eq_iff_columns]
      unfold physicalRuleMajorOutcome
      constructor
      · rintro ⟨rule1aEq, rule1bEq, rule2Eq⟩
        refine ⟨?_, ?_, ?_⟩
        · exact (table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
            singleBonded acyclic realizesLeft realizesRight Ordering.eq).mp rule1aEq
        · exact (table_rule1b_compareSparseLayers_eq_physical_firstDifference
            singleBonded acyclic realizesLeft realizesRight outerRoot leftRoot rightRoot
            rule1aEq Ordering.eq).mp rule1bEq
        · exact (table_rule2_compareSparseLayers_eq_physical_firstDifference
            singleBonded acyclic realizesLeft realizesRight outerRoot leftRoot rightRoot
            rule1aEq Ordering.eq).mp rule2Eq
      · rintro ⟨rule1aEq, rule1bEq, rule2Eq⟩
        refine ⟨?_, ?_, ?_⟩
        · exact (table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
            singleBonded acyclic realizesLeft realizesRight Ordering.eq).mpr rule1aEq
        · exact (table_rule1b_compareSparseLayers_eq_physical_firstDifference
            singleBonded acyclic realizesLeft realizesRight outerRoot leftRoot rightRoot
            ((table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight Ordering.eq).mpr rule1aEq)
            Ordering.eq).mpr rule1bEq
        · exact (table_rule2_compareSparseLayers_eq_physical_firstDifference
            singleBonded acyclic realizesLeft realizesRight outerRoot leftRoot rightRoot
            ((table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight Ordering.eq).mpr rule1aEq)
            Ordering.eq).mpr rule2Eq
  | lt =>
      rw [compare_constitutional_lt_iff_columns]
      unfold physicalRuleMajorOutcome
      constructor
      · rintro (rule1aLt | ⟨rule1aEq, rule1bLt⟩ | ⟨rule1aEq, rule1bEq, rule2Lt⟩)
        · exact Or.inl ((table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
            singleBonded acyclic realizesLeft realizesRight Ordering.lt).mp rule1aLt)
        · refine Or.inr (Or.inl ⟨?_, ?_⟩)
          · exact (table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight Ordering.eq).mp rule1aEq
          · exact (table_rule1b_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight outerRoot leftRoot rightRoot
              rule1aEq Ordering.lt).mp rule1bLt
        · refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
          · exact (table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight Ordering.eq).mp rule1aEq
          · exact (table_rule1b_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight outerRoot leftRoot rightRoot
              rule1aEq Ordering.eq).mp rule1bEq
          · exact (table_rule2_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight outerRoot leftRoot rightRoot
              rule1aEq Ordering.lt).mp rule2Lt
      · rintro (rule1aLt | ⟨rule1aEq, rule1bLt⟩ | ⟨rule1aEq, rule1bEq, rule2Lt⟩)
        · exact Or.inl ((table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
            singleBonded acyclic realizesLeft realizesRight Ordering.lt).mpr rule1aLt)
        · refine Or.inr (Or.inl ⟨?_, ?_⟩)
          · exact (table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight Ordering.eq).mpr rule1aEq
          · exact (table_rule1b_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight outerRoot leftRoot rightRoot
              ((table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
                singleBonded acyclic realizesLeft realizesRight Ordering.eq).mpr rule1aEq)
              Ordering.lt).mpr rule1bLt
        · refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
          · exact (table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight Ordering.eq).mpr rule1aEq
          · exact (table_rule1b_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight outerRoot leftRoot rightRoot
              ((table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
                singleBonded acyclic realizesLeft realizesRight Ordering.eq).mpr rule1aEq)
              Ordering.eq).mpr rule1bEq
          · exact (table_rule2_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight outerRoot leftRoot rightRoot
              ((table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
                singleBonded acyclic realizesLeft realizesRight Ordering.eq).mpr rule1aEq)
              Ordering.lt).mpr rule2Lt
  | gt =>
      rw [compare_constitutional_gt_iff_columns]
      unfold physicalRuleMajorOutcome
      constructor
      · rintro (rule1aGt | ⟨rule1aEq, rule1bGt⟩ | ⟨rule1aEq, rule1bEq, rule2Gt⟩)
        · exact Or.inl ((table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
            singleBonded acyclic realizesLeft realizesRight Ordering.gt).mp rule1aGt)
        · refine Or.inr (Or.inl ⟨?_, ?_⟩)
          · exact (table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight Ordering.eq).mp rule1aEq
          · exact (table_rule1b_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight outerRoot leftRoot rightRoot
              rule1aEq Ordering.gt).mp rule1bGt
        · refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
          · exact (table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight Ordering.eq).mp rule1aEq
          · exact (table_rule1b_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight outerRoot leftRoot rightRoot
              rule1aEq Ordering.eq).mp rule1bEq
          · exact (table_rule2_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight outerRoot leftRoot rightRoot
              rule1aEq Ordering.gt).mp rule2Gt
      · rintro (rule1aGt | ⟨rule1aEq, rule1bGt⟩ | ⟨rule1aEq, rule1bEq, rule2Gt⟩)
        · exact Or.inl ((table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
            singleBonded acyclic realizesLeft realizesRight Ordering.gt).mpr rule1aGt)
        · refine Or.inr (Or.inl ⟨?_, ?_⟩)
          · exact (table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight Ordering.eq).mpr rule1aEq
          · exact (table_rule1b_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight outerRoot leftRoot rightRoot
              ((table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
                singleBonded acyclic realizesLeft realizesRight Ordering.eq).mpr rule1aEq)
              Ordering.gt).mpr rule1bGt
        · refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
          · exact (table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight Ordering.eq).mpr rule1aEq
          · exact (table_rule1b_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight outerRoot leftRoot rightRoot
              ((table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
                singleBonded acyclic realizesLeft realizesRight Ordering.eq).mpr rule1aEq)
              Ordering.eq).mpr rule1bEq
          · exact (table_rule2_compareSparseLayers_eq_physical_firstDifference
              singleBonded acyclic realizesLeft realizesRight outerRoot leftRoot rightRoot
              ((table_atomicNumber_compareSparseLayers_eq_physical_firstDifference
                singleBonded acyclic realizesLeft realizesRight Ordering.eq).mpr rule1aEq)
              Ordering.gt).mpr rule2Gt

/-- **Key level: the actual built constitutional key realizes the physical outcome.**  For two
actual full/table matches and realized trees at the same original root, the executed
`OfficialRuleMajorKey.compare` of the actual constitutional keys is equivalent, at every
`Ordering`, to the independent physical rule-major outcome of the two trees. -/
theorem compare_eq_iff_physicalRuleMajorOutcome
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {stage : LocalizedCumulativeRule45Stage}
    {readLeft readRight : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftMatch : LocalizedCumulativeTreeTableMatch stage leftTree leftKey)
    (rightMatch : LocalizedCumulativeTreeTableMatch stage rightTree rightKey)
    (realizesLeft : LocalizedCumulativeTreeRealizes input readLeft leftTree)
    (realizesRight : LocalizedCumulativeTreeRealizes input readRight rightTree)
    (outerRoot : input.Atom)
    (leftRoot : leftTree.source.occurrence.1.root = outerRoot)
    (rightRoot : rightTree.source.occurrence.1.root = outerRoot)
    (outcome : Ordering) :
    OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional = outcome ↔
      physicalRuleMajorOutcome singleBonded acyclic outerRoot leftTree rightTree outcome := by
  have leftRule1a : leftKey.constitutional.rule1a =
      LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree :=
    leftMatch.1.symm.trans (LocalizedCumulativeDecoratedTree.tables_rule1a stage leftTree)
  have leftRule1b : leftKey.constitutional.rule1b =
      LocalizedCumulativeDecoratedTree.table (fun node => node.rule1bDistance) leftTree :=
    leftMatch.2.1.symm.trans (LocalizedCumulativeDecoratedTree.tables_rule1b stage leftTree)
  have leftRule2 : leftKey.constitutional.rule2 =
      LocalizedCumulativeDecoratedTree.table (fun node => node.isotopeMass) leftTree :=
    leftMatch.2.2.1.symm.trans (LocalizedCumulativeDecoratedTree.tables_rule2 stage leftTree)
  have rightRule1a : rightKey.constitutional.rule1a =
      LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree :=
    rightMatch.1.symm.trans (LocalizedCumulativeDecoratedTree.tables_rule1a stage rightTree)
  have rightRule1b : rightKey.constitutional.rule1b =
      LocalizedCumulativeDecoratedTree.table (fun node => node.rule1bDistance) rightTree :=
    rightMatch.2.1.symm.trans (LocalizedCumulativeDecoratedTree.tables_rule1b stage rightTree)
  have rightRule2 : rightKey.constitutional.rule2 =
      LocalizedCumulativeDecoratedTree.table (fun node => node.isotopeMass) rightTree :=
    rightMatch.2.2.1.symm.trans (LocalizedCumulativeDecoratedTree.tables_rule2 stage rightTree)
  have leftKeyEq : leftKey.constitutional =
      constitutionalTablesKey leftKey.constitutional.sourceNodes leftKey.constitutional.complete
        leftTree := by
    unfold constitutionalTablesKey
    rw [← leftRule1a, ← leftRule1b, ← leftRule2]
  have rightKeyEq : rightKey.constitutional =
      constitutionalTablesKey rightKey.constitutional.sourceNodes rightKey.constitutional.complete
        rightTree := by
    unfold constitutionalTablesKey
    rw [← rightRule1a, ← rightRule1b, ← rightRule2]
  rw [leftKeyEq, rightKeyEq]
  exact compare_tables_eq_iff_physicalRuleMajorOutcome singleBonded acyclic
    realizesLeft realizesRight outerRoot leftRoot rightRoot outcome

/-! ## G. Physical descending order of the actual sibling lists -/

/-- The left tree is not physically junior to the right tree: it is physically senior or the two
tie physically. -/
noncomputable def physicalRuleMajorNotLt
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (outerRoot : input.Atom) : Prop :=
  physicalRuleMajorOutcome singleBonded acyclic outerRoot leftTree rightTree Ordering.gt ∨
    physicalRuleMajorOutcome singleBonded acyclic outerRoot leftTree rightTree Ordering.eq

/-- A non-junior executed comparison realizes the physical non-junior outcome. -/
theorem physicalRuleMajorNotLt_of_compare_not_lt
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {stage : LocalizedCumulativeRule45Stage}
    {readLeft readRight : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftMatch : LocalizedCumulativeTreeTableMatch stage leftTree leftKey)
    (rightMatch : LocalizedCumulativeTreeTableMatch stage rightTree rightKey)
    (realizesLeft : LocalizedCumulativeTreeRealizes input readLeft leftTree)
    (realizesRight : LocalizedCumulativeTreeRealizes input readRight rightTree)
    (outerRoot : input.Atom)
    (leftRoot : leftTree.source.occurrence.1.root = outerRoot)
    (rightRoot : rightTree.source.occurrence.1.root = outerRoot)
    (notLt : OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional ≠
      Ordering.lt) :
    physicalRuleMajorNotLt singleBonded acyclic leftTree rightTree outerRoot := by
  unfold physicalRuleMajorNotLt
  cases compared : OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional with
  | lt => exact absurd compared notLt
  | eq => exact Or.inr ((compare_eq_iff_physicalRuleMajorOutcome singleBonded acyclic
      leftMatch rightMatch realizesLeft realizesRight outerRoot leftRoot rightRoot
      Ordering.eq).mp compared)
  | gt => exact Or.inl ((compare_eq_iff_physicalRuleMajorOutcome singleBonded acyclic
      leftMatch rightMatch realizesLeft realizesRight outerRoot leftRoot rightRoot
      Ordering.gt).mp compared)

/-- Every right member of a `Forall₂` pairing is paired with some left member. -/
private theorem exists_of_mem_right_forall₂ {α β : Type*} {r : α → β → Prop}
    {left : List α} {right : List β} (paired : List.Forall₂ r left right) :
    ∀ b ∈ right, ∃ a ∈ left, r a b := by
  induction paired with
  | nil => intro b present; cases present
  | cons head tail ih =>
      intro b present
      rcases List.mem_cons.mp present with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨a, aMem, related⟩ := ih b later
        exact ⟨a, List.mem_cons_of_mem _ aMem, related⟩

/-- Translate a pairwise key property through a `Forall₂` pairing of keys with trees. -/
private theorem pairwise_of_forall₂_of_pairwise {α β : Type*}
    {keyNotLt : α → α → Prop} {physical : β → β → Prop}
    {sound : α → β → Prop} :
    ∀ {keys : List α} {trees : List β},
      List.Forall₂ sound keys trees →
        keys.Pairwise keyNotLt →
          (∀ {leftKey rightKey : α} {leftTree rightTree : β},
            keyNotLt leftKey rightKey → sound leftKey leftTree → sound rightKey rightTree →
              leftTree ∈ trees → rightTree ∈ trees → physical leftTree rightTree) →
          trees.Pairwise physical
  | [], [], .nil, _, _ => by simp
  | headKeys :: tailKeys, headTree :: tailTrees, .cons headSound tailPaired, ordered, translate => by
      have orderParts := List.pairwise_cons.mp ordered
      rw [List.pairwise_cons]
      constructor
      · intro rightTree rightPresent
        obtain ⟨rightKey, rightKeyPresent, rightSound⟩ :=
          exists_of_mem_right_forall₂ tailPaired rightTree rightPresent
        exact translate (orderParts.1 rightKey rightKeyPresent) headSound rightSound
          (by simp) (List.mem_cons_of_mem headTree rightPresent)
      · exact pairwise_of_forall₂_of_pairwise tailPaired orderParts.2 (by
          intro leftKey rightKey leftTree rightTree notLt soundLeft soundRight
            leftPresent rightPresent
          exact translate notLt soundLeft soundRight
            (List.mem_cons_of_mem headTree leftPresent)
            (List.mem_cons_of_mem headTree rightPresent))

/-- **Recursive physical sibling descending order.**

Every actual sibling list is descending for the physical rule-major outcome: each pair of actual
sibling trees is not physically junior left-to-right, every sibling keeps the original outer root,
and the property recurses into every child.  (The root-preservation and the recursive fields are
kept separate so the kernel accepts the strictly-positive nested construction.) -/
inductive PhysicalSiblingDescending
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (outerRoot : input.Atom) :
    LocalizedCumulativeDecoratedTree input carrierFuel → Prop where
  | mk (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
      (siblings : tree.children.Pairwise fun left right =>
        physicalRuleMajorNotLt singleBonded acyclic left right outerRoot)
      (childrenRoot : ∀ child ∈ tree.children,
        child.source.occurrence.1.root = outerRoot)
      (children : ∀ child ∈ tree.children,
        PhysicalSiblingDescending singleBonded acyclic outerRoot child) :
      PhysicalSiblingDescending singleBonded acyclic outerRoot tree







theorem physicalSiblingDescending_of_trace
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (outerRoot : input.Atom) :
    ∀ (fuel : Nat) (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      tree.source.occurrence.1.root = outerRoot →
        LocalizedActualRecursiveSortTrace input stage read fuel tree key →
          PhysicalSiblingDescending singleBonded acyclic outerRoot tree := by
  intro fuel
  induction fuel with
  | zero =>
      intro tree key rootEq trace
      cases trace with
      | terminal _ cursor children childrenComputed terminalChildren fullMatch realizes =>
          constructor
          · simp [localizedRootTree]
          · intro child present
            simp [localizedRootTree] at present
          · intro child present
            simp [localizedRootTree] at present
  | succ fuel ih =>
      intro tree key rootEq trace
      cases trace with
      | terminal _ cursor children childrenComputed terminalChildren fullMatch realizes =>
          constructor
          · simp [localizedRootTree]
          · intro child present
            simp [localizedRootTree] at present
          · intro child present
            simp [localizedRootTree] at present
      | node fuel cursor children childKeys sortedKeys sortedTrees childrenComputed nonempty
          childKeysComputed sortedEq constitutionalDescending fullMatch realizes childrenTraced =>
          have orderedOnKeys : sortedKeys.Pairwise fun left right =>
              OfficialRuleMajorKey.compare left.constitutional right.constitutional ≠
                Ordering.lt :=
            List.pairwise_map.mp constitutionalDescending
          have paired := LocalizedActualRecursiveSortTraceList.to_forall₂ childrenTraced
          constructor
          · refine pairwise_of_forall₂_of_pairwise paired orderedOnKeys ?_
            intro leftKey rightKey leftTree rightTree notLt soundLeft soundRight
              leftPresent rightPresent
            have leftMatch :=
              (LocalizedActualRecursiveSortTrace.fullMatch_of_trace soundLeft).tableMatch
            have rightMatch :=
              (LocalizedActualRecursiveSortTrace.fullMatch_of_trace soundRight).tableMatch
            have realizesLeft := LocalizedActualRecursiveSortTrace.realizes_of_trace soundLeft
            have realizesRight := LocalizedActualRecursiveSortTrace.realizes_of_trace soundRight
            have leftRootEq : leftTree.source.occurrence.1.root = outerRoot := by
              obtain ⟨slot, lookup⟩ := List.mem_iff_getElem?.mp leftPresent
              rw [child_root_of_child realizes (by simpa using lookup)]
              exact rootEq
            have rightRootEq : rightTree.source.occurrence.1.root = outerRoot := by
              obtain ⟨slot, lookup⟩ := List.mem_iff_getElem?.mp rightPresent
              rw [child_root_of_child realizes (by simpa using lookup)]
              exact rootEq
            exact physicalRuleMajorNotLt_of_compare_not_lt singleBonded acyclic
              leftMatch rightMatch realizesLeft realizesRight outerRoot leftRootEq rightRootEq notLt
          · intro child present
            obtain ⟨slot, lookup⟩ := List.mem_iff_getElem?.mp present
            rw [child_root_of_child realizes (by simpa using lookup)]
            exact rootEq
          · intro child present
            obtain ⟨key, _, sound⟩ := exists_of_mem_right_forall₂ paired child present
            have childRoot : child.source.occurrence.1.root = outerRoot := by
              obtain ⟨slot, lookup⟩ := List.mem_iff_getElem?.mp present
              rw [child_root_of_child realizes (by simpa using lookup)]
              exact rootEq
            exact ih child key childRoot sound

/-! ## H. Adequate-budget actual production -/









theorem production_constitutional_physical_fidelity
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (outerRoot : input.Atom)
    (rootEq : cursor.occurrence.1.root = outerRoot) :
    ∃ (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      tree.source = cursor ∧
        tree.source.occurrence.1.root = outerRoot ∧
          LocalizedCumulativeTreeFullMatch stage tree key ∧
            LocalizedCumulativeTreeRealizes input
              (fun occurrence => input.localizedDependencyLabel target view occurrence) tree ∧
              PhysicalSiblingDescending singleBonded acyclic outerRoot tree ∧
                (∀ (other : LocalizedCumulativeDecoratedTree input carrierFuel)
                  (otherKey : input.LocalizedRerootCumulativeRule45Key),
                  LocalizedCumulativeTreeTableMatch stage other otherKey →
                    LocalizedCumulativeTreeRealizes input
                      (fun occurrence => input.localizedDependencyLabel target view occurrence) other →
                      other.source.occurrence.1.root = outerRoot →
                        ∀ outcome,
                          OfficialRuleMajorKey.compare key.constitutional otherKey.constitutional =
                              outcome ↔
                            physicalRuleMajorOutcome singleBonded acyclic outerRoot
                              tree other outcome) := by
  obtain ⟨tree, key, source, fullMatch, realizes, trace⟩ :=
    exists_trace_of_build_at_twice input stage target view cursor valid
  refine ⟨tree, key, source, ?_, fullMatch, realizes, ?_, ?_⟩
  · simpa [source] using rootEq
  · exact physicalSiblingDescending_of_trace singleBonded acyclic outerRoot
      (2 * (carrierFuel + 1)) tree key (by simpa [source] using rootEq) trace
  · intro other otherKey otherMatch otherRealizes otherRoot outcome
    exact compare_eq_iff_physicalRuleMajorOutcome singleBonded acyclic
      fullMatch.tableMatch otherMatch realizes otherRealizes outerRoot
      (by simpa [source] using rootEq) otherRoot outcome

/-- **Actual production constitutional physical comparison.**

At two actual valid cursors sharing the same original root `outerRoot`, both adequate-budget
actual production builds succeed and expose actual production keys and actual realized trees
(sources equal to the cursors, roots equal to `outerRoot`), the recursive physical sibling
descending order of both trees, and the equivalence between the executed constitutional comparison
of the two actual keys and the independent physical rule-major outcome, at every `Ordering`. -/
theorem production_constitutional_physical_comparison
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftValid : input.LocalizedRerootCursorValid leftCursor)
    (rightValid : input.LocalizedRerootCursorValid rightCursor)
    (outerRoot : input.Atom)
    (leftRootEq : leftCursor.occurrence.1.root = outerRoot)
    (rightRootEq : rightCursor.occurrence.1.root = outerRoot) :
    ∃ (leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel)
      (leftKey rightKey : input.LocalizedRerootCumulativeRule45Key),
      leftTree.source = leftCursor ∧
        rightTree.source = rightCursor ∧
          leftTree.source.occurrence.1.root = outerRoot ∧
            rightTree.source.occurrence.1.root = outerRoot ∧
              LocalizedCumulativeTreeFullMatch stage leftTree leftKey ∧
                LocalizedCumulativeTreeFullMatch stage rightTree rightKey ∧
                  LocalizedCumulativeTreeRealizes input
                    (fun occurrence => input.localizedDependencyLabel target view occurrence) leftTree ∧
                    LocalizedCumulativeTreeRealizes input
                      (fun occurrence => input.localizedDependencyLabel target view occurrence) rightTree ∧
                      PhysicalSiblingDescending singleBonded acyclic outerRoot leftTree ∧
                        PhysicalSiblingDescending singleBonded acyclic outerRoot rightTree ∧
                          ∀ outcome,
                            OfficialRuleMajorKey.compare leftKey.constitutional
                                rightKey.constitutional = outcome ↔
                              physicalRuleMajorOutcome singleBonded acyclic outerRoot
                                leftTree rightTree outcome := by
  obtain ⟨leftTree, leftKey, leftSource, leftTreeRoot, leftFullMatch, leftRealizes,
    leftDescending, _⟩ :=
    production_constitutional_physical_fidelity singleBonded acyclic stage target view
      leftCursor leftValid outerRoot leftRootEq
  obtain ⟨rightTree, rightKey, rightSource, rightTreeRoot, rightFullMatch, rightRealizes,
    rightDescending, _⟩ :=
    production_constitutional_physical_fidelity singleBonded acyclic stage target view
      rightCursor rightValid outerRoot rightRootEq
  refine ⟨leftTree, rightTree, leftKey, rightKey, leftSource, rightSource, leftTreeRoot,
    rightTreeRoot, leftFullMatch, rightFullMatch, leftRealizes, rightRealizes,
    leftDescending, rightDescending, ?_⟩
  · intro outcome
    exact compare_eq_iff_physicalRuleMajorOutcome singleBonded acyclic
      leftFullMatch.tableMatch rightFullMatch.tableMatch leftRealizes rightRealizes outerRoot
      leftTreeRoot rightTreeRoot outcome

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.physicalOuterRootDistanceAt
assert_kernel_only TetraStereo.OneCenter.physicalAtomMassAt
assert_kernel_only TetraStereo.OneCenter.physicalOuterRootDistanceAt_eq_tableValue_rule1bDistance
assert_kernel_only TetraStereo.OneCenter.physicalAtomMassAt_eq_tableValue_isotopeMass
assert_kernel_only TetraStereo.OneCenter.table_rule1b_compareSparseLayers_eq_physical_firstDifference
assert_kernel_only TetraStereo.OneCenter.table_rule2_compareSparseLayers_eq_physical_firstDifference
assert_kernel_only TetraStereo.OneCenter.constitutionalTablesKey
assert_kernel_only TetraStereo.OneCenter.physicalRuleMajorOutcome
assert_kernel_only TetraStereo.OneCenter.compare_tables_eq_iff_physicalRuleMajorOutcome
assert_kernel_only TetraStereo.OneCenter.compare_eq_iff_physicalRuleMajorOutcome
assert_kernel_only TetraStereo.OneCenter.physicalRuleMajorNotLt
assert_kernel_only TetraStereo.OneCenter.physicalRuleMajorNotLt_of_compare_not_lt
assert_kernel_only TetraStereo.OneCenter.PhysicalSiblingDescending
assert_kernel_only TetraStereo.OneCenter.physicalSiblingDescending_of_trace
assert_kernel_only TetraStereo.OneCenter.production_constitutional_physical_fidelity
assert_kernel_only TetraStereo.OneCenter.production_constitutional_physical_comparison
