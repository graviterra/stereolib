import TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000






namespace TetraStereo.UniversalProof.NextFrontier.ParsedParityThreeLeafProjection

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering

private theorem exceptList_pointwise {source : AuthoritativeChemicalInput}
    {carrierFuel ruleFuel : Nat} {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
      excluded ruleFuel cursors keys) :
    List.Forall₂ (source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept excluded ruleFuel)
      cursors keys :=
  match derived with
  | .nil _ => .nil
  | .cons head tail => .cons head (exceptList_pointwise tail)

private theorem key_head (source : AuthoritativeChemicalInput)
    {carrierFuel ruleFuel : Nat} {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {key : source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept excluded ruleFuel cursor key) :
    key.constitutional.sourceNodes.head? = some [([], cursor.occurrence.1.node)] := by
  cases derived <;> rfl

private theorem key_atomicNat (source : AuthoritativeChemicalInput)
    {carrierFuel ruleFuel : Nat} {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {key : source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept excluded ruleFuel cursor key) :
    keyAtomicNat source key =
      (source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        cursor.occurrence.1.node).numerator := by
  have head := ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head
    source.molecule.toLocalizedMoleculeGraph key.constitutional.sourceNodes cursor.occurrence.1.node
    (key_head source derived)
  simp [keyAtomicNat, head]

private theorem key_nodes_of_terminal (source : AuthoritativeChemicalInput)
    {carrierFuel ruleFuel : Nat} {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {key : source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept excluded ruleFuel cursor key)
    (terminal : source.aromaticCanonicalRerootChildren cursor = []) :
    key.constitutional.sourceNodes = [[([], cursor.occurrence.1.node)]] := by
  cases derived with
  | zeroLeaf => rfl
  | successorLeaf => rfl
  | successorBranch frame nonterminal observed childrenDerived permutation descending =>
      have actual := (source.aromaticCanonicalRerootChildren?_eq_some_iff _ _).mpr frame
      simp only [aromaticCanonicalRerootChildren?, Option.some.injEq] at actual
      exact False.elim (nonterminal (actual.symm.trans terminal))

private theorem exceptList_atomicNats (source : AuthoritativeChemicalInput)
    {carrierFuel ruleFuel : Nat} {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
      excluded ruleFuel cursors keys) :
    keys.map (keyAtomicNat source) = cursors.map (fun cursor =>
      (source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        cursor.occurrence.1.node).numerator) := by
  have pointwise := exceptList_pointwise derived
  clear derived
  induction pointwise with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, key_atomicNat source head, ih]

private theorem exceptList_heads (source : AuthoritativeChemicalInput)
    {carrierFuel ruleFuel : Nat} {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
      excluded ruleFuel cursors keys)
    (natural : ∀ cursor ∈ cursors,
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation cursor.occurrence.1.node =
        .ofNat ((source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
          cursor.occurrence.1.node).numerator)) :
    ∀ key ∈ keys, (ExactOfficialRuleMajorKey.exactRule1aLayers
      source.molecule.toLocalizedMoleculeGraph key.constitutional.sourceNodes).head? =
        some [([], .ofNat (keyAtomicNat source key))] := by
  have pointwise := exceptList_pointwise derived
  clear derived
  revert natural
  induction pointwise with
  | nil => intro natural; simp
  | @cons cursor key cursors keys head tail ih =>
      intro natural selected member
      rcases List.mem_cons.mp member with rfl | retained
      · have projected := ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head
          source.molecule.toLocalizedMoleculeGraph selected.constitutional.sourceNodes cursor.occurrence.1.node
          (key_head source head)
        rw [key_atomicNat source head]
        rw [natural cursor List.mem_cons_self] at projected
        exact projected
      · exact ih (fun cursor member => natural cursor (List.mem_cons_of_mem _ member)) selected retained

private theorem exceptList_terminal_observed {α : Type*} (source : AuthoritativeChemicalInput)
    {carrierFuel ruleFuel : Nat} {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
      excluded ruleFuel cursors keys)
    (terminal : ∀ cursor ∈ cursors, source.aromaticCanonicalRerootChildren cursor = [])
    (observe : OfficialCIPNode source.AromaticCanonicalAtom → α) (byAtomic : Nat → α)
    (observed : ∀ cursor ∈ cursors, observe cursor.occurrence.1.node =
      byAtomic ((source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        cursor.occurrence.1.node).numerator)) :
    ∀ key ∈ keys, ∃ node, key.constitutional.sourceNodes = [[([], node)]] ∧
      observe node = byAtomic (keyAtomicNat source key) := by
  have pointwise := exceptList_pointwise derived
  clear derived
  revert terminal observed
  induction pointwise with
  | nil => intro terminal observed; simp
  | @cons cursor key cursors keys head tail ih =>
      intro terminal observed selected member
      rcases List.mem_cons.mp member with rfl | retained
      · refine ⟨cursor.occurrence.1.node,
          key_nodes_of_terminal source head (terminal cursor List.mem_cons_self), ?_⟩
        rw [key_atomicNat source head]
        exact observed cursor List.mem_cons_self
      · exact ih (fun cursor member => terminal cursor (List.mem_cons_of_mem _ member))
          (fun cursor member => observed cursor (List.mem_cons_of_mem _ member)) selected retained

/-- Every observation is projected through the actual key's actual sorted terminal children.
The correspondence with atomic number is a local physical observation premise; a family
wrapper must derive it, the branch, terminality, and physical child multiset independently. -/
theorem source_three_leaf_observed_projection {α : Type*} (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (cursor : source.AromaticCanonicalRerootCursor 1)
    (present : cursor ∈ finalOccurrenceRoots source 1 center)
    (real : cursor.occurrence.1.node.provenance = .realAtom)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) (ruleFuel : Nat)
    (branch : SourceKeyBranch source excluded ruleFuel cursor key)
    (z0 z1 z2 : Nat)
    (observations : ((source.aromaticCanonicalRerootChildren cursor).map (fun child =>
      (source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        child.occurrence.1.node).numerator)).Perm [z0, z1, z2])
    (natural : ∀ child ∈ source.aromaticCanonicalRerootChildren cursor,
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation child.occurrence.1.node =
        .ofNat ((source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
          child.occurrence.1.node).numerator))
    (orderedNumbers : [z0, z1, z2].Pairwise (fun first second => second ≤ first))
    (observe : OfficialCIPNode source.AromaticCanonicalAtom → α) (byAtomic : Nat → α)
    (observed : ∀ child ∈ source.aromaticCanonicalRerootChildren cursor,
      observe child.occurrence.1.node =
        byAtomic ((source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
          child.occurrence.1.node).numerator)) :
    OfficialRuleMajorKey.mapSourceLayers observe key.constitutional.sourceNodes =
      [[([], observe cursor.occurrence.1.node)],
        [([0], byAtomic z0), ([1], byAtomic z1), ([2], byAtomic z2)]] := by
  obtain ⟨depth, children, rawKeys, sorted, _, frame, _, derived, permutation, descending, assembly⟩ := branch
  have actual : source.aromaticCanonicalRerootChildren cursor = children := by
    have computed := (source.aromaticCanonicalRerootChildren?_eq_some_iff _ _).mpr frame
    simpa only [aromaticCanonicalRerootChildren?, Option.some.injEq] using computed
  have childNatural : ∀ child ∈ children,
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation child.occurrence.1.node =
        .ofNat ((source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
          child.occurrence.1.node).numerator) := by
    intro child member
    exact natural child (by rw [actual]; exact member)
  have childTerminal : ∀ child ∈ children, source.aromaticCanonicalRerootChildren child = [] := by
    intro child member
    exact returned_one_child_terminal source center cursor present real child (by rw [actual]; exact member)
  have rawHeads := exceptList_heads source derived childNatural
  have sortedHeads : ∀ key ∈ sorted,
      (ExactOfficialRuleMajorKey.exactRule1aLayers source.molecule.toLocalizedMoleculeGraph
        key.constitutional.sourceNodes).head? = some [([], .ofNat (keyAtomicNat source key))] := by
    intro selected member
    exact rawHeads selected (permutation.mem_iff.mp member)
  have values := permutation.map (keyAtomicNat source)
  rw [exceptList_atomicNats source derived] at values
  have physical := observations
  rw [actual] at physical
  have sortedValues := descending_keys_atomicNats source sorted sortedHeads descending
  have valueOrder : sorted.map (keyAtomicNat source) = [z0, z1, z2] :=
    List.Perm.eq_of_pairwise (fun _ _ _ _ first second => Nat.le_antisymm second first)
      sortedValues orderedNumbers (values.trans physical)
  have leafNodes := exceptList_terminal_observed source derived childTerminal observe byAtomic
    (fun child member => observed child (by rw [actual]; exact member))
  have sortedNodes : ∀ key ∈ sorted, ∃ node, key.constitutional.sourceNodes = [[([], node)]] ∧
      observe node = byAtomic (keyAtomicNat source key) := by
    intro selected member
    exact leafNodes selected (permutation.mem_iff.mp member)
  have length : sorted.length = 3 := by
    have lengths := congrArg List.length valueOrder
    simpa only [List.length_map, List.length_cons, List.length_nil] using lengths
  obtain ⟨k0, k1, k2, sortedEq⟩ := List.length_eq_three.mp length
  subst sorted
  obtain ⟨n0, s0, o0⟩ := sortedNodes k0 (by simp)
  obtain ⟨n1, s1, o1⟩ := sortedNodes k1 (by simp)
  obtain ⟨n2, s2, o2⟩ := sortedNodes k2 (by simp)
  have v0 : keyAtomicNat source k0 = z0 := by
    simpa using congrArg (fun numbers : List Nat => numbers.getD 0 0) valueOrder
  have v1 : keyAtomicNat source k1 = z1 := by
    simpa using congrArg (fun numbers : List Nat => numbers.getD 1 0) valueOrder
  have v2 : keyAtomicNat source k2 = z2 := by
    simpa using congrArg (fun numbers : List Nat => numbers.getD 2 0) valueOrder
  rw [assembly]
  simp [OfficialRuleMajorKey.mapSourceLayers, OfficialRuleMajorKey.mergeAddressedChildren,
    OfficialRuleMajorKey.addressedChildLayerCount, OfficialRuleMajorKey.prefixLayer,
    OfficialRuleMajorKey.mapObservation, s0, s1, s2, o0, o1, o2, v0, v1, v2, List.range_succ]

end TetraStereo.UniversalProof.NextFrontier.ParsedParityThreeLeafProjection
