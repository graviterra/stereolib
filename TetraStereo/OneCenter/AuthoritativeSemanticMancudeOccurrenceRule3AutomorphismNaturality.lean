import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3SpatialKey
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3CanonicalFrameExact
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceNaturality

set_option autoImplicit false

/-!
# Rule 3 comparator naturality under constitutional relabeling

Comparator-visible official source layers are mapped independently of physical atom identity.
Once Rule-1a and Rule-2 observations are invariant, exact constitutional and uncancelled Rule-3
comparisons follow in one theorem.
-/

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput


def mapAromaticCanonicalAddressedSourceLayers
    {source : AuthoritativeChemicalInput}
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (layers : OfficialRuleMajorKey.AddressedSourceLayers
      source.AromaticCanonicalAtom) :
    OfficialRuleMajorKey.AddressedSourceLayers source.AromaticCanonicalAtom :=
  layers.map fun layer => layer.map fun entry =>
    (entry.1, mapAromaticCanonicalOfficialCIPNode atomPermutation entry.2)

def mapAromaticCanonicalExactOfficialRuleMajorKey
    {source : AuthoritativeChemicalInput}
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (key : ExactOfficialRuleMajorKey source.AromaticCanonicalAtom) :
    ExactOfficialRuleMajorKey source.AromaticCanonicalAtom :=
  { sourceNodes := mapAromaticCanonicalAddressedSourceLayers atomPermutation key.sourceNodes
    complete := key.complete }

theorem mapSourceLayers_mapAromaticCanonicalAddressedSourceLayers
    {source : AuthoritativeChemicalInput}
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    {alpha : Type*}
    (observe : OfficialCIPNode source.AromaticCanonicalAtom → alpha)
    (observeNatural : ∀ node,
      observe (mapAromaticCanonicalOfficialCIPNode atomPermutation node) = observe node)
    (layers : OfficialRuleMajorKey.AddressedSourceLayers
      source.AromaticCanonicalAtom) :
    OfficialRuleMajorKey.mapSourceLayers observe
        (mapAromaticCanonicalAddressedSourceLayers atomPermutation layers) =
      OfficialRuleMajorKey.mapSourceLayers observe layers := by
  simp [OfficialRuleMajorKey.mapSourceLayers,
    OfficialRuleMajorKey.mapObservation,
    mapAromaticCanonicalAddressedSourceLayers, observeNatural]

theorem rule1bRootDistance_mapAromaticCanonicalOfficialCIPNode
    {source : AuthoritativeChemicalInput}
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    (mapAromaticCanonicalOfficialCIPNode atomPermutation node).rule1bRootDistance =
      node.rule1bRootDistance := by
  cases node
  simp [mapAromaticCanonicalOfficialCIPNode, OfficialCIPNode.rule1bRootDistance,
    OfficialCIPNode.depth]

theorem exactOfficialRuleMajorKey_compare_map_natural_of_observations
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (rule1aNatural : ∀ node,
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node) =
        source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation node)
    (rule2Natural : ∀ node,
      (ofLex (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node))).2 =
        (ofLex (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel node)).2)
    (left right : ExactOfficialRuleMajorKey source.AromaticCanonicalAtom) :
    ExactOfficialRuleMajorKey.compare source.molecule.toLocalizedMoleculeGraph
        (mapAromaticCanonicalExactOfficialRuleMajorKey atomPermutation left)
        (mapAromaticCanonicalExactOfficialRuleMajorKey atomPermutation right) =
      ExactOfficialRuleMajorKey.compare source.molecule.toLocalizedMoleculeGraph left right := by
  unfold ExactOfficialRuleMajorKey.compare ExactOfficialRuleMajorKey.compareAddressedSources
    ExactOfficialRuleMajorKey.exactRule1aLayers ExactOfficialRuleMajorKey.rule1bLayers
    ExactOfficialRuleMajorKey.rule2Layers Ordering.byKey
    mapAromaticCanonicalExactOfficialRuleMajorKey compareLex
  dsimp only
  rw [mapSourceLayers_mapAromaticCanonicalAddressedSourceLayers
      atomPermutation
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      rule1aNatural,
    mapSourceLayers_mapAromaticCanonicalAddressedSourceLayers
      atomPermutation OfficialCIPNode.rule1bRootDistance
      (rule1bRootDistance_mapAromaticCanonicalOfficialCIPNode atomPermutation),
    mapSourceLayers_mapAromaticCanonicalAddressedSourceLayers
      atomPermutation
      (fun node => (ofLex
        (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel node)).2)
      rule2Natural,
    mapSourceLayers_mapAromaticCanonicalAddressedSourceLayers
      atomPermutation
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      rule1aNatural,
    mapSourceLayers_mapAromaticCanonicalAddressedSourceLayers
      atomPermutation OfficialCIPNode.rule1bRootDistance
      (rule1bRootDistance_mapAromaticCanonicalOfficialCIPNode atomPermutation),
    mapSourceLayers_mapAromaticCanonicalAddressedSourceLayers
      atomPermutation
      (fun node => (ofLex
        (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel node)).2)
      rule2Natural]

def mapAromaticCanonicalUncancelledRule3SpatialKey
    {source : AuthoritativeChemicalInput}
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.AromaticCanonicalUncancelledRule3SpatialKey :=
  { constitutional :=
      mapAromaticCanonicalExactOfficialRuleMajorKey atomPermutation key.constitutional
    observations := key.observations
    rule3 := key.rule3 }

theorem compareAromaticCanonicalUncancelledRule3SpatialKeys_map_natural_of_observations
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (rule1aNatural : ∀ node,
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node) =
        source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation node)
    (rule2Natural : ∀ node,
      (ofLex (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node))).2 =
        (ofLex (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel node)).2)
    (left right : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation left)
        (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation right) =
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys left right := by
  unfold compareAromaticCanonicalUncancelledRule3SpatialKeys compareLex Ordering.byKey
  dsimp [mapAromaticCanonicalUncancelledRule3SpatialKey]
  rw [exactOfficialRuleMajorKey_compare_map_natural_of_observations
    source atomPermutation rule1aNatural rule2Natural]

theorem compareAromaticCanonicalUncancelledRule3SpatialKeys_self_map_eq_of_observations
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (rule1aNatural : ∀ node,
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node) =
        source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation node)
    (rule2Natural : ∀ node,
      (ofLex (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node))).2 =
        (ofLex (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel node)).2)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys key
        (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation key) = .eq := by
  have comparisonNatural :
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys key
          (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation key) =
        source.compareAromaticCanonicalUncancelledRule3SpatialKeys key key := by
    unfold compareAromaticCanonicalUncancelledRule3SpatialKeys compareLex Ordering.byKey
    dsimp [mapAromaticCanonicalUncancelledRule3SpatialKey,
      mapAromaticCanonicalExactOfficialRuleMajorKey]
    unfold ExactOfficialRuleMajorKey.compare ExactOfficialRuleMajorKey.compareAddressedSources
      ExactOfficialRuleMajorKey.exactRule1aLayers ExactOfficialRuleMajorKey.rule1bLayers
      ExactOfficialRuleMajorKey.rule2Layers Ordering.byKey compareLex
    dsimp only
    rw [mapSourceLayers_mapAromaticCanonicalAddressedSourceLayers
        atomPermutation _ rule1aNatural,
      mapSourceLayers_mapAromaticCanonicalAddressedSourceLayers atomPermutation _
        (rule1bRootDistance_mapAromaticCanonicalOfficialCIPNode atomPermutation),
      mapSourceLayers_mapAromaticCanonicalAddressedSourceLayers atomPermutation
        (fun node => (ofLex
          (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel node)).2)
        rule2Natural]
  rw [comparisonNatural]
  letI := source.compareAromaticCanonicalUncancelledRule3SpatialKeys_transCmp
  exact Std.ReflCmp.compare_self

theorem aromaticCanonicalAtomRecord_natural
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (constitution : source.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (atom : source.AromaticCanonicalAtom) :
    source.molecule.atoms.get (atomPermutation atom) =
      source.molecule.atoms.get atom :=
  constitution.1 atom

theorem aromaticCanonicalAtomZ_natural
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (constitution : source.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (atom : source.AromaticCanonicalAtom) :
    source.molecule.toLocalizedMoleculeGraph.atomZ (atomPermutation atom) =
      source.molecule.toLocalizedMoleculeGraph.atomZ atom := by
  simpa using congrArg (fun record : SemanticAtom => record.element.atomicNumber)
    (constitution.1 atom)

theorem aromaticCanonicalAtomMass_natural
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (constitution : source.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (atom : source.AromaticCanonicalAtom) :
    source.molecule.toLocalizedMoleculeGraph.atomMass (atomPermutation atom) =
      source.molecule.toLocalizedMoleculeGraph.atomMass atom := by
  simpa using congrArg (fun record : SemanticAtom => record.rule2MassPico?.getD 0)
    (constitution.1 atom)

theorem officialNodeRule2_natural_of_constitution
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (constitution : source.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    (ofLex (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel
        (mapAromaticCanonicalOfficialCIPNode atomPermutation node))).2 =
      (ofLex (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel node)).2 := by
  cases node with
  | mk current history provenance =>
      cases current with
      | none => rfl
      | some atom =>
          cases provenance with
          | realAtom =>
              unfold mapAromaticCanonicalOfficialCIPNode
                MoleculeGraph.officialNodeAtomLabel MoleculeGraph.rawCIPAtomLabel
              dsimp only [Option.map]
              exact aromaticCanonicalAtomMass_natural source atomPermutation constitution atom
          | multipleBondDuplicate distance => rfl
          | ringDuplicate distance => rfl
          | placeholder kind distance => rfl

theorem no_localizedMancudeEdge_of_no_aromatic_edges
    (source : AuthoritativeChemicalInput)
    (exact : source.molecule.SemanticAromaticMancudeEdgeSetExact source.molecule)
    (noEdges : source.molecule.aromaticPairEdges = [])
    (left right : source.AromaticCanonicalAtom) :
    ¬ source.molecule.toLocalizedMoleculeGraph.LocalizedMancudeEdge left right := by
  rw [source.molecule.localizedMancudeEdge_iff_semanticEdgeKey_mem_aromaticPairEdges
    source.molecule exact]
  simp [noEdges]

theorem exactOfficialRule1aObservation_natural_of_constitution_of_no_edges
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (constitution : source.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (exact : source.molecule.SemanticAromaticMancudeEdgeSetExact source.molecule)
    (noEdges : source.molecule.aromaticPairEdges = [])
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        (mapAromaticCanonicalOfficialCIPNode atomPermutation node) =
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation node := by
  cases node with
  | mk current history provenance =>
      cases current with
      | none => rfl
      | some atom =>
          cases provenance with
          | realAtom =>
              unfold mapAromaticCanonicalOfficialCIPNode
                MoleculeGraph.exactOfficialRule1aObservation
              dsimp only [Option.map]
              exact congrArg DeclarativeCIP.ExactAtomicNumber.ofNat
                (aromaticCanonicalAtomZ_natural source atomPermutation constitution atom)
          | ringDuplicate distance =>
              unfold mapAromaticCanonicalOfficialCIPNode
                MoleculeGraph.exactOfficialRule1aObservation
              dsimp only [Option.map]
              exact congrArg DeclarativeCIP.ExactAtomicNumber.ofNat
                (aromaticCanonicalAtomZ_natural source atomPermutation constitution atom)
          | placeholder kind distance =>
              unfold mapAromaticCanonicalOfficialCIPNode
                MoleculeGraph.exactOfficialRule1aObservation
              dsimp only [Option.map]
              exact congrArg DeclarativeCIP.ExactAtomicNumber.ofNat
                (aromaticCanonicalAtomZ_natural source atomPermutation constitution atom)
          | multipleBondDuplicate distance =>
              cases history with
              | nil =>
                  unfold mapAromaticCanonicalOfficialCIPNode
                    MoleculeGraph.exactOfficialRule1aObservation OfficialCIPNode.parent?
                  dsimp only [Option.map, List.map]
                  exact congrArg DeclarativeCIP.ExactAtomicNumber.ofNat
                    (aromaticCanonicalAtomZ_natural source atomPermutation constitution atom)
              | cons first rest =>
                  cases rest with
                  | nil =>
                      unfold mapAromaticCanonicalOfficialCIPNode
                        MoleculeGraph.exactOfficialRule1aObservation OfficialCIPNode.parent?
                      dsimp only [Option.map, List.map]
                      exact congrArg DeclarativeCIP.ExactAtomicNumber.ofNat
                        (aromaticCanonicalAtomZ_natural source atomPermutation constitution atom)
                  | cons parent tail =>
                      unfold mapAromaticCanonicalOfficialCIPNode
                        MoleculeGraph.exactOfficialRule1aObservation OfficialCIPNode.parent?
                      dsimp only [Option.map, List.map]
                      simp [MoleculeGraph.exactRule1aMultipleBond,
                        no_localizedMancudeEdge_of_no_aromatic_edges source exact noEdges]
                      exact congrArg DeclarativeCIP.ExactAtomicNumber.ofNat
                        (aromaticCanonicalAtomZ_natural source atomPermutation constitution atom)

theorem compareAromaticCanonicalUncancelledRule3SpatialKeys_map_natural_of_constitution_of_no_edges
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (constitution : source.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (exact : source.molecule.SemanticAromaticMancudeEdgeSetExact source.molecule)
    (noEdges : source.molecule.aromaticPairEdges = [])
    (left right : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation left)
        (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation right) =
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys left right := by
  exact compareAromaticCanonicalUncancelledRule3SpatialKeys_map_natural_of_observations
    source atomPermutation
      (exactOfficialRule1aObservation_natural_of_constitution_of_no_edges
        source atomPermutation constitution exact noEdges)
      (officialNodeRule2_natural_of_constitution source atomPermutation constitution)
      left right

theorem insertAromaticCanonicalUncancelledRule3SpatialKey_map
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (compareNatural : ∀ left right,
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys
          (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation left)
          (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation right) =
        source.compareAromaticCanonicalUncancelledRule3SpatialKeys left right)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    ∀ keys,
      insertAromaticCanonicalUncancelledRule3SpatialKey
          source.compareAromaticCanonicalUncancelledRule3SpatialKeys
          (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation key)
          (keys.map (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation)) =
        (insertAromaticCanonicalUncancelledRule3SpatialKey
          source.compareAromaticCanonicalUncancelledRule3SpatialKeys key keys).map
            (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation)
  | [] => rfl
  | head :: tail => by
      simp only [List.map_cons]
      unfold insertAromaticCanonicalUncancelledRule3SpatialKey
      rw [compareNatural key head]
      cases source.compareAromaticCanonicalUncancelledRule3SpatialKeys key head with
      | lt =>
          simp only [List.map_cons, List.cons.injEq, true_and]
          exact insertAromaticCanonicalUncancelledRule3SpatialKey_map
            source atomPermutation compareNatural key tail
      | eq => rfl
      | gt => rfl

theorem sortAromaticCanonicalUncancelledRule3SpatialKeys_map
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (compareNatural : ∀ left right,
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys
          (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation left)
          (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation right) =
        source.compareAromaticCanonicalUncancelledRule3SpatialKeys left right) :
    ∀ keys,
      sortAromaticCanonicalUncancelledRule3SpatialKeys
          source.compareAromaticCanonicalUncancelledRule3SpatialKeys
          (keys.map (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation)) =
        (sortAromaticCanonicalUncancelledRule3SpatialKeys
          source.compareAromaticCanonicalUncancelledRule3SpatialKeys keys).map
            (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation)
  | [] => rfl
  | key :: keys => by
      simp only [List.map_cons]
      unfold sortAromaticCanonicalUncancelledRule3SpatialKeys
      rw [sortAromaticCanonicalUncancelledRule3SpatialKeys_map
        source atomPermutation compareNatural keys]
      exact insertAromaticCanonicalUncancelledRule3SpatialKey_map
        source atomPermutation compareNatural key _

theorem aromaticCanonicalRule3ObservationChildLayerCount_map
    {source : AuthoritativeChemicalInput}
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    aromaticCanonicalRule3ObservationChildLayerCount
        (keys.map (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation)) =
      aromaticCanonicalRule3ObservationChildLayerCount keys := by
  unfold aromaticCanonicalRule3ObservationChildLayerCount
  have generalized : ∀ initial,
      (keys.map (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation)).foldl
          (fun longest child => max longest child.observations.length) initial =
        keys.foldl (fun longest child => max longest child.observations.length) initial := by
    induction keys with
    | nil => intro initial; rfl
    | cons key keys ih =>
        intro initial
        simp only [List.map_cons, List.foldl_cons]
        simpa [mapAromaticCanonicalUncancelledRule3SpatialKey] using
          ih (max initial key.observations.length)
  exact generalized 0

theorem aromaticCanonicalRule3PriorityChildLayerCount_map
    {source : AuthoritativeChemicalInput}
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    aromaticCanonicalRule3PriorityChildLayerCount
        (keys.map (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation)) =
      aromaticCanonicalRule3PriorityChildLayerCount keys := by
  unfold aromaticCanonicalRule3PriorityChildLayerCount
  have generalized : ∀ initial,
      (keys.map (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation)).foldl
          (fun longest child => max longest child.rule3.length) initial =
        keys.foldl (fun longest child => max longest child.rule3.length) initial := by
    induction keys with
    | nil => intro initial; rfl
    | cons key keys ih =>
        intro initial
        simp only [List.map_cons, List.foldl_cons]
        simpa [mapAromaticCanonicalUncancelledRule3SpatialKey] using
          ih (max initial key.rule3.length)
  exact generalized 0

theorem mergeAromaticCanonicalRule3ObservationChildren_map
    {source : AuthoritativeChemicalInput}
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    mergeAromaticCanonicalRule3ObservationChildren
        (keys.map (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation)) =
      mergeAromaticCanonicalRule3ObservationChildren keys := by
  unfold mergeAromaticCanonicalRule3ObservationChildren
  rw [aromaticCanonicalRule3ObservationChildLayerCount_map]
  apply List.map_congr_left
  intro depth present
  rw [List.zipIdx_map, List.flatMap_map]
  apply List.flatMap_congr
  intro child childPresent
  cases child with
  | mk key slot =>
      simp [mapAromaticCanonicalUncancelledRule3SpatialKey]

theorem mergeAromaticCanonicalRule3PriorityChildren_map
    {source : AuthoritativeChemicalInput}
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    mergeAromaticCanonicalRule3PriorityChildren
        (keys.map (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation)) =
      mergeAromaticCanonicalRule3PriorityChildren keys := by
  unfold mergeAromaticCanonicalRule3PriorityChildren
  rw [aromaticCanonicalRule3PriorityChildLayerCount_map]
  apply List.map_congr_left
  intro depth present
  rw [List.zipIdx_map, List.flatMap_map]
  apply List.flatMap_congr
  intro child childPresent
  cases child with
  | mk key slot =>
      simp [mapAromaticCanonicalUncancelledRule3SpatialKey]

theorem mapAromaticCanonicalAddressedSourceLayers_mergeAddressedChildren
    {source : AuthoritativeChemicalInput}
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (children : List (OfficialRuleMajorKey.AddressedSourceLayers
      source.AromaticCanonicalAtom)) :
    mapAromaticCanonicalAddressedSourceLayers atomPermutation
        (OfficialRuleMajorKey.mergeAddressedChildren children) =
      OfficialRuleMajorKey.mergeAddressedChildren
        (children.map (mapAromaticCanonicalAddressedSourceLayers atomPermutation)) := by
  unfold mapAromaticCanonicalAddressedSourceLayers
    OfficialRuleMajorKey.mergeAddressedChildren
  have countEq :
      OfficialRuleMajorKey.addressedChildLayerCount
          (children.map (fun layers =>
            layers.map fun layer => layer.map fun entry =>
              (entry.1, mapAromaticCanonicalOfficialCIPNode atomPermutation entry.2))) =
        OfficialRuleMajorKey.addressedChildLayerCount children := by
    unfold OfficialRuleMajorKey.addressedChildLayerCount
    have generalized : ∀ initial,
        (children.map (fun layers =>
          layers.map fun layer => layer.map fun entry =>
            (entry.1, mapAromaticCanonicalOfficialCIPNode atomPermutation entry.2))).foldl
            (fun longest child => max longest child.length) initial =
          children.foldl (fun longest child => max longest child.length) initial := by
      induction children with
      | nil => intro initial; rfl
      | cons child children ih =>
          intro initial
          simp only [List.map_cons, List.foldl_cons, List.length_map]
          exact ih (max initial child.length)
    exact generalized 0
  rw [countEq]
  rw [List.map_map]
  apply List.map_congr_left
  intro depth present
  simp only [Function.comp_apply]
  rw [List.map_flatMap, List.zipIdx_map, List.flatMap_map]
  apply List.flatMap_congr
  intro child childPresent
  cases child with
  | mk layers slot =>
      change
        (OfficialRuleMajorKey.prefixLayer slot (layers.getD depth [])).map
            (OfficialRuleMajorKey.mapObservation
              (mapAromaticCanonicalOfficialCIPNode atomPermutation)) =
          OfficialRuleMajorKey.prefixLayer slot
            ((OfficialRuleMajorKey.mapSourceLayers
              (mapAromaticCanonicalOfficialCIPNode atomPermutation) layers).getD depth [])
      rw [OfficialRuleMajorKey.mapSourceLayers_getD]
      exact (OfficialRuleMajorKey.prefixLayer_mapObservation
        (mapAromaticCanonicalOfficialCIPNode atomPermutation) slot
          (layers.getD depth [])).symm

theorem mapAromaticCanonicalExactOfficialRuleMajorKey_assemble
    {source : AuthoritativeChemicalInput}
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (root : ExactOfficialRuleMajorKey source.AromaticCanonicalAtom)
    (children : List (ExactOfficialRuleMajorKey source.AromaticCanonicalAtom)) :
    mapAromaticCanonicalExactOfficialRuleMajorKey atomPermutation
        (ExactOfficialRuleMajorKey.assemble root children) =
      ExactOfficialRuleMajorKey.assemble
        (mapAromaticCanonicalExactOfficialRuleMajorKey atomPermutation root)
        (children.map (mapAromaticCanonicalExactOfficialRuleMajorKey atomPermutation)) := by
  cases root with
  | mk rootSources rootComplete =>
    simp only [mapAromaticCanonicalExactOfficialRuleMajorKey,
      ExactOfficialRuleMajorKey.assemble]
    rw [show mapAromaticCanonicalAddressedSourceLayers atomPermutation
          (rootSources ++ OfficialRuleMajorKey.mergeAddressedChildren
            (children.map ExactOfficialRuleMajorKey.sourceNodes)) =
        mapAromaticCanonicalAddressedSourceLayers atomPermutation rootSources ++
          mapAromaticCanonicalAddressedSourceLayers atomPermutation
            (OfficialRuleMajorKey.mergeAddressedChildren
              (children.map ExactOfficialRuleMajorKey.sourceNodes)) by
      simp [mapAromaticCanonicalAddressedSourceLayers]]
    rw [mapAromaticCanonicalAddressedSourceLayers_mergeAddressedChildren]
    simp [mapAromaticCanonicalExactOfficialRuleMajorKey, List.map_map,
      Function.comp_def]

private theorem mapM_map_option_natural
    {alpha beta gamma : Type*}
    (mapInput : alpha → beta) (mapOutput : gamma → gamma)
    (right : beta → Option gamma) (left : alpha → Option gamma)
    (natural : ∀ value, right (mapInput value) = (left value).map mapOutput) :
    ∀ values : List alpha,
      (values.map mapInput).mapM right =
        (values.mapM left).map (List.map mapOutput)
  | [] => rfl
  | value :: values => by
      rw [List.map_cons, List.mapM_cons, natural value,
        mapM_map_option_natural mapInput mapOutput right left natural values]
      cases head : left value <;> cases tail : values.mapM left <;>
        simp [head, tail]

private theorem mapM_map_option_natural_of_mem
    {alpha beta gamma : Type*}
    (mapInput : alpha → beta) (mapOutput : gamma → gamma)
    (right : beta → Option gamma) (left : alpha → Option gamma) :
    ∀ values : List alpha,
      (∀ value, value ∈ values →
        right (mapInput value) = (left value).map mapOutput) →
      (values.map mapInput).mapM right =
        (values.mapM left).map (List.map mapOutput)
  | [], _ => rfl
  | value :: values, natural => by
      rw [List.map_cons, List.mapM_cons, natural value (by simp),
        mapM_map_option_natural_of_mem mapInput mapOutput right left values
          (fun tail present => natural tail (by simp [present]))]
      cases head : left value <;> cases tail : values.mapM left <;>
        simp [head, tail]

def AromaticCanonicalRule3CursorAutomorphismNatural
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    {carrierFuel : Nat}
    (mapCursor : source.AromaticCanonicalRerootCursor carrierFuel →
      source.AromaticCanonicalRerootCursor carrierFuel) :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel → Prop
  | 0, cursor =>
      (mapCursor cursor).occurrence.1.node =
          mapAromaticCanonicalOfficialCIPNode atomPermutation cursor.occurrence.1.node ∧
        source.aromaticCanonicalRerootChildren (mapCursor cursor) =
          (source.aromaticCanonicalRerootChildren cursor).map mapCursor
  | fuel + 1, cursor =>
      (mapCursor cursor).occurrence.1.node =
          mapAromaticCanonicalOfficialCIPNode atomPermutation cursor.occurrence.1.node ∧
        source.aromaticCanonicalRerootChildren (mapCursor cursor) =
          (source.aromaticCanonicalRerootChildren cursor).map mapCursor ∧
        ∀ child ∈ source.aromaticCanonicalRerootChildren cursor,
          AromaticCanonicalRule3CursorAutomorphismNatural source atomPermutation
            mapCursor fuel child

/-- Recursive Rule-3 compilation is natural under an exact cursor automorphism once its actual
cursor children and node observation producers are natural. -/
theorem buildAromaticCanonicalRule3SpatialKeyWith?_automorphism_natural
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    {carrierFuel : Nat}
    (mapCursor : source.AromaticCanonicalRerootCursor carrierFuel →
      source.AromaticCanonicalRerootCursor carrierFuel)
    (nodeNatural : ∀ cursor,
      (mapCursor cursor).occurrence.1.node =
        mapAromaticCanonicalOfficialCIPNode atomPermutation cursor.occurrence.1.node)
    (childrenNatural : ∀ cursor,
      source.aromaticCanonicalRerootChildren (mapCursor cursor) =
        (source.aromaticCanonicalRerootChildren cursor).map mapCursor)
    (observe : OfficialCIPNode source.AromaticCanonicalAtom →
      Option (Option source.AromaticCanonicalRule3SpatialNodeResult))
    (observeNatural : ∀ node,
      observe (mapAromaticCanonicalOfficialCIPNode atomPermutation node) = observe node)
    (compareNatural : ∀ left right,
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys
          (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation left)
          (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation right) =
        source.compareAromaticCanonicalUncancelledRule3SpatialKeys left right) :
    ∀ fuel cursor,
      source.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel (mapCursor cursor) =
        (source.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel cursor).map
          (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation) := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor
      unfold buildAromaticCanonicalRule3SpatialKeyWith?
      rw [childrenNatural cursor, nodeNatural cursor, observeNatural]
      cases childrenComputed : source.aromaticCanonicalRerootChildren cursor with
      | nil =>
          cases observationComputed : observe cursor.occurrence.1.node with
          | none => simp
          | some observation =>
              simp [
                mapAromaticCanonicalUncancelledRule3SpatialKey,
                mapAromaticCanonicalExactOfficialRuleMajorKey,
                mapAromaticCanonicalAddressedSourceLayers,
                MoleculeGraph.exactOfficialRuleMajorRootKey]
      | cons child tail =>
          cases observationComputed : observe cursor.occurrence.1.node <;> simp
  | succ fuel inductionHypothesis =>
      intro cursor
      unfold buildAromaticCanonicalRule3SpatialKeyWith?
      rw [childrenNatural cursor, nodeNatural cursor, observeNatural]
      cases childrenComputed : source.aromaticCanonicalRerootChildren cursor with
      | nil =>
          cases observationComputed : observe cursor.occurrence.1.node with
          | none => simp
          | some observation =>
              simp [
                mapAromaticCanonicalUncancelledRule3SpatialKey,
                mapAromaticCanonicalExactOfficialRuleMajorKey,
                mapAromaticCanonicalAddressedSourceLayers,
                MoleculeGraph.exactOfficialRuleMajorRootKey]
      | cons child tail =>
          cases observationComputed : observe cursor.occurrence.1.node with
          | none => simp
          | some observation =>
              have childMap := mapM_map_option_natural mapCursor
                (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation)
                (source.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel)
                (source.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel)
                inductionHypothesis (child :: tail)
              simp only [List.map_cons, List.cons_ne_nil, ↓reduceIte] at childMap ⊢
              rw [childMap]
              cases childKeysComputed : (child :: tail).mapM
                  (source.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel) with
              | none => simp
              | some childKeys =>
                  simp
                  rw [sortAromaticCanonicalUncancelledRule3SpatialKeys_map
                    source atomPermutation compareNatural]
                  simp only [mapAromaticCanonicalUncancelledRule3SpatialKey]
                  rw [mapAromaticCanonicalExactOfficialRuleMajorKey_assemble,
                    mergeAromaticCanonicalRule3ObservationChildren_map,
                    mergeAromaticCanonicalRule3PriorityChildren_map]
                  simp [mapAromaticCanonicalExactOfficialRuleMajorKey,
                    mapAromaticCanonicalAddressedSourceLayers,
                    MoleculeGraph.exactOfficialRuleMajorRootKey,
                    List.map_map, Function.comp_def,
                    mapAromaticCanonicalUncancelledRule3SpatialKey]

theorem buildAromaticCanonicalRule3SpatialKeyWith?_automorphism_natural_of_cursor
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    {carrierFuel : Nat}
    (mapCursor : source.AromaticCanonicalRerootCursor carrierFuel →
      source.AromaticCanonicalRerootCursor carrierFuel)
    (observe : OfficialCIPNode source.AromaticCanonicalAtom →
      Option (Option source.AromaticCanonicalRule3SpatialNodeResult))
    (observeNatural : ∀ node,
      observe (mapAromaticCanonicalOfficialCIPNode atomPermutation node) = observe node)
    (compareNatural : ∀ left right,
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys
          (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation left)
          (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation right) =
        source.compareAromaticCanonicalUncancelledRule3SpatialKeys left right) :
    ∀ fuel cursor,
      AromaticCanonicalRule3CursorAutomorphismNatural source atomPermutation
          mapCursor fuel cursor →
      source.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel (mapCursor cursor) =
        (source.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel cursor).map
          (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation) := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor natural
      unfold AromaticCanonicalRule3CursorAutomorphismNatural at natural
      unfold buildAromaticCanonicalRule3SpatialKeyWith?
      rw [natural.2, natural.1, observeNatural]
      cases childrenComputed : source.aromaticCanonicalRerootChildren cursor with
      | nil =>
          cases observationComputed : observe cursor.occurrence.1.node with
          | none => simp
          | some observation =>
              simp [mapAromaticCanonicalUncancelledRule3SpatialKey,
                mapAromaticCanonicalExactOfficialRuleMajorKey,
                mapAromaticCanonicalAddressedSourceLayers,
                MoleculeGraph.exactOfficialRuleMajorRootKey]
      | cons child tail =>
          cases observationComputed : observe cursor.occurrence.1.node <;> simp
  | succ fuel inductionHypothesis =>
      intro cursor natural
      unfold AromaticCanonicalRule3CursorAutomorphismNatural at natural
      unfold buildAromaticCanonicalRule3SpatialKeyWith?
      rw [natural.2.1, natural.1, observeNatural]
      cases childrenComputed : source.aromaticCanonicalRerootChildren cursor with
      | nil =>
          cases observationComputed : observe cursor.occurrence.1.node with
          | none => simp
          | some observation =>
              simp [mapAromaticCanonicalUncancelledRule3SpatialKey,
                mapAromaticCanonicalExactOfficialRuleMajorKey,
                mapAromaticCanonicalAddressedSourceLayers,
                MoleculeGraph.exactOfficialRuleMajorRootKey]
      | cons child tail =>
          cases observationComputed : observe cursor.occurrence.1.node with
          | none => simp
          | some observation =>
              have childMap := mapM_map_option_natural_of_mem mapCursor
                (mapAromaticCanonicalUncancelledRule3SpatialKey atomPermutation)
                (source.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel)
                (source.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel)
                (child :: tail) (fun next present =>
                  inductionHypothesis next (natural.2.2 next (by
                    simpa [childrenComputed] using present)))
              simp only [List.map_cons, List.cons_ne_nil, ↓reduceIte] at childMap ⊢
              rw [childMap]
              cases childKeysComputed : (child :: tail).mapM
                  (source.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel) with
              | none => simp
              | some childKeys =>
                  simp
                  rw [sortAromaticCanonicalUncancelledRule3SpatialKeys_map
                    source atomPermutation compareNatural]
                  simp only [mapAromaticCanonicalUncancelledRule3SpatialKey]
                  rw [mapAromaticCanonicalExactOfficialRuleMajorKey_assemble,
                    mergeAromaticCanonicalRule3ObservationChildren_map,
                    mergeAromaticCanonicalRule3PriorityChildren_map]
                  simp [mapAromaticCanonicalExactOfficialRuleMajorKey,
                    mapAromaticCanonicalAddressedSourceLayers,
                    MoleculeGraph.exactOfficialRuleMajorRootKey,
                    List.map_map, Function.comp_def,
                    mapAromaticCanonicalUncancelledRule3SpatialKey]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
