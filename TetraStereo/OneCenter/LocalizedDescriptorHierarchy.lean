import TetraStereo.OneCenter.LocalizedOfficialContextPerception

set_option autoImplicit false

namespace TetraStereo.OneCenter


















namespace CertifiedLocalizedCIPInput

/-- One addressed provenance occurrence, classified either as a constitution-only tetrahedral
descriptor source or as a non-source. -/
abbrev AddressedConstitutionalSeedObservation (input : CertifiedLocalizedCIPInput) :=
  OfficialSparseEntry (Option input.ConstitutionalSeedSource)

/-- Complete addressed descriptor observations for a ligand, sphere by sphere. -/
abbrev AddressedConstitutionalSeedLayers (input : CertifiedLocalizedCIPInput) :=
  List (List input.AddressedConstitutionalSeedObservation)

/-- Classify one addressed provenance node.  A non-source is retained as `none`; a real detected
tetrahedral center whose constitution-only descriptor cannot be established makes the operation
fail. -/
def observeAddressedConstitutionalSeed? (input : CertifiedLocalizedCIPInput)
    (entry : OfficialSparseEntry (OfficialCIPNode input.Atom)) :
    Option input.AddressedConstitutionalSeedObservation :=
  match input.realTetrahedralCenterAtNode? entry.2 with
  | none => some (entry.1, none)
  | some center => do
      let descriptor ← input.constitutionalSeedDescriptorAt? center
      some (entry.1, some (center, descriptor))

/-- Independent meaning of one addressed observation.  Addresses are unchanged, absence carries
a proof that the provenance node is not a real detected tetrahedral center, and presence carries
the exact molecular occurrence and declarative constitution-only descriptor evidence. -/
def DeclarativeAddressedConstitutionalSeedObservation
    (input : CertifiedLocalizedCIPInput)
    (entry : OfficialSparseEntry (OfficialCIPNode input.Atom))
    (observation : input.AddressedConstitutionalSeedObservation) : Prop :=
  entry.1 = observation.1 ∧
    match observation.2 with
    | none => ∀ center, ¬ input.RealTetrahedralCenterNode entry.2 center
    | some source => input.DeclarativeConstitutionalSeedSource entry.2 source

/-- One successful executable node observation satisfies the independent addressed relation. -/
theorem observeAddressedConstitutionalSeed?_sound
    (input : CertifiedLocalizedCIPInput)
    (entry : OfficialSparseEntry (OfficialCIPNode input.Atom))
    (observation : input.AddressedConstitutionalSeedObservation)
    (computed : input.observeAddressedConstitutionalSeed? entry = some observation) :
    input.DeclarativeAddressedConstitutionalSeedObservation entry observation := by
  unfold observeAddressedConstitutionalSeed? at computed
  cases centerComputed : input.realTetrahedralCenterAtNode? entry.2 with
  | none =>
      simp [centerComputed] at computed
      subst observation
      constructor
      · rfl
      · intro center atNode
        have present :=
          (input.realTetrahedralCenterAtNode?_eq_some_iff entry.2 center).mpr atNode
        rw [centerComputed] at present
        contradiction
  | some center =>
      cases descriptorComputed : input.constitutionalSeedDescriptorAt? center with
      | none => simp [centerComputed, descriptorComputed] at computed
      | some descriptor =>
          simp [centerComputed, descriptorComputed] at computed
          subst observation
          exact ⟨rfl,
            (input.realTetrahedralCenterAtNode?_eq_some_iff entry.2 center).mp centerComputed,
            input.constitutionalSeedDescriptorAt?_sound
              center descriptor descriptorComputed⟩

/-- Structural, fail-closed observation of one complete addressed sphere. -/
def observeConstitutionalSeedLayer? (input : CertifiedLocalizedCIPInput) :
    List (OfficialSparseEntry (OfficialCIPNode input.Atom)) →
      Option (List input.AddressedConstitutionalSeedObservation)
  | [] => some []
  | entry :: entries => do
      let observation ← input.observeAddressedConstitutionalSeed? entry
      let observations ← input.observeConstitutionalSeedLayer? entries
      some (observation :: observations)

/-- Pointwise declarative correspondence for one complete addressed sphere. -/
inductive DeclarativeConstitutionalSeedLayer (input : CertifiedLocalizedCIPInput) :
    List (OfficialSparseEntry (OfficialCIPNode input.Atom)) →
      List input.AddressedConstitutionalSeedObservation → Prop
  | nil : DeclarativeConstitutionalSeedLayer input [] []
  | cons {entry entries observation observations}
      (head : input.DeclarativeAddressedConstitutionalSeedObservation entry observation)
      (tail : DeclarativeConstitutionalSeedLayer input entries observations) :
      DeclarativeConstitutionalSeedLayer input (entry :: entries)
        (observation :: observations)

theorem observeConstitutionalSeedLayer?_sound
    (input : CertifiedLocalizedCIPInput) :
    ∀ layer observations,
      input.observeConstitutionalSeedLayer? layer = some observations →
      input.DeclarativeConstitutionalSeedLayer layer observations
  | [], observations, computed => by
      simp [observeConstitutionalSeedLayer?] at computed
      subst observations
      exact DeclarativeConstitutionalSeedLayer.nil
  | entry :: entries, observations, computed => by
      unfold observeConstitutionalSeedLayer? at computed
      cases headComputed : input.observeAddressedConstitutionalSeed? entry with
      | none => simp [headComputed] at computed
      | some observation =>
          cases tailComputed : input.observeConstitutionalSeedLayer? entries with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst observations
              exact DeclarativeConstitutionalSeedLayer.cons
                (input.observeAddressedConstitutionalSeed?_sound
                  entry observation headComputed)
                (input.observeConstitutionalSeedLayer?_sound entries tail tailComputed)

/-- Structural, fail-closed observation of every addressed sphere. -/
def observeConstitutionalSeedLayers? (input : CertifiedLocalizedCIPInput) :
    OfficialRuleMajorKey.AddressedSourceLayers input.Atom →
      Option input.AddressedConstitutionalSeedLayers
  | [] => some []
  | layer :: layers => do
      let observations ← input.observeConstitutionalSeedLayer? layer
      let remaining ← input.observeConstitutionalSeedLayers? layers
      some (observations :: remaining)

/-- Exact declarative correspondence over every sphere and every addressed provenance node. -/
inductive DeclarativeConstitutionalSeedLayers (input : CertifiedLocalizedCIPInput) :
    OfficialRuleMajorKey.AddressedSourceLayers input.Atom →
      input.AddressedConstitutionalSeedLayers → Prop
  | nil : DeclarativeConstitutionalSeedLayers input [] []
  | cons {layer layers observations remaining}
      (head : input.DeclarativeConstitutionalSeedLayer layer observations)
      (tail : DeclarativeConstitutionalSeedLayers input layers remaining) :
      DeclarativeConstitutionalSeedLayers input (layer :: layers)
        (observations :: remaining)

theorem observeConstitutionalSeedLayers?_sound
    (input : CertifiedLocalizedCIPInput) :
    ∀ layers observations,
      input.observeConstitutionalSeedLayers? layers = some observations →
      input.DeclarativeConstitutionalSeedLayers layers observations
  | [], observations, computed => by
      simp [observeConstitutionalSeedLayers?] at computed
      subst observations
      exact DeclarativeConstitutionalSeedLayers.nil
  | layer :: layers, observations, computed => by
      unfold observeConstitutionalSeedLayers? at computed
      cases headComputed : input.observeConstitutionalSeedLayer? layer with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : input.observeConstitutionalSeedLayers? layers with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst observations
              exact DeclarativeConstitutionalSeedLayers.cons
                (input.observeConstitutionalSeedLayer?_sound layer head headComputed)
                (input.observeConstitutionalSeedLayers?_sound layers tail tailComputed)

/-- Build and observe the complete addressed provenance hierarchy for one canonical ligand. -/
def perceiveConstitutionalSeedHierarchyAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    Option input.AddressedConstitutionalSeedLayers := do
  let key ← input.buildExecutableOfficialRuleMajorKey
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center index))
  input.observeConstitutionalSeedLayers? key.sourceNodes

/-- Independent full-hierarchy perception relation. -/
def DeclarativeConstitutionalSeedHierarchyAt
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (observations : input.AddressedConstitutionalSeedLayers) : Prop :=
  ∃ sources,
    input.DeclarativeRuleMajorLigandExpansion center index sources ∧
    input.DeclarativeConstitutionalSeedLayers sources observations

theorem perceiveConstitutionalSeedHierarchyAt?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (observations : input.AddressedConstitutionalSeedLayers)
    (computed : input.perceiveConstitutionalSeedHierarchyAt? center index =
      some observations) :
    input.DeclarativeConstitutionalSeedHierarchyAt center index observations := by
  unfold perceiveConstitutionalSeedHierarchyAt? at computed
  cases keyComputed : input.buildExecutableOfficialRuleMajorKey
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index)) with
  | none => simp [keyComputed] at computed
  | some key =>
      simp only [keyComputed] at computed
      exact ⟨key.sourceNodes,
        input.buildExecutableOfficialRuleMajorKey_declarative_default
          center index key keyComputed,
        input.observeConstitutionalSeedLayers?_sound
          key.sourceNodes observations computed⟩

/-! ## Address-preserving descriptor projections -/

/-- Rule-4a kind at every addressed position.  Non-source positions are retained as explicit
nonstereogenic observations rather than deleted. -/
def constitutionalRule4aKind (input : CertifiedLocalizedCIPInput)
    (source : Option input.ConstitutionalSeedSource) : OfficialStereogenicUnitKind :=
  match source with
  | none => OfficialStereogenicUnitKind.nonstereogenic
  | some _ => OfficialStereogenicUnitKind.chiral

/-- Complete addressed Rule-4a projection. -/
def constitutionalRule4aLayers (input : CertifiedLocalizedCIPInput)
    (layers : input.AddressedConstitutionalSeedLayers) :
    List (List (OfficialSparseEntry OfficialStereogenicUnitKind)) :=
  OfficialRuleMajorKey.mapSourceLayers input.constitutionalRule4aKind layers

/-- Descriptors occurring in one sphere, retaining the sphere's canonical address order. -/
def constitutionalDescriptorsInLayer (input : CertifiedLocalizedCIPInput)
    (layer : List input.AddressedConstitutionalSeedObservation) : List RS :=
  layer.filterMap fun entry => entry.2.map Prod.snd

/-- Rule-4b reference senses selected from the first descriptor-bearing sphere. -/
def constitutionalRule4bReferences (input : CertifiedLocalizedCIPInput)
    (layers : input.AddressedConstitutionalSeedLayers) : List RS :=
  match layers.find? fun layer => !(input.constitutionalDescriptorsInLayer layer).isEmpty with
  | none => []
  | some layer =>
      let descriptors := input.constitutionalDescriptorsInLayer layer
      let rCount := (descriptors.filter fun descriptor => descriptor == RS.R).length
      let sCount := (descriptors.filter fun descriptor => descriptor == RS.S).length
      if sCount < rCount then [RS.R]
      else if rCount < sCount then [RS.S]
      else [RS.R, RS.S]

/-- Like/unlike bit relative to one selected Rule-4b or Rule-5 reference.  The zero assigned to
non-sources is an explicit placeholder at the same parent address. -/
def constitutionalReferencePriority (input : CertifiedLocalizedCIPInput) (reference : RS) :
    Option input.ConstitutionalSeedSource → ℕ
  | none => 0
  | some source => if source.2 == reference then 1 else 0

/-- Complete addressed reading under one reference sense. -/
def constitutionalReferenceReading (input : CertifiedLocalizedCIPInput)
    (reference : RS) (layers : input.AddressedConstitutionalSeedLayers) :
    List (List (OfficialSparseEntry ℕ)) :=
  OfficialRuleMajorKey.mapSourceLayers
    (input.constitutionalReferencePriority reference) layers

/-- Compare complete addressed descriptor readings in sphere/parent-slot order. -/
def compareConstitutionalReferenceReadings :
    List (List (OfficialSparseEntry ℕ)) →
      List (List (OfficialSparseEntry ℕ)) → Ordering :=
  OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat

/-- Structural descending insertion for the at-most-two Rule-4b reference readings. -/
def insertConstitutionalReferenceReading
    (reading : List (List (OfficialSparseEntry ℕ))) :
    List (List (List (OfficialSparseEntry ℕ))) →
      List (List (List (OfficialSparseEntry ℕ)))
  | [] => [reading]
  | head :: tail =>
      match compareConstitutionalReferenceReadings reading head with
      | Ordering.lt => head :: insertConstitutionalReferenceReading reading tail
      | Ordering.eq | Ordering.gt => reading :: head :: tail

/-- Descending structural sort of the complete alternative Rule-4b readings. -/
def sortConstitutionalReferenceReadings :
    List (List (List (OfficialSparseEntry ℕ))) →
      List (List (List (OfficialSparseEntry ℕ)))
  | [] => []
  | reading :: readings =>
      insertConstitutionalReferenceReading reading
        (sortConstitutionalReferenceReadings readings)

/-- Unary Rule-4b key.  A unique reference has priority over two references before their complete
like/unlike readings are compared. -/
structure ConstitutionalRule4bKey where
  referenceCountPriority : ℕ
  readings : List (List (List (OfficialSparseEntry ℕ)))
  deriving DecidableEq, Repr

def constitutionalRule4bReferenceCountPriority : List RS → ℕ
  | [_] => 2
  | [_, _] => 1
  | _ => 0

def constitutionalRule4bKey (input : CertifiedLocalizedCIPInput)
    (layers : input.AddressedConstitutionalSeedLayers) : ConstitutionalRule4bKey :=
  let references := input.constitutionalRule4bReferences layers
  let readings := references.map fun reference =>
    input.constitutionalReferenceReading reference layers
  { referenceCountPriority := constitutionalRule4bReferenceCountPriority references
    readings := sortConstitutionalReferenceReadings readings }

/-- Address-preserving Rule-4b projection comparison, including criterion (c)(i)'s
one-reference-over-two priority and both ranked readings in the tied-population case. -/
def compareConstitutionalRule4bKeys :
    ConstitutionalRule4bKey → ConstitutionalRule4bKey → Ordering :=
  compareLex
    (Ordering.byKey ConstitutionalRule4bKey.referenceCountPriority compare)
    (Ordering.byKey ConstitutionalRule4bKey.readings
      (List.compareLex compareConstitutionalReferenceReadings))

/-- Rule-5 result retains whether the two common-reference readings decide in opposite
directions.  That flag is the `±2` enantiomorphic comparison used by lowercase classification. -/
structure ConstitutionalRule5Comparison where
  ordering : Ordering
  pseudo : Bool
  deriving DecidableEq, Repr

def compareConstitutionalRule5Hierarchies (input : CertifiedLocalizedCIPInput)
    (left right : input.AddressedConstitutionalSeedLayers) :
    ConstitutionalRule5Comparison :=
  let cmpR := compareConstitutionalReferenceReadings
    (input.constitutionalReferenceReading RS.R left)
    (input.constitutionalReferenceReading RS.R right)
  let cmpS := compareConstitutionalReferenceReadings
    (input.constitutionalReferenceReading RS.S left)
    (input.constitutionalReferenceReading RS.S right)
  match cmpR with
  | Ordering.lt => { ordering := Ordering.lt, pseudo := cmpS != Ordering.lt }
  | Ordering.gt => { ordering := Ordering.gt, pseudo := cmpS != Ordering.gt }
  | Ordering.eq => { ordering := Ordering.eq, pseudo := false }

/-- Result of the complete addressed uppercase-seed Rules-4a/4b/5 fallthrough. -/
structure ConstitutionalDescriptorHierarchyComparison where
  ordering : Ordering
  decisiveRule? : Option CIPRuleFamily := none
  pseudo : Bool := false
  deriving DecidableEq, Repr

def compareConstitutionalDescriptorHierarchies
    (input : CertifiedLocalizedCIPInput)
    (left right : input.AddressedConstitutionalSeedLayers) :
    ConstitutionalDescriptorHierarchyComparison :=
  let rule4a := OfficialRuleMajorKey.compareSparseLayers OfficialStereogenicUnitKind.compare
    (input.constitutionalRule4aLayers left)
    (input.constitutionalRule4aLayers right)
  if rule4a != Ordering.eq then
    { ordering := rule4a, decisiveRule? := some CIPRuleFamily.stereogenicUnitKind }
  else
    let rule4b := compareConstitutionalRule4bKeys
      (input.constitutionalRule4bKey left)
      (input.constitutionalRule4bKey right)
    if rule4b != Ordering.eq then
      { ordering := rule4b, decisiveRule? := some CIPRuleFamily.likeUnlikeDescriptorPair }
    else
      let rule5 := input.compareConstitutionalRule5Hierarchies left right
      { ordering := rule5.ordering
        decisiveRule? := if rule5.ordering = Ordering.eq then none
          else some CIPRuleFamily.pseudoasymmetricTiebreak
        pseudo := rule5.pseudo }

/-- Relational reading of the complete uppercase-seed hierarchy comparison.  Each rule is freshly
projected from the addressed observations, and the stored result is obtained only by normative
4a → 4b → 5 fallthrough. -/
def DeclarativeConstitutionalDescriptorHierarchyComparison
    (input : CertifiedLocalizedCIPInput)
    (left right : input.AddressedConstitutionalSeedLayers)
    (result : ConstitutionalDescriptorHierarchyComparison) : Prop :=
  let rule4a := OfficialRuleMajorKey.compareSparseLayers OfficialStereogenicUnitKind.compare
    (input.constitutionalRule4aLayers left)
    (input.constitutionalRule4aLayers right)
  let rule4b := compareConstitutionalRule4bKeys
    (input.constitutionalRule4bKey left)
    (input.constitutionalRule4bKey right)
  let rule5 := input.compareConstitutionalRule5Hierarchies left right
  (rule4a != Ordering.eq ∧
      result = ⟨rule4a, some CIPRuleFamily.stereogenicUnitKind, false⟩) ∨
    (rule4a = Ordering.eq ∧ rule4b != Ordering.eq ∧
      result = ⟨rule4b, some CIPRuleFamily.likeUnlikeDescriptorPair, false⟩) ∨
    (rule4a = Ordering.eq ∧ rule4b = Ordering.eq ∧
      result = ⟨rule5.ordering,
        if rule5.ordering = Ordering.eq then none
          else some CIPRuleFamily.pseudoasymmetricTiebreak,
        rule5.pseudo⟩)

theorem compareConstitutionalDescriptorHierarchies_declarative
    (input : CertifiedLocalizedCIPInput)
    (left right : input.AddressedConstitutionalSeedLayers) :
    input.DeclarativeConstitutionalDescriptorHierarchyComparison left right
      (input.compareConstitutionalDescriptorHierarchies left right) := by
  by_cases rule4aTie :
      OfficialRuleMajorKey.compareSparseLayers OfficialStereogenicUnitKind.compare
        (input.constitutionalRule4aLayers left)
        (input.constitutionalRule4aLayers right) = Ordering.eq
  · by_cases rule4bTie :
        compareConstitutionalRule4bKeys
          (input.constitutionalRule4bKey left)
          (input.constitutionalRule4bKey right) = Ordering.eq
    · simp [DeclarativeConstitutionalDescriptorHierarchyComparison,
        compareConstitutionalDescriptorHierarchies, rule4aTie, rule4bTie]
    · simp [DeclarativeConstitutionalDescriptorHierarchyComparison,
        compareConstitutionalDescriptorHierarchies, rule4aTie, rule4bTie]
  · simp [DeclarativeConstitutionalDescriptorHierarchyComparison,
      compareConstitutionalDescriptorHierarchies, rule4aTie]

/-- Perceive and compare the complete addressed descriptor hierarchies of two ligands. -/
def comparePerceivedConstitutionalDescriptorHierarchiesAt?
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4) :
    Option ConstitutionalDescriptorHierarchyComparison := do
  let leftHierarchy ← input.perceiveConstitutionalSeedHierarchyAt? center left
  let rightHierarchy ← input.perceiveConstitutionalSeedHierarchyAt? center right
  some (input.compareConstitutionalDescriptorHierarchies leftHierarchy rightHierarchy)

/-- Independent molecule-to-hierarchy-to-comparison relation for one ligand pair. -/
def DeclarativePerceivedConstitutionalDescriptorHierarchyComparisonAt
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (result : ConstitutionalDescriptorHierarchyComparison) : Prop :=
  ∃ leftHierarchy rightHierarchy,
    input.DeclarativeConstitutionalSeedHierarchyAt center left leftHierarchy ∧
    input.DeclarativeConstitutionalSeedHierarchyAt center right rightHierarchy ∧
    input.DeclarativeConstitutionalDescriptorHierarchyComparison
      leftHierarchy rightHierarchy result

theorem comparePerceivedConstitutionalDescriptorHierarchiesAt?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (result : ConstitutionalDescriptorHierarchyComparison)
    (computed : input.comparePerceivedConstitutionalDescriptorHierarchiesAt?
      center left right = some result) :
    input.DeclarativePerceivedConstitutionalDescriptorHierarchyComparisonAt
      center left right result := by
  unfold comparePerceivedConstitutionalDescriptorHierarchiesAt? at computed
  cases leftComputed : input.perceiveConstitutionalSeedHierarchyAt? center left with
  | none => simp [leftComputed] at computed
  | some leftHierarchy =>
      cases rightComputed : input.perceiveConstitutionalSeedHierarchyAt? center right with
      | none => simp [leftComputed, rightComputed] at computed
      | some rightHierarchy =>
          simp [leftComputed, rightComputed] at computed
          subst result
          exact ⟨leftHierarchy, rightHierarchy,
            input.perceiveConstitutionalSeedHierarchyAt?_sound
              center left leftHierarchy leftComputed,
            input.perceiveConstitutionalSeedHierarchyAt?_sound
              center right rightHierarchy rightComputed,
            input.compareConstitutionalDescriptorHierarchies_declarative
              leftHierarchy rightHierarchy⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
