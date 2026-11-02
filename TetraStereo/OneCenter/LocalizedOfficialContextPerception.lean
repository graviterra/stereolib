import TetraStereo.OneCenter.AuthoritativeLocalizedTetrahedralDescriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Molecule-derived later-rule contexts for localized authoritative inputs

The localized rule-major analyzer historically accepted an arbitrary function supplying Rules
3--5 contexts.  This module begins replacing that boundary with evidence computed from the same
format-neutral molecule.

The first deliberately conservative pass discovers ordinary tetrahedral descriptor sources only.
It walks the complete addressed provenance tree of one ligand and treats every real graph atom
that is also a detected four-coordinate center as a potential descriptor source.  Such a source is
accepted only when its `R/S` descriptor is independently resolved by Rules 1a--2 and exact spatial
geometry, using an empty later-rule context.  If even one encountered four-coordinate center is
unresolved, the entire branch-context computation refuses.  Thus a missing Rule-4/5 fact can never
be silently skipped before a lower-priority fact is consulted.

This pass supplies Rule 4a and Rule 5 from the first descriptor-bearing occurrence, and Rule 4b
from the first later occurrence at a distinct molecular center.  Rule 3, Rule 4c, auxiliary
descriptor sequences, and the general dependency fixed point remain separate extensions.
-/

namespace CertifiedLocalizedCIPInput

/-- The empty later-rule environment used to establish constitution-only descriptor seeds. -/
def emptyOfficialContext (_index : Fin 4) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  CIPRuleEngine.OfficialLigandRuleContext.empty

/-- A tetrahedral `R/S` seed that does not depend on Rules 3--5. -/
def constitutionalSeedDescriptorAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) : Option RS :=
  input.ruleMajorTetrahedralSpatialDescriptorAt? center emptyOfficialContext

/-- Independent meaning of a constitution-only tetrahedral descriptor seed. -/
def DeclarativeConstitutionalSeedDescriptor
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (descriptor : RS) : Prop :=
  input.DeclarativeRuleMajorLocalizedTetrahedralDescriptor
    center emptyOfficialContext descriptor

/-- Every executable seed carries recursive constitutional-priority and exact-geometry evidence. -/
theorem constitutionalSeedDescriptorAt?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (descriptor : RS)
    (computed : input.constitutionalSeedDescriptorAt? center = some descriptor) :
    input.DeclarativeConstitutionalSeedDescriptor center descriptor := by
  exact input.ruleMajorTetrahedralSpatialDescriptorAt?_sound_declarative
    center emptyOfficialContext descriptor computed

/-- Recover the detected-center subtype at an atom, when the graph shape is tetrahedral. -/
def tetrahedralCenterAt? (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    Option input.TetrahedralCenter :=
  if detected : atom ∈ input.tetrahedralCenterSet then some ⟨atom, detected⟩ else none

@[simp] theorem tetrahedralCenterAt?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    (center : input.TetrahedralCenter) :
    input.tetrahedralCenterAt? atom = some center ↔ center.1 = atom := by
  by_cases detected : atom ∈ input.tetrahedralCenterSet
  · simp only [tetrahedralCenterAt?, dif_pos detected, Option.some.injEq]
    constructor
    · intro equality
      exact (congrArg Subtype.val equality).symm
    · intro equality
      exact Subtype.ext equality.symm
  · constructor
    · intro impossible
      simp [tetrahedralCenterAt?, detected] at impossible
    · intro equality
      subst atom
      exact (detected center.2).elim

/-- A provenance node is a real occurrence of a detected tetrahedral center.  Duplicate nodes are
not descriptor sources: CIP descriptors attach to real stereogenic-unit occurrences. -/
def RealTetrahedralCenterNode (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (center : input.TetrahedralCenter) : Prop :=
  node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    node.current? = some center.1

/-- Executable recognition of real tetrahedral-center occurrences. -/
def realTetrahedralCenterAtNode? (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) : Option input.TetrahedralCenter :=
  if node.provenance = OfficialCIPNodeProvenance.realAtom then
    match node.current? with
    | some atom => input.tetrahedralCenterAt? atom
    | none => none
  else none

theorem realTetrahedralCenterAtNode?_eq_some_iff
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (center : input.TetrahedralCenter) :
    input.realTetrahedralCenterAtNode? node = some center ↔
      input.RealTetrahedralCenterNode node center := by
  unfold realTetrahedralCenterAtNode? RealTetrahedralCenterNode
  by_cases real : node.provenance = OfficialCIPNodeProvenance.realAtom
  · simp only [if_pos real]
    cases current : node.current? with
    | none => simp
    | some atom =>
        rw [input.tetrahedralCenterAt?_eq_some_iff atom center]
        constructor
        · intro equality
          exact ⟨real, congrArg some equality.symm⟩
        · rintro ⟨_real, equality⟩
          exact (Option.some.inj equality).symm
  · simp [real]

/-- A descriptor source retains the actual molecular center and its constitution-only `R/S`. -/
abbrev ConstitutionalSeedSource (input : CertifiedLocalizedCIPInput) :=
  input.TetrahedralCenter × RS

/-- Independently justified descriptor source at one provenance node. -/
def DeclarativeConstitutionalSeedSource (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom)
    (source : input.ConstitutionalSeedSource) : Prop :=
  input.RealTetrahedralCenterNode node source.1 ∧
    input.DeclarativeConstitutionalSeedDescriptor source.1 source.2

/-- Fail-closed collection of descriptor sources from a linearized addressed tree.  Non-center
nodes are skipped.  Every real four-coordinate center must resolve constitutionally or the whole
collection returns `none`. -/
def collectConstitutionalSeedSources? (input : CertifiedLocalizedCIPInput) :
    List (OfficialCIPNode input.Atom) → Option (List input.ConstitutionalSeedSource)
  | [] => some []
  | node :: nodes =>
      match input.realTetrahedralCenterAtNode? node with
      | none => input.collectConstitutionalSeedSources? nodes
      | some center => do
          let descriptor ← input.constitutionalSeedDescriptorAt? center
          let sources ← input.collectConstitutionalSeedSources? nodes
          some ((center, descriptor) :: sources)

/-- Proof-relevant exact extraction relation.  It accounts for every provenance node: a node is
skipped only with proof that it is not a real tetrahedral-center occurrence; otherwise it is kept
with a declarative constitution-only descriptor proof. -/
inductive DeclarativeConstitutionalSeedExtraction (input : CertifiedLocalizedCIPInput) :
    List (OfficialCIPNode input.Atom) → List input.ConstitutionalSeedSource → Prop
  | nil : DeclarativeConstitutionalSeedExtraction input [] []
  | skip {node nodes sources}
      (notSource : ∀ center, ¬ input.RealTetrahedralCenterNode node center)
      (tail : DeclarativeConstitutionalSeedExtraction input nodes sources) :
      DeclarativeConstitutionalSeedExtraction input (node :: nodes) sources
  | keep {node nodes center descriptor sources}
      (atNode : input.RealTetrahedralCenterNode node center)
      (seed : input.DeclarativeConstitutionalSeedDescriptor center descriptor)
      (tail : DeclarativeConstitutionalSeedExtraction input nodes sources) :
      DeclarativeConstitutionalSeedExtraction input (node :: nodes)
        ((center, descriptor) :: sources)

/-- Successful collection is an exact, fail-closed declarative extraction over every input node. -/
theorem collectConstitutionalSeedSources?_sound
    (input : CertifiedLocalizedCIPInput) :
    ∀ nodes sources,
      input.collectConstitutionalSeedSources? nodes = some sources →
      input.DeclarativeConstitutionalSeedExtraction nodes sources
  | [], sources, computed => by
      simp [collectConstitutionalSeedSources?] at computed
      subst sources
      exact DeclarativeConstitutionalSeedExtraction.nil
  | node :: nodes, sources, computed => by
      unfold collectConstitutionalSeedSources? at computed
      cases centerComputed : input.realTetrahedralCenterAtNode? node with
      | none =>
          simp only [centerComputed] at computed
          have notSource : ∀ center,
              ¬ input.RealTetrahedralCenterNode node center := by
            intro center atNode
            have present :=
              (input.realTetrahedralCenterAtNode?_eq_some_iff node center).mpr atNode
            rw [centerComputed] at present
            contradiction
          exact DeclarativeConstitutionalSeedExtraction.skip notSource
            (input.collectConstitutionalSeedSources?_sound nodes sources computed)
      | some center =>
          cases descriptorComputed : input.constitutionalSeedDescriptorAt? center with
          | none => simp [centerComputed, descriptorComputed] at computed
          | some descriptor =>
              cases tailComputed : input.collectConstitutionalSeedSources? nodes with
              | none => simp [centerComputed, descriptorComputed, tailComputed] at computed
              | some tail =>
                  simp [centerComputed, descriptorComputed, tailComputed] at computed
                  subst sources
                  exact DeclarativeConstitutionalSeedExtraction.keep
                    ((input.realTetrahedralCenterAtNode?_eq_some_iff node center).mp
                      centerComputed)
                    (input.constitutionalSeedDescriptorAt?_sound
                      center descriptor descriptorComputed)
                    (input.collectConstitutionalSeedSources?_sound nodes tail tailComputed)

/-- Linearize addressed source layers without losing provenance-node multiplicity.  Addresses are
used for priority compilation; descriptor perception needs the resulting ordered occurrences. -/
def addressedSourceNodeList (input : CertifiedLocalizedCIPInput)
    (layers : OfficialRuleMajorKey.AddressedSourceLayers input.Atom) :
    List (OfficialCIPNode input.Atom) :=
  layers.flatten.map Prod.snd

/-- Fail-closed descriptor-source extraction from a complete addressed ligand tree. -/
def constitutionalSeedSources? (input : CertifiedLocalizedCIPInput)
    (layers : OfficialRuleMajorKey.AddressedSourceLayers input.Atom) :
    Option (List input.ConstitutionalSeedSource) :=
  input.collectConstitutionalSeedSources? (input.addressedSourceNodeList layers)

/-- First later descriptor occurrence at a molecular center distinct from the head source. -/
def firstDistinctConstitutionalSeedSource? (input : CertifiedLocalizedCIPInput)
    (head : input.ConstitutionalSeedSource) :
    List input.ConstitutionalSeedSource → Option input.ConstitutionalSeedSource
  | [] => none
  | source :: sources =>
      if source.1 ≠ head.1 then some source
      else input.firstDistinctConstitutionalSeedSource? head sources

/-- The first two source occurrences belonging to distinct molecular centers. -/
def firstDistinctConstitutionalSeedPair? (input : CertifiedLocalizedCIPInput) :
    List input.ConstitutionalSeedSource →
      Option (input.ConstitutionalSeedSource × input.ConstitutionalSeedSource)
  | [] => none
  | head :: sources =>
      (input.firstDistinctConstitutionalSeedSource? head sources).map fun other => (head, other)

/-- Rules 4a/4b/5 context generated by complete constitution-only descriptor sources. -/
def officialContextOfConstitutionalSeedSources
    (input : CertifiedLocalizedCIPInput)
    (sources : List input.ConstitutionalSeedSource) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  match sources with
  | [] => CIPRuleEngine.OfficialLigandRuleContext.empty
  | head :: tail =>
      let base := CIPRuleEngine.OfficialLigandRuleContext.ofRS head.2
      match input.firstDistinctConstitutionalSeedSource? head tail with
      | none => base
      | some other =>
          base.withRule4bPair
            (OfficialRule5Descriptor.pairKind
              (OfficialRule5Descriptor.ofRS head.2)
              (OfficialRule5Descriptor.ofRS other.2))

/-- Relational reading of the deliberately narrow context aggregation. -/
inductive DeclarativeContextOfConstitutionalSeedSources
    (input : CertifiedLocalizedCIPInput) :
    List input.ConstitutionalSeedSource →
      CIPRuleEngine.OfficialLigandRuleContext → Prop
  | empty : DeclarativeContextOfConstitutionalSeedSources input []
      CIPRuleEngine.OfficialLigandRuleContext.empty
  | firstOnly {head tail}
      (noDistinct : input.firstDistinctConstitutionalSeedSource? head tail = none) :
      DeclarativeContextOfConstitutionalSeedSources input (head :: tail)
        (CIPRuleEngine.OfficialLigandRuleContext.ofRS head.2)
  | firstPair {head tail other}
      (firstDistinct : input.firstDistinctConstitutionalSeedSource? head tail = some other) :
      DeclarativeContextOfConstitutionalSeedSources input (head :: tail)
        ((CIPRuleEngine.OfficialLigandRuleContext.ofRS head.2).withRule4bPair
          (OfficialRule5Descriptor.pairKind
            (OfficialRule5Descriptor.ofRS head.2)
            (OfficialRule5Descriptor.ofRS other.2)))

theorem officialContextOfConstitutionalSeedSources_declarative
    (input : CertifiedLocalizedCIPInput)
    (sources : List input.ConstitutionalSeedSource) :
    DeclarativeContextOfConstitutionalSeedSources input sources
      (input.officialContextOfConstitutionalSeedSources sources) := by
  cases sources with
  | nil => exact DeclarativeContextOfConstitutionalSeedSources.empty
  | cons head tail =>
      cases observed : input.firstDistinctConstitutionalSeedSource? head tail with
      | none =>
          simpa [officialContextOfConstitutionalSeedSources, observed] using
            (DeclarativeContextOfConstitutionalSeedSources.firstOnly
              (input := input) observed)
      | some other =>
          simpa [officialContextOfConstitutionalSeedSources, observed] using
            (DeclarativeContextOfConstitutionalSeedSources.firstPair
              (input := input) observed)

/-- Perceive a Rules-4a/4b/5 context directly from the complete provenance tree of one ligand.
Key construction is total at the proved finite bound; `none` therefore means that an encountered
tetrahedral source lacked a constitution-only exact descriptor. -/
def perceiveConstitutionalSeedContextAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    Option CIPRuleEngine.OfficialLigandRuleContext := do
  let key ← input.buildExecutableOfficialRuleMajorKey
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center index))
  let sources ← input.constitutionalSeedSources? key.sourceNodes
  some (input.officialContextOfConstitutionalSeedSources sources)

/-- Independent molecule-derived context relation.  The branch is recursively and completely
expanded; every provenance node is accounted for by fail-closed seed extraction; and the context
is relationally assembled from those justified molecular occurrences. -/
def DeclarativeConstitutionalSeedContextAt
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (context : CIPRuleEngine.OfficialLigandRuleContext) : Prop :=
  ∃ layers sources,
    input.DeclarativeRuleMajorLigandExpansion center index layers ∧
    input.DeclarativeConstitutionalSeedExtraction
      (input.addressedSourceNodeList layers) sources ∧
    DeclarativeContextOfConstitutionalSeedSources input sources context

/-- Every automatically perceived localized context has a complete recursive molecular-source
derivation.  It is no longer an arbitrary caller-supplied Rules-4/5 value. -/
theorem perceiveConstitutionalSeedContextAt?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (context : CIPRuleEngine.OfficialLigandRuleContext)
    (computed : input.perceiveConstitutionalSeedContextAt? center index = some context) :
    input.DeclarativeConstitutionalSeedContextAt center index context := by
  unfold perceiveConstitutionalSeedContextAt? at computed
  cases keyComputed : input.buildExecutableOfficialRuleMajorKey
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index)) with
  | none => simp [keyComputed] at computed
  | some key =>
      cases sourcesComputed : input.constitutionalSeedSources? key.sourceNodes with
      | none => simp [keyComputed, sourcesComputed] at computed
      | some sources =>
          simp [keyComputed, sourcesComputed] at computed
          subst context
          refine ⟨key.sourceNodes, sources,
            input.buildExecutableOfficialRuleMajorKey_declarative_default
              center index key keyComputed, ?_,
            input.officialContextOfConstitutionalSeedSources_declarative sources⟩
          exact input.collectConstitutionalSeedSources?_sound
            (input.addressedSourceNodeList key.sourceNodes) sources sourcesComputed

/-- Perceive all four ligand contexts for one localized center.  This is deliberately all-or-none:
if any branch contains an unresolved tetrahedral source, no context function is returned. -/
def perceiveConstitutionalSeedContextsAt?
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) :
    Option (Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) := do
  let context0 ← input.perceiveConstitutionalSeedContextAt? center 0
  let context1 ← input.perceiveConstitutionalSeedContextAt? center 1
  let context2 ← input.perceiveConstitutionalSeedContextAt? center 2
  let context3 ← input.perceiveConstitutionalSeedContextAt? center 3
  some ![context0, context1, context2, context3]

/-- Every component of a successfully perceived four-ligand context function is independently
derived from its own complete molecular provenance tree. -/
theorem perceiveConstitutionalSeedContextsAt?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (computed : input.perceiveConstitutionalSeedContextsAt? center = some context) :
    ∀ index, input.DeclarativeConstitutionalSeedContextAt center index (context index) := by
  unfold perceiveConstitutionalSeedContextsAt? at computed
  cases context0Computed : input.perceiveConstitutionalSeedContextAt? center 0 with
  | none => simp [context0Computed] at computed
  | some context0 =>
      cases context1Computed : input.perceiveConstitutionalSeedContextAt? center 1 with
      | none => simp [context0Computed, context1Computed] at computed
      | some context1 =>
          cases context2Computed : input.perceiveConstitutionalSeedContextAt? center 2 with
          | none =>
              simp [context0Computed, context1Computed, context2Computed] at computed
          | some context2 =>
              cases context3Computed : input.perceiveConstitutionalSeedContextAt? center 3 with
              | none =>
                  simp [context0Computed, context1Computed, context2Computed,
                    context3Computed] at computed
              | some context3 =>
                  simp [context0Computed, context1Computed, context2Computed,
                    context3Computed] at computed
                  subst context
                  intro index
                  fin_cases index
                  · exact input.perceiveConstitutionalSeedContextAt?_sound
                      center 0 context0 context0Computed
                  · exact input.perceiveConstitutionalSeedContextAt?_sound
                      center 1 context1 context1Computed
                  · exact input.perceiveConstitutionalSeedContextAt?_sound
                      center 2 context2 context2Computed
                  · exact input.perceiveConstitutionalSeedContextAt?_sound
                      center 3 context3 context3Computed

/-- Safe uppercase localized descriptor assignment with molecule-derived Rules-4a/4b/5 contexts.

The current localized output type is `RS`, so this entry point additionally requires an exact
constitution-only descriptor for the final center and agreement with the context-aware result.
That guard prevents a center whose priority is created only by Rule 5 from being mislabeled with
uppercase `R/S`; such a center must eventually be routed through the lowercase `r/s` pipeline. -/
def perceivedRuleMajorTetrahedralSpatialDescriptorAt?
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) : Option RS := do
  let context ← input.perceiveConstitutionalSeedContextsAt? center
  let contextualDescriptor ← input.ruleMajorTetrahedralSpatialDescriptorAt? center context
  let constitutionalDescriptor ← input.constitutionalSeedDescriptorAt? center
  if contextualDescriptor = constitutionalDescriptor then some constitutionalDescriptor else none

/-- Independent end-to-end relation for the molecule-derived context pass.  Every ligand context
has its own complete fail-closed perception derivation, and the final descriptor has the existing
recursive rule-major priority and exact rational-geometry derivation under those contexts. -/
def DeclarativePerceivedRuleMajorLocalizedTetrahedralDescriptor
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (descriptor : RS) : Prop :=
  ∃ context,
    (∀ index,
      input.DeclarativeConstitutionalSeedContextAt center index (context index)) ∧
    input.DeclarativeConstitutionalSeedDescriptor center descriptor ∧
    input.DeclarativeRuleMajorLocalizedTetrahedralDescriptor center context descriptor

/-- An emitted descriptor from the automatic pass is justified both at the molecule-to-context
boundary and at the context-to-priority-to-geometry boundary. -/
theorem perceivedRuleMajorTetrahedralSpatialDescriptorAt?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (descriptor : RS)
    (emitted : input.perceivedRuleMajorTetrahedralSpatialDescriptorAt? center =
      some descriptor) :
    input.DeclarativePerceivedRuleMajorLocalizedTetrahedralDescriptor center descriptor := by
  unfold perceivedRuleMajorTetrahedralSpatialDescriptorAt? at emitted
  cases contextComputed : input.perceiveConstitutionalSeedContextsAt? center with
  | none => simp [contextComputed] at emitted
  | some context =>
      cases contextualComputed :
          input.ruleMajorTetrahedralSpatialDescriptorAt? center context with
      | none => simp [contextComputed, contextualComputed] at emitted
      | some contextualDescriptor =>
          cases constitutionalComputed : input.constitutionalSeedDescriptorAt? center with
          | none =>
              simp [contextComputed, constitutionalComputed] at emitted
          | some constitutionalDescriptor =>
              by_cases same : contextualDescriptor = constitutionalDescriptor
              · simp [contextComputed, contextualComputed, constitutionalComputed, same] at emitted
                subst descriptor
                subst contextualDescriptor
                exact ⟨context,
                  input.perceiveConstitutionalSeedContextsAt?_sound
                    center context contextComputed,
                  input.constitutionalSeedDescriptorAt?_sound
                    center constitutionalDescriptor constitutionalComputed,
                  input.ruleMajorTetrahedralSpatialDescriptorAt?_sound_declarative
                    center context constitutionalDescriptor contextualComputed⟩
              · simp [contextComputed, contextualComputed, constitutionalComputed, same] at emitted

/-- Whole-molecule uppercase analyzer whose later-rule contexts are produced from molecular
evidence rather than supplied by the caller. Unresolved source perception, unresolved
constitution-only final priority, contextual disagreement, or final priority failure refuses
locally. -/
def analyzePerceivedRuleMajorTetrahedralSpatial
    (input : CertifiedLocalizedCIPInput) :
    List (LocalizedTetrahedralSpatialAssignment input) :=
  input.canonicalTetrahedralCenters.filterMap fun center =>
    (input.perceivedRuleMajorTetrahedralSpatialDescriptorAt? center).map fun descriptor =>
      { center := center, descriptor := descriptor }

theorem mem_analyzePerceivedRuleMajorTetrahedralSpatial_iff
    (input : CertifiedLocalizedCIPInput)
    (assignment : LocalizedTetrahedralSpatialAssignment input) :
    assignment ∈ input.analyzePerceivedRuleMajorTetrahedralSpatial ↔
      input.perceivedRuleMajorTetrahedralSpatialDescriptorAt? assignment.center =
        some assignment.descriptor := by
  constructor
  · intro present
    rw [analyzePerceivedRuleMajorTetrahedralSpatial, List.mem_filterMap] at present
    obtain ⟨center, _centerPresent, assignmentObserved⟩ := present
    cases descriptorObserved :
        input.perceivedRuleMajorTetrahedralSpatialDescriptorAt? center with
    | none => simp [descriptorObserved] at assignmentObserved
    | some descriptor =>
        simp [descriptorObserved] at assignmentObserved
        subst assignment
        exact descriptorObserved
  · intro emitted
    rw [analyzePerceivedRuleMajorTetrahedralSpatial, List.mem_filterMap]
    refine ⟨assignment.center, ?_, ?_⟩
    · exact (input.mem_canonicalTetrahedralCenters_iff assignment.center).mpr
        assignment.center.2
    · simp [emitted]

/-- Every emitted whole-molecule uppercase assignment has molecule-derived later-rule context
evidence, an independent constitution-only final descriptor, recursive context-aware priority
evidence, direct semantic coordinates, and exact determinant-sign evidence. -/
theorem analyzePerceivedRuleMajorTetrahedralSpatial_member_conforms_declarative
    (input : CertifiedLocalizedCIPInput)
    (assignment : LocalizedTetrahedralSpatialAssignment input)
    (present : assignment ∈ input.analyzePerceivedRuleMajorTetrahedralSpatial) :
    input.DeclarativePerceivedRuleMajorLocalizedTetrahedralDescriptor
      assignment.center assignment.descriptor := by
  apply input.perceivedRuleMajorTetrahedralSpatialDescriptorAt?_sound
  exact (input.mem_analyzePerceivedRuleMajorTetrahedralSpatial_iff assignment).mp present

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
