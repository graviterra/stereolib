import TetraStereo.OneCenter.P91DescriptorSyntax

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Executable P-91 descriptor-name annotation

P-91 treats stereodescriptors as annotations on a base name and numbering that already exist.
This module implements exactly that layer for numeric locants: it validates descriptor
applicability, orders citations by locant, refuses duplicate locants, chooses the source-prescribed
parent/component placement, and renders the descriptor prefix.  It deliberately does not invent
the underlying systematic base name or numbering.
-/

namespace IUPACBlueBookP91.ExecutableNaming

open BlueBookP91

/-- One requested numeric descriptor citation. -/
structure NamingCitation where
  locant : Nat
  kind : StereogenicUnitKind
  descriptor : Descriptor
  deriving DecidableEq, Repr

/-- P-91 annotation request over an already selected base name. -/
structure NamingRequest where
  baseName : String
  target : NameTarget String
  scope? : Option ScopeQualifier := none
  citations : List NamingCitation
  deriving DecidableEq, Repr

def descriptorApplies? : Descriptor → StereogenicUnitKind → Bool
  | .capitalR, .quadriligantChiralityCenter
  | .capitalS, .quadriligantChiralityCenter
  | .lowercaseR, .pseudoasymmetricCenter
  | .lowercaseS, .pseudoasymmetricCenter
  | .capitalM, .axialHelicityEntity
  | .capitalP, .axialHelicityEntity
  | .capitalM, .planarHelicityEntity
  | .capitalP, .planarHelicityEntity
  | .lowercaseM, .pseudoasymmetricAxialHelicityEntity
  | .lowercaseP, .pseudoasymmetricAxialHelicityEntity
  | .lowercaseM, .pseudoasymmetricPlanarHelicityEntity
  | .lowercaseP, .pseudoasymmetricPlanarHelicityEntity
  | .seqCis, .enantiomorphicDoubleBond
  | .seqTrans, .enantiomorphicDoubleBond
  | .axialR, .chiralityAxis
  | .axialS, .chiralityAxis
  | .planarR, .chiralityPlane
  | .planarS, .chiralityPlane
  | .pseudoAxialR, .pseudoasymmetricAxis
  | .pseudoAxialS, .pseudoasymmetricAxis
  | .pseudoPlanarR, .pseudoasymmetricPlane
  | .pseudoPlanarS, .pseudoasymmetricPlane
  | .capitalE, .diastereomorphicTwoEndedUnsaturation
  | .capitalZ, .diastereomorphicTwoEndedUnsaturation
  | .capitalA, .pentaligantCenter
  | .capitalC, .pentaligantCenter
  | .capitalA, .hexaligantCenter
  | .capitalC, .hexaligantCenter => true
  | _, _ => false

@[simp] theorem descriptorApplies?_eq_true_iff
    (descriptor : Descriptor) (kind : StereogenicUnitKind) :
    descriptorApplies? descriptor kind = true ↔ DescriptorApplies descriptor kind := by
  cases descriptor <;> cases kind <;> simp [descriptorApplies?, DescriptorApplies]

def citationLocantLE (left right : NamingCitation) : Prop := left.locant ≤ right.locant

instance citationLocantLEDecidable (left right : NamingCitation) :
    Decidable (citationLocantLE left right) := by
  unfold citationLocantLE
  infer_instance

/-- Structurally recursive, kernel-reducible locant ordering. -/
def orderedCitations (request : NamingRequest) : List NamingCitation :=
  request.citations.insertionSort citationLocantLE

def StrictlyIncreasingLocants : List NamingCitation → Prop
  | [] | [_] => True
  | first :: second :: remaining =>
      first.locant < second.locant ∧
        StrictlyIncreasingLocants (second :: remaining)

def strictlyIncreasingLocants? : List NamingCitation → Bool
  | [] | [_] => true
  | first :: second :: remaining =>
      decide (first.locant < second.locant) &&
        strictlyIncreasingLocants? (second :: remaining)

@[simp] theorem strictlyIncreasingLocants?_eq_true_iff
    (citations : List NamingCitation) :
    strictlyIncreasingLocants? citations = true ↔ StrictlyIncreasingLocants citations := by
  induction citations with
  | nil => simp [strictlyIncreasingLocants?, StrictlyIncreasingLocants]
  | cons first remaining inductionHypothesis =>
      cases remaining with
      | nil => simp [strictlyIncreasingLocants?, StrictlyIncreasingLocants]
      | cons second tail =>
          simp [strictlyIncreasingLocants?, StrictlyIncreasingLocants,
            inductionHypothesis]

theorem strictlyIncreasingLocants_pairwise (citations : List NamingCitation)
    (strict : StrictlyIncreasingLocants citations) :
    citations.Pairwise fun left right => left.locant < right.locant := by
  induction citations with
  | nil => simp
  | cons first remaining inductionHypothesis =>
      cases remaining with
      | nil => simp
      | cons second tail =>
          have firstSecond : first.locant < second.locant := strict.1
          have remainingPairwise :
              (second :: tail).Pairwise fun left right => left.locant < right.locant :=
            inductionHypothesis strict.2
          have secondBeforeTail := (List.pairwise_cons.mp remainingPairwise).1
          rw [List.pairwise_cons]
          refine ⟨?_, remainingPairwise⟩
          simp only [List.mem_cons]
          intro later choice
          rcases choice with equality | member
          · subst later
            exact firstSecond
          · exact Nat.lt_trans firstSecond (secondBeforeTail later member)

def NamingRequestReady (request : NamingRequest) : Prop :=
  request.citations ≠ [] ∧
    (∀ citation ∈ request.citations,
      DescriptorApplies citation.descriptor citation.kind) ∧
    StrictlyIncreasingLocants (orderedCitations request)

def namingRequestReady? (request : NamingRequest) : Bool :=
  !request.citations.isEmpty &&
    request.citations.all (fun citation =>
      descriptorApplies? citation.descriptor citation.kind) &&
    strictlyIncreasingLocants? (orderedCitations request)

@[simp] theorem namingRequestReady?_eq_true_iff (request : NamingRequest) :
    namingRequestReady? request = true ↔ NamingRequestReady request := by
  simp [namingRequestReady?, NamingRequestReady, and_assoc]

def citationPosition (target : NameTarget String) : CitationPosition String :=
  match target with
  | .parent => .frontOfCompleteName
  | .substituent component => .frontOfPrefix component

def compileCitation (target : NameTarget String)
    (citation : NamingCitation) : DescriptorCitation Nat String :=
  { descriptor := citation.descriptor
    locant := some citation.locant
    target := target
    position := citationPosition target
    parenthesizedAndHyphenated := true }

def locatedCitation (target : NameTarget String)
    (citation : NamingCitation) : LocatedDescriptorCitation Nat String :=
  { descriptor := citation.descriptor
    locant := citation.locant
    target := target }

theorem namingRequestReady_inIncreasingLocantOrder (request : NamingRequest)
    (ready : NamingRequestReady request) :
    InIncreasingLocantOrder
      ((orderedCitations request).map (locatedCitation request.target)) := by
  have pairwise := strictlyIncreasingLocants_pairwise _ ready.2.2
  unfold InIncreasingLocantOrder
  rw [List.pairwise_map]
  simpa [locatedCitation] using pairwise

theorem compileCitation_correctPlacement (target : NameTarget String)
    (citation : NamingCitation) :
    CorrectCitationPlacement (compileCitation target citation) := by
  cases target <;> simp [compileCitation, citationPosition, CorrectCitationPlacement]

def scopePrefix : Option ScopeQualifier → String
  | none => ""
  | some .relative => "rel-"
  | some .racemic => "rac-"

def renderCitation (citation : NamingCitation) : String :=
  toString citation.locant ++ citation.descriptor.symbol

def renderDescriptorPrefix (request : NamingRequest) : String :=
  scopePrefix request.scope? ++ "(" ++
    String.intercalate "," ((orderedCitations request).map renderCitation) ++ ")-"

/-- Result of the descriptor-annotation layer. -/
structure CompiledName where
  name : AnnotatedName String Unit Nat String
  target : NameTarget String
  scope? : Option ScopeQualifier
  orderedCitations : List NamingCitation
  descriptorPrefix : String

def compiledName (request : NamingRequest) : CompiledName :=
  let ordered := orderedCitations request
  { name :=
      { baseName := request.baseName
        numbering := ()
        citations := ordered.map (compileCitation request.target) }
    target := request.target
    scope? := request.scope?
    orderedCitations := ordered
    descriptorPrefix := renderDescriptorPrefix request }

/-- Independent specification of successful P-91 annotation. -/
def NamingCompilationJudgment (request : NamingRequest) (compiled : CompiledName) : Prop :=
  NamingRequestReady request ∧ compiled = compiledName request

def compileName? (request : NamingRequest) : Option CompiledName :=
  if namingRequestReady? request then some (compiledName request) else none

theorem compileName?_eq_some_iff (request : NamingRequest) (compiled : CompiledName) :
    compileName? request = some compiled ↔ NamingCompilationJudgment request compiled := by
  unfold NamingCompilationJudgment
  by_cases checked : namingRequestReady? request = true
  · have ready : NamingRequestReady request :=
      (namingRequestReady?_eq_true_iff request).mp checked
    constructor
    · intro computed
      have equality : compiledName request = compiled := by
        exact Option.some.inj (by simpa [compileName?, checked] using computed)
      exact ⟨ready, equality.symm⟩
    · rintro ⟨_, rfl⟩
      simp [compileName?, checked]
  · have notReady : ¬NamingRequestReady request := by
      intro ready
      exact checked ((namingRequestReady?_eq_true_iff request).mpr ready)
    simp [compileName?, checked, notReady]

theorem compileName?_eq_none_iff (request : NamingRequest) :
    compileName? request = none ↔ ¬NamingRequestReady request := by
  rw [← namingRequestReady?_eq_true_iff]
  simp [compileName?]

theorem compiledName_all_citations_correctlyPlaced (request : NamingRequest)
    (citation : DescriptorCitation Nat String)
    (member : citation ∈ (compiledName request).name.citations) :
    CorrectCitationPlacement citation := by
  simp [compiledName] at member
  rcases member with ⟨source, _, rfl⟩
  exact compileCitation_correctPlacement request.target source

@[simp] theorem compiledName_preserves_baseName (request : NamingRequest) :
    (compiledName request).name.baseName = request.baseName :=
  rfl

end IUPACBlueBookP91.ExecutableNaming

end TetraStereo.OneCenter
