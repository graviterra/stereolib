import TetraStereo.OneCenter.AuthoritativeLocalizedCIPAnalysis
import TetraStereo.OneCenter.ExactOfficialRuleMajorKey
import TetraStereo.OneCenter.OfficialRuleMajorKey
import TetraStereo.OneCenter.SemanticLocalizedMancudeFiniteRealization

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Rule-major comparison for authoritative localized inputs

This is the replacement constitutional path for the older local-per-node hierarchy comparator.
It compiles each ligand independently through the executable semantic child enumerator, compares
the resulting parent-addressed projections in exhaustive Rule 1a → Rule 1b → Rule 2 order, and
consults the supplied Rule 3/4/5 context only after the complete constitutional trace ties.
-/

namespace CertifiedLocalizedCIPInput

/-- Executable exact-rational, arbitrary-width rule-major key for one branch root. -/
def buildExecutableExactOfficialRuleMajorKey (input : CertifiedLocalizedCIPInput)
    (fuel : ℕ) (node : OfficialCIPNode input.Atom) :
    Option (ExactOfficialRuleMajorKey input.Atom) :=
  input.moleculeGraph.buildObservedExactOfficialRuleMajorKey
    input.certified.input.molecule.semanticExactOfficialRule1aObservation
    input.executableOfficialCIPChildren fuel node

/-- The executable finite observation used by the exact key is extensionally the independent
maximum-matching observation. -/
theorem executableExactOfficialRule1aObservation_correct
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) :
    input.certified.input.molecule.semanticExactOfficialRule1aObservation node =
      input.moleculeGraph.exactOfficialRule1aObservation node :=
  input.certified.input.molecule.semanticExactOfficialRule1aObservation_eq_independent node

/-- Independent exact-rational recursive provenance-tree semantics for one canonical ligand. -/
def DeclarativeExactRuleMajorLigandExpansion (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (sources : OfficialRuleMajorKey.AddressedSourceLayers input.Atom) : Prop :=
  ExactOfficialRuleMajorKey.DeclarativeAddressedExpansion input.moleculeGraph
    input.executableOfficialCIPChildren
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index)) sources

/-- Executable, arbitrary-width rule-major key for one provenance-bearing branch root. -/
def buildExecutableOfficialRuleMajorKey (input : CertifiedLocalizedCIPInput)
    (fuel : ℕ) (node : OfficialCIPNode input.Atom) :
    Option (OfficialRuleMajorKey input.Atom) :=
  input.moleculeGraph.buildOfficialRuleMajorKey
    input.executableOfficialCIPChildren fuel node

/-- Independent recursive provenance-tree semantics for one executable canonical ligand root. -/
def DeclarativeRuleMajorLigandExpansion (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (sources : OfficialRuleMajorKey.AddressedSourceLayers input.Atom) : Prop :=
  OfficialRuleMajorKey.DeclarativeAddressedExpansion input.moleculeGraph
    input.executableOfficialCIPChildren
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index)) sources

/-- Every executable key is exactly aligned with fresh observations from its addressed provenance
nodes, for arbitrary fuel and root. -/
theorem buildExecutableOfficialRuleMajorKey_sourceAligned
    (input : CertifiedLocalizedCIPInput) (fuel : ℕ)
    (node : OfficialCIPNode input.Atom) (key : OfficialRuleMajorKey input.Atom)
    (computed : input.buildExecutableOfficialRuleMajorKey fuel node = some key) :
    OfficialRuleMajorKey.SourceAligned input.moleculeGraph key := by
  unfold buildExecutableOfficialRuleMajorKey at computed
  exact input.moleculeGraph.buildOfficialRuleMajorKey_sourceAligned
    input.executableOfficialCIPChildren fuel node key computed

/-- A canonical ligand is distinct from its center because it is connected by a positive graph
bond and the certified molecular graph has no self-bonds. -/
theorem canonicalLigandAtom_ne_center (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    input.canonicalLigandAtom center index ≠ center.1 := by
  intro equality
  have adjacent := input.canonicalLigandAtom_adj center index
  rw [equality] at adjacent
  simp [MoleculeGraph.Adj, input.moleculeGraph.bond_self] at adjacent

/-- The executable canonical child enumeration exhausts every ordinary ligand branch within the
default finite-atom depth bound. Enumeration permutation cannot change this property. -/
theorem executableOfficialExpansionCompleteWithin_default
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    MoleculeGraph.OfficialExpansionCompleteWithin input.executableOfficialCIPChildren
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index)) := by
  have reference := input.moleculeGraph.officialExpansionCompleteWithin_rootFromEdge_default
    (input.canonicalLigandAtom_ne_center center index)
  have same := MoleculeGraph.officialExpansionCompleteWithin_iff_of_children_perm
    input.executableOfficialCIPChildren input.moleculeGraph.officialCIPChildren
    input.executableOfficialCIPChildren_perm_officialCIPChildren
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index))
  apply same.mpr
  simpa using reference

/-- Default-fuel executable key construction succeeds and marks every canonical ligand key
complete. This removes fuel exhaustion as a possible refusal on admitted finite inputs. -/
theorem buildExecutableOfficialRuleMajorKey_complete_default
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    ∃ key,
      input.buildExecutableOfficialRuleMajorKey
        (input.certified.input.molecule.atomCount + 1)
        (OfficialCIPNode.rootFromEdge center.1
          (input.canonicalLigandAtom center index)) = some key ∧
      key.complete = true := by
  unfold buildExecutableOfficialRuleMajorKey
  exact input.moleculeGraph.buildOfficialRuleMajorKey_complete_of_expansionCompleteWithin
    input.executableOfficialCIPChildren
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index))
    (input.executableOfficialExpansionCompleteWithin_default center index)

/-- The exact-rational compiler is total and complete at the same proved finite-atom bound. -/
theorem buildExecutableExactOfficialRuleMajorKey_complete_default
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    ∃ key,
      input.buildExecutableExactOfficialRuleMajorKey
        (input.certified.input.molecule.atomCount + 1)
        (OfficialCIPNode.rootFromEdge center.1
          (input.canonicalLigandAtom center index)) = some key ∧
      key.complete = true := by
  unfold buildExecutableExactOfficialRuleMajorKey
  rw [input.moleculeGraph.buildObservedExactOfficialRuleMajorKey_eq_exact
    input.certified.input.molecule.semanticExactOfficialRule1aObservation
    input.executableExactOfficialRule1aObservation_correct
    input.executableOfficialCIPChildren]
  exact input.moleculeGraph.buildExactOfficialRuleMajorKey_complete_of_expansionCompleteWithin
    input.executableOfficialCIPChildren
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index))
    (input.executableOfficialExpansionCompleteWithin_default center index)

/-- The source tree produced at the proved default bound satisfies the independent recursive
addressed-expansion semantics. -/
theorem buildExecutableOfficialRuleMajorKey_declarative_default
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (key : OfficialRuleMajorKey input.Atom)
    (computed : input.buildExecutableOfficialRuleMajorKey
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index)) = some key) :
    input.DeclarativeRuleMajorLigandExpansion center index key.sourceNodes := by
  unfold DeclarativeRuleMajorLigandExpansion
  unfold buildExecutableOfficialRuleMajorKey at computed
  exact input.moleculeGraph.buildOfficialRuleMajorKey_declarativeAddressedExpansion
    input.executableOfficialCIPChildren
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index)) key computed

/-- Every exact-rational compiler result satisfies the independent recursive addressed-tree
semantics. -/
theorem buildExecutableExactOfficialRuleMajorKey_declarative_default
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (key : ExactOfficialRuleMajorKey input.Atom)
    (computed : input.buildExecutableExactOfficialRuleMajorKey
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index)) = some key) :
    input.DeclarativeExactRuleMajorLigandExpansion center index key.sourceNodes := by
  unfold DeclarativeExactRuleMajorLigandExpansion
  unfold buildExecutableExactOfficialRuleMajorKey at computed
  rw [input.moleculeGraph.buildObservedExactOfficialRuleMajorKey_eq_exact
    input.certified.input.molecule.semanticExactOfficialRule1aObservation
    input.executableExactOfficialRule1aObservation_correct
    input.executableOfficialCIPChildren] at computed
  exact input.moleculeGraph.buildExactOfficialRuleMajorKey_declarativeAddressedExpansion
    input.executableOfficialCIPChildren
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index)) key computed

/-- Safe constitutional comparison of two detected-center ligands. -/
def compareRuleMajorConstitutionAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4) :
    Option CIPTraceCertificate := do
  let fuel := input.certified.input.molecule.atomCount + 1
  let leftKey ← input.buildExecutableExactOfficialRuleMajorKey fuel
    (OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center left))
  let rightKey ← input.buildExecutableExactOfficialRuleMajorKey fuel
    (OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center right))
  let _ ← ExactOfficialRuleMajorKey.compareObserved? input.moleculeGraph
    input.certified.input.molecule.semanticExactOfficialRule1aObservation leftKey rightKey
  some (CIPTraceCertificate.ofTrace
    (ExactOfficialRuleMajorKey.compareTraceObserved input.moleculeGraph
      input.certified.input.molecule.semanticExactOfficialRule1aObservation leftKey rightKey))

/-- Independent constitutional specification: both ligand provenance trees satisfy recursive
expansion, and the rule-tagged trace is freshly read from those nodes in Rule 1a → 1b → 2 order. -/
def DeclarativeRuleMajorConstitutionalTrace
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (trace : List CIPRuleDecision) : Prop :=
  ∃ leftSources rightSources,
    input.DeclarativeExactRuleMajorLigandExpansion center left leftSources ∧
    input.DeclarativeExactRuleMajorLigandExpansion center right rightSources ∧
    ExactOfficialRuleMajorKey.compareAddressedSourceTrace input.moleculeGraph
      leftSources rightSources = trace

/-- Every executable constitutional certificate has an independent recursive-expansion witness
and exactly the freshly interpreted rule-major trace. -/
theorem compareRuleMajorConstitutionAt?_sound_declarative_trace
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (certificate : CIPTraceCertificate)
    (computed : input.compareRuleMajorConstitutionAt? center left right =
      some certificate) :
    input.DeclarativeRuleMajorConstitutionalTrace center left right
      certificate.trace := by
  unfold compareRuleMajorConstitutionAt? at computed
  cases leftComputed : input.buildExecutableExactOfficialRuleMajorKey
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center left)) with
  | none => simp [leftComputed] at computed
  | some leftKey =>
      cases rightComputed : input.buildExecutableExactOfficialRuleMajorKey
          (input.certified.input.molecule.atomCount + 1)
          (OfficialCIPNode.rootFromEdge center.1
            (input.canonicalLigandAtom center right)) with
      | none => simp [leftComputed, rightComputed] at computed
      | some rightKey =>
          cases compared : ExactOfficialRuleMajorKey.compareObserved?
              input.moleculeGraph
              input.certified.input.molecule.semanticExactOfficialRule1aObservation
              leftKey rightKey with
          | none => simp [leftComputed, rightComputed, compared] at computed
          | some outcome =>
              simp [leftComputed, rightComputed, compared] at computed
              subst certificate
              refine ⟨leftKey.sourceNodes, rightKey.sourceNodes,
                input.buildExecutableExactOfficialRuleMajorKey_declarative_default
                  center left leftKey leftComputed,
                input.buildExecutableExactOfficialRuleMajorKey_declarative_default
                  center right rightKey rightComputed, ?_⟩
              exact (ExactOfficialRuleMajorKey.compareAddressedSourceTraceObserved_eq_exact
                input.moleculeGraph
                input.certified.input.molecule.semanticExactOfficialRule1aObservation
                input.executableExactOfficialRule1aObservation_correct
                leftKey.sourceNodes rightKey.sourceNodes).symm

/-- Constitutional comparison never refuses for canonical ligands of an admitted finite input:
both branch keys are proved complete and complete keys are always safely comparable. -/
theorem compareRuleMajorConstitutionAt?_isSome
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4) :
    (input.compareRuleMajorConstitutionAt? center left right).isSome = true := by
  obtain ⟨leftKey, leftComputed, leftComplete⟩ :=
    input.buildExecutableExactOfficialRuleMajorKey_complete_default center left
  obtain ⟨rightKey, rightComputed, rightComplete⟩ :=
    input.buildExecutableExactOfficialRuleMajorKey_complete_default center right
  have exactComparisonExists := ExactOfficialRuleMajorKey.compare?_isSome_of_complete
    input.moleculeGraph leftKey rightKey leftComplete rightComplete
  have comparisonExists :
      (ExactOfficialRuleMajorKey.compareObserved? input.moleculeGraph
        input.certified.input.molecule.semanticExactOfficialRule1aObservation
        leftKey rightKey).isSome = true := by
    rw [ExactOfficialRuleMajorKey.compareObserved?_eq_exact input.moleculeGraph
      input.certified.input.molecule.semanticExactOfficialRule1aObservation
      input.executableExactOfficialRule1aObservation_correct]
    exact exactComparisonExists
  obtain ⟨outcome, comparisonComputed⟩ := Option.isSome_iff_exists.mp comparisonExists
  simp [compareRuleMajorConstitutionAt?, leftComputed, rightComputed, comparisonComputed]

/-- Rule-major constitutional comparison followed by the existing explicit Rule 3/4/5 context.
Failure to build or safely compare either unary key is preserved as `none`. -/
def compareRuleMajorAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (left right : Fin 4) : Option CIPTraceCertificate := do
  let constitutional ← input.compareRuleMajorConstitutionAt? center left right
  some (CIPRuleEngine.compareDigraphThenOfficialCertificate constitutional.trace
    (context left) (context right))

/-- Full localized comparison specification at the current explicit context boundary: the
constitutional trace comes from independent recursive provenance expansion, then the existing
official Rules 3--5 context semantics is consulted only through the common trace combiner. -/
def DeclarativeRuleMajorOutcome (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (left right : Fin 4) (outcome : Ordering) : Prop :=
  ∃ constitutionalTrace,
    input.DeclarativeRuleMajorConstitutionalTrace center left right constitutionalTrace ∧
    cipTraceOutcome (CIPRuleEngine.compareDigraphThenOfficialTrace constitutionalTrace
      (context left) (context right)) = outcome

/-- Every comparison certificate emitted by the localized rule-major path satisfies the full
declarative outcome relation. -/
theorem compareRuleMajorAt?_sound_declarative
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (left right : Fin 4) (certificate : CIPTraceCertificate)
    (computed : input.compareRuleMajorAt? center context left right = some certificate) :
    input.DeclarativeRuleMajorOutcome center context left right certificate.outcome := by
  unfold compareRuleMajorAt? at computed
  cases constitutionalComputed : input.compareRuleMajorConstitutionAt? center left right with
  | none => simp [constitutionalComputed] at computed
  | some constitutional =>
      simp [constitutionalComputed] at computed
      subst certificate
      refine ⟨constitutional.trace,
        input.compareRuleMajorConstitutionAt?_sound_declarative_trace
          center left right constitutional constitutionalComputed, ?_⟩
      rfl

/-- Adding the supplied later-rule context cannot introduce failure after the constitutional
comparison, so every canonical ligand pair has a comparison certificate. -/
theorem compareRuleMajorAt?_isSome (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (left right : Fin 4) :
    (input.compareRuleMajorAt? center context left right).isSome = true := by
  obtain ⟨constitutional, computed⟩ := Option.isSome_iff_exists.mp
    (input.compareRuleMajorConstitutionAt?_isSome center left right)
  simp [compareRuleMajorAt?, computed]

/-- A strict Rule-1a difference at the real ligand roots decides the exhaustive rule-major path.
The theorem uses only the proved root retention, branch completeness, and normative rule order;
deeper spheres and the supplied later-rule context cannot override the result. -/
theorem compareRuleMajorAt?_outcome_lt_of_root_atomicNumber_lt
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (left right : Fin 4)
    (lower :
      (input.certified.input.molecule.atoms.get
        (input.canonicalLigandAtom center left)).element.atomicNumber <
      (input.certified.input.molecule.atoms.get
        (input.canonicalLigandAtom center right)).element.atomicNumber) :
    (input.compareRuleMajorAt? center context left right).map
      CIPTraceCertificate.outcome = some Ordering.lt := by
  obtain ⟨leftKey, leftComputed, leftComplete⟩ :=
    input.buildExecutableExactOfficialRuleMajorKey_complete_default center left
  obtain ⟨rightKey, rightComputed, rightComplete⟩ :=
    input.buildExecutableExactOfficialRuleMajorKey_complete_default center right
  have leftReferenceComputed :
      input.moleculeGraph.buildExactOfficialRuleMajorKey
        input.executableOfficialCIPChildren
        (input.certified.input.molecule.atomCount + 1)
        (OfficialCIPNode.rootFromEdge center.1
          (input.canonicalLigandAtom center left)) = some leftKey := by
    rw [← input.moleculeGraph.buildObservedExactOfficialRuleMajorKey_eq_exact
      input.certified.input.molecule.semanticExactOfficialRule1aObservation
      input.executableExactOfficialRule1aObservation_correct
      input.executableOfficialCIPChildren]
    exact leftComputed
  have rightReferenceComputed :
      input.moleculeGraph.buildExactOfficialRuleMajorKey
        input.executableOfficialCIPChildren
        (input.certified.input.molecule.atomCount + 1)
        (OfficialCIPNode.rootFromEdge center.1
          (input.canonicalLigandAtom center right)) = some rightKey := by
    rw [← input.moleculeGraph.buildObservedExactOfficialRuleMajorKey_eq_exact
      input.certified.input.molecule.semanticExactOfficialRule1aObservation
      input.executableExactOfficialRule1aObservation_correct
      input.executableOfficialCIPChildren]
    exact rightComputed
  have leftSourceHead := input.moleculeGraph.buildExactOfficialRuleMajorKey_sourceNodes_head
    input.executableOfficialCIPChildren
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center left)) leftKey leftReferenceComputed
  have rightSourceHead := input.moleculeGraph.buildExactOfficialRuleMajorKey_sourceNodes_head
    input.executableOfficialCIPChildren
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center right)) rightKey rightReferenceComputed
  have leftHead :
      (ExactOfficialRuleMajorKey.exactRule1aLayers input.moleculeGraph
        leftKey.sourceNodes).head? =
        some [([], .ofNat (input.moleculeGraph.atomZ
          (input.canonicalLigandAtom center left)))] := by
    simpa using ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head
      input.moleculeGraph leftKey.sourceNodes
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center left)) leftSourceHead
  have rightHead :
      (ExactOfficialRuleMajorKey.exactRule1aLayers input.moleculeGraph
        rightKey.sourceNodes).head? =
        some [([], .ofNat (input.moleculeGraph.atomZ
          (input.canonicalLigandAtom center right)))] := by
    simpa using ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head
      input.moleculeGraph rightKey.sourceNodes
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center right)) rightSourceHead
  have rootLower : input.moleculeGraph.atomZ (input.canonicalLigandAtom center left) <
      input.moleculeGraph.atomZ (input.canonicalLigandAtom center right) := by
    simpa [CertifiedLocalizedCIPInput.moleculeGraph,
      SemanticMolecule.toLocalizedMoleculeGraph] using lower
  have rule1a : OfficialRuleMajorKey.compareSparseLayers
      ExactOfficialRuleMajorKey.compareExactAtomicNumber
      (ExactOfficialRuleMajorKey.exactRule1aLayers input.moleculeGraph leftKey.sourceNodes)
      (ExactOfficialRuleMajorKey.exactRule1aLayers input.moleculeGraph rightKey.sourceNodes) =
        Ordering.lt :=
    ExactOfficialRuleMajorKey.compareSparseExactRule1a_lt_of_heads_lt
      leftHead rightHead rootLower
  have exactCompared : ExactOfficialRuleMajorKey.compare?
      input.moleculeGraph leftKey rightKey = some Ordering.lt := by
    simp [ExactOfficialRuleMajorKey.compare?, rule1a]
  have compared : ExactOfficialRuleMajorKey.compareObserved? input.moleculeGraph
      input.certified.input.molecule.semanticExactOfficialRule1aObservation
      leftKey rightKey = some Ordering.lt := by
    rw [ExactOfficialRuleMajorKey.compareObserved?_eq_exact input.moleculeGraph
      input.certified.input.molecule.semanticExactOfficialRule1aObservation
      input.executableExactOfficialRule1aObservation_correct]
    exact exactCompared
  have exactTraceOutcome : cipTraceOutcome
      (ExactOfficialRuleMajorKey.compareTrace input.moleculeGraph leftKey rightKey) =
        Ordering.lt := by
    simp [ExactOfficialRuleMajorKey.compareTrace,
      ExactOfficialRuleMajorKey.compareAddressedSourceTrace, rule1a]
  have traceOutcome : cipTraceOutcome
      (ExactOfficialRuleMajorKey.compareTraceObserved input.moleculeGraph
        input.certified.input.molecule.semanticExactOfficialRule1aObservation
        leftKey rightKey) = Ordering.lt := by
    rw [ExactOfficialRuleMajorKey.compareTraceObserved_eq_exact input.moleculeGraph
      input.certified.input.molecule.semanticExactOfficialRule1aObservation
      input.executableExactOfficialRule1aObservation_correct]
    exact exactTraceOutcome
  simp [compareRuleMajorAt?, compareRuleMajorConstitutionAt?, leftComputed,
    rightComputed, compared]
  change cipTraceOutcome (CIPRuleEngine.compareDigraphThenOfficialTrace
    (ExactOfficialRuleMajorKey.compareTraceObserved input.moleculeGraph
      input.certified.input.molecule.semanticExactOfficialRule1aObservation leftKey rightKey)
    (context left) (context right)) = Ordering.lt
  rw [CIPRuleEngine.compareDigraphThenOfficialTrace_outcome_of_digraph_ne_eq
    (by simp [traceOutcome])]
  exact traceOutcome

/-- The symmetric strict Rule-1a root case decides the exhaustive rule-major path as greater. -/
theorem compareRuleMajorAt?_outcome_gt_of_root_atomicNumber_gt
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (left right : Fin 4)
    (higher :
      (input.certified.input.molecule.atoms.get
        (input.canonicalLigandAtom center right)).element.atomicNumber <
      (input.certified.input.molecule.atoms.get
        (input.canonicalLigandAtom center left)).element.atomicNumber) :
    (input.compareRuleMajorAt? center context left right).map
      CIPTraceCertificate.outcome = some Ordering.gt := by
  obtain ⟨leftKey, leftComputed, leftComplete⟩ :=
    input.buildExecutableExactOfficialRuleMajorKey_complete_default center left
  obtain ⟨rightKey, rightComputed, rightComplete⟩ :=
    input.buildExecutableExactOfficialRuleMajorKey_complete_default center right
  have leftReferenceComputed :
      input.moleculeGraph.buildExactOfficialRuleMajorKey
        input.executableOfficialCIPChildren
        (input.certified.input.molecule.atomCount + 1)
        (OfficialCIPNode.rootFromEdge center.1
          (input.canonicalLigandAtom center left)) = some leftKey := by
    rw [← input.moleculeGraph.buildObservedExactOfficialRuleMajorKey_eq_exact
      input.certified.input.molecule.semanticExactOfficialRule1aObservation
      input.executableExactOfficialRule1aObservation_correct
      input.executableOfficialCIPChildren]
    exact leftComputed
  have rightReferenceComputed :
      input.moleculeGraph.buildExactOfficialRuleMajorKey
        input.executableOfficialCIPChildren
        (input.certified.input.molecule.atomCount + 1)
        (OfficialCIPNode.rootFromEdge center.1
          (input.canonicalLigandAtom center right)) = some rightKey := by
    rw [← input.moleculeGraph.buildObservedExactOfficialRuleMajorKey_eq_exact
      input.certified.input.molecule.semanticExactOfficialRule1aObservation
      input.executableExactOfficialRule1aObservation_correct
      input.executableOfficialCIPChildren]
    exact rightComputed
  have leftSourceHead := input.moleculeGraph.buildExactOfficialRuleMajorKey_sourceNodes_head
    input.executableOfficialCIPChildren
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center left)) leftKey leftReferenceComputed
  have rightSourceHead := input.moleculeGraph.buildExactOfficialRuleMajorKey_sourceNodes_head
    input.executableOfficialCIPChildren
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center right)) rightKey rightReferenceComputed
  have leftHead :
      (ExactOfficialRuleMajorKey.exactRule1aLayers input.moleculeGraph
        leftKey.sourceNodes).head? =
        some [([], .ofNat (input.moleculeGraph.atomZ
          (input.canonicalLigandAtom center left)))] := by
    simpa using ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head
      input.moleculeGraph leftKey.sourceNodes
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center left)) leftSourceHead
  have rightHead :
      (ExactOfficialRuleMajorKey.exactRule1aLayers input.moleculeGraph
        rightKey.sourceNodes).head? =
        some [([], .ofNat (input.moleculeGraph.atomZ
          (input.canonicalLigandAtom center right)))] := by
    simpa using ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head
      input.moleculeGraph rightKey.sourceNodes
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center right)) rightSourceHead
  have rootHigher : input.moleculeGraph.atomZ (input.canonicalLigandAtom center right) <
      input.moleculeGraph.atomZ (input.canonicalLigandAtom center left) := by
    simpa [CertifiedLocalizedCIPInput.moleculeGraph,
      SemanticMolecule.toLocalizedMoleculeGraph] using higher
  have rule1a : OfficialRuleMajorKey.compareSparseLayers
      ExactOfficialRuleMajorKey.compareExactAtomicNumber
      (ExactOfficialRuleMajorKey.exactRule1aLayers input.moleculeGraph leftKey.sourceNodes)
      (ExactOfficialRuleMajorKey.exactRule1aLayers input.moleculeGraph rightKey.sourceNodes) =
        Ordering.gt :=
    ExactOfficialRuleMajorKey.compareSparseExactRule1a_gt_of_heads_gt
      leftHead rightHead rootHigher
  have exactCompared : ExactOfficialRuleMajorKey.compare?
      input.moleculeGraph leftKey rightKey = some Ordering.gt := by
    simp [ExactOfficialRuleMajorKey.compare?, rule1a]
  have compared : ExactOfficialRuleMajorKey.compareObserved? input.moleculeGraph
      input.certified.input.molecule.semanticExactOfficialRule1aObservation
      leftKey rightKey = some Ordering.gt := by
    rw [ExactOfficialRuleMajorKey.compareObserved?_eq_exact input.moleculeGraph
      input.certified.input.molecule.semanticExactOfficialRule1aObservation
      input.executableExactOfficialRule1aObservation_correct]
    exact exactCompared
  have exactTraceOutcome : cipTraceOutcome
      (ExactOfficialRuleMajorKey.compareTrace input.moleculeGraph leftKey rightKey) =
        Ordering.gt := by
    simp [ExactOfficialRuleMajorKey.compareTrace,
      ExactOfficialRuleMajorKey.compareAddressedSourceTrace, rule1a]
  have traceOutcome : cipTraceOutcome
      (ExactOfficialRuleMajorKey.compareTraceObserved input.moleculeGraph
        input.certified.input.molecule.semanticExactOfficialRule1aObservation
        leftKey rightKey) = Ordering.gt := by
    rw [ExactOfficialRuleMajorKey.compareTraceObserved_eq_exact input.moleculeGraph
      input.certified.input.molecule.semanticExactOfficialRule1aObservation
      input.executableExactOfficialRule1aObservation_correct]
    exact exactTraceOutcome
  simp [compareRuleMajorAt?, compareRuleMajorConstitutionAt?, leftComputed,
    rightComputed, compared]
  change cipTraceOutcome (CIPRuleEngine.compareDigraphThenOfficialTrace
    (ExactOfficialRuleMajorKey.compareTraceObserved input.moleculeGraph
      input.certified.input.molecule.semanticExactOfficialRule1aObservation leftKey rightKey)
    (context left) (context right)) = Ordering.gt
  rw [CIPRuleEngine.compareDigraphThenOfficialTrace_outcome_of_digraph_ne_eq
    (by simp [traceOutcome])]
  exact traceOutcome

/-- Comparing a canonical ligand with itself always produces an exact tie. This is proved from
the lawful total key comparator plus reflexivity of the independently supplied Rules 3--5
context, without evaluating a concrete molecule. -/
@[simp] theorem compareRuleMajorAt?_outcome_self
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (index : Fin 4) :
    (input.compareRuleMajorAt? center context index index).map
      CIPTraceCertificate.outcome = some Ordering.eq := by
  obtain ⟨key, keyComputed, keyComplete⟩ :=
    input.buildExecutableExactOfficialRuleMajorKey_complete_default center index
  have safeExists := ExactOfficialRuleMajorKey.compare?_isSome_of_complete
    input.moleculeGraph key key keyComplete keyComplete
  obtain ⟨outcome, safeComputed⟩ := Option.isSome_iff_exists.mp safeExists
  have totalSelf : ExactOfficialRuleMajorKey.compare input.moleculeGraph key key =
      Ordering.eq := by
    letI : Std.TransCmp (ExactOfficialRuleMajorKey.compare input.moleculeGraph) :=
      ExactOfficialRuleMajorKey.compare_transCmp input.moleculeGraph
    exact Std.ReflCmp.compare_self
  have safeOutcome : outcome = Ordering.eq := by
    have agrees := ExactOfficialRuleMajorKey.compare_eq_of_compare?_eq_some
      input.moleculeGraph key key outcome safeComputed
    exact agrees.symm.trans totalSelf
  subst outcome
  have safeObservedComputed : ExactOfficialRuleMajorKey.compareObserved?
      input.moleculeGraph
      input.certified.input.molecule.semanticExactOfficialRule1aObservation key key =
        some Ordering.eq := by
    rw [ExactOfficialRuleMajorKey.compareObserved?_eq_exact input.moleculeGraph
      input.certified.input.molecule.semanticExactOfficialRule1aObservation
      input.executableExactOfficialRule1aObservation_correct]
    exact safeComputed
  have exactTraceOutcome : cipTraceOutcome
      (ExactOfficialRuleMajorKey.compareTrace input.moleculeGraph key key) =
        Ordering.eq := by
    rw [ExactOfficialRuleMajorKey.compareTrace_outcome, totalSelf]
  have traceOutcome : cipTraceOutcome
      (ExactOfficialRuleMajorKey.compareTraceObserved input.moleculeGraph
        input.certified.input.molecule.semanticExactOfficialRule1aObservation key key) =
        Ordering.eq := by
    rw [ExactOfficialRuleMajorKey.compareTraceObserved_eq_exact input.moleculeGraph
      input.certified.input.molecule.semanticExactOfficialRule1aObservation
      input.executableExactOfficialRule1aObservation_correct]
    exact exactTraceOutcome
  simp [compareRuleMajorAt?, compareRuleMajorConstitutionAt?, keyComputed,
    safeObservedComputed]
  change cipTraceOutcome (CIPRuleEngine.compareDigraphThenOfficialTrace
    (ExactOfficialRuleMajorKey.compareTraceObserved input.moleculeGraph
      input.certified.input.molecule.semanticExactOfficialRule1aObservation key key)
    (context index) (context index)) = Ordering.eq
  rw [CIPRuleEngine.compareDigraphThenOfficialTrace_outcome_of_digraph_eq traceOutcome]
  exact CIPRuleEngine.compareOfficialContextTrace_self (context index)

/-- Deterministic ordering predicate. `none` and exact ties use atom-index position only; neither
case is chemically interpreted unless `ruleMajorResolvedAt?` succeeds. -/
def ruleMajorLigandBeforeAt (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (left right : Fin 4) : Bool :=
  match input.compareRuleMajorAt? center context left right with
  | none => decide (left ≤ right)
  | some certificate =>
      match certificate.outcome with
      | Ordering.gt => true
      | Ordering.lt => false
      | Ordering.eq => decide (left ≤ right)

def ruleMajorLigandOrderAt (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) : List (Fin 4) :=
  (List.finRange 4).mergeSort (input.ruleMajorLigandBeforeAt center context)

/-- A pair is strictly coherent with descending priority only when comparison succeeds and returns
`gt`; missing, tied, or lower comparisons all fail this check. -/
def ruleMajorOrderPairStrictAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (left right : Fin 4) : Bool :=
  match input.compareRuleMajorAt? center context left right with
  | none => false
  | some certificate => certificate.outcome == Ordering.gt

/-- Verify every earlier/later pair in a proposed list, not merely adjacent pairs. This rejects
cycles that can otherwise arise from inconsistent or partial externally supplied contexts. -/
def ruleMajorOrderCoherentListAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    List (Fin 4) → Bool
  | [] => true
  | left :: rest =>
      rest.all (input.ruleMajorOrderPairStrictAt? center context left) &&
        input.ruleMajorOrderCoherentListAt? center context rest

@[simp] theorem ruleMajorOrderPairStrictAt?_eq_true_iff
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (left right : Fin 4) :
    input.ruleMajorOrderPairStrictAt? center context left right = true ↔
      ∃ certificate,
        input.compareRuleMajorAt? center context left right = some certificate ∧
        certificate.outcome = Ordering.gt := by
  cases computed : input.compareRuleMajorAt? center context left right with
  | none => simp [ruleMajorOrderPairStrictAt?, computed]
  | some certificate => simp [ruleMajorOrderPairStrictAt?, computed]

theorem ruleMajorOrderCoherentListAt?_eq_true_iff
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    ∀ order,
      input.ruleMajorOrderCoherentListAt? center context order = true ↔
        order.Pairwise fun left right =>
          ∃ certificate,
            input.compareRuleMajorAt? center context left right = some certificate ∧
            certificate.outcome = Ordering.gt
  | [] => by simp [ruleMajorOrderCoherentListAt?]
  | left :: rest => by
      rw [ruleMajorOrderCoherentListAt?, Bool.and_eq_true, List.all_eq_true,
        List.pairwise_cons, ruleMajorOrderCoherentListAt?_eq_true_iff]
      constructor
      · rintro ⟨head, tail⟩
        exact ⟨fun right present =>
          (input.ruleMajorOrderPairStrictAt?_eq_true_iff
            center context left right).mp (head right present), tail⟩
      · rintro ⟨head, tail⟩
        exact ⟨fun right present =>
          (input.ruleMajorOrderPairStrictAt?_eq_true_iff
            center context left right).mpr (head right present), tail⟩

/-- Coherence of the concrete deterministic order returned by the sorter. -/
def ruleMajorOrderCoherentAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) : Bool :=
  input.ruleMajorOrderCoherentListAt? center context
    (input.ruleMajorLigandOrderAt center context)

/-- One pair is safely resolved precisely when key construction succeeds and the full comparison
is decisive. -/
def ruleMajorPairResolvedAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (left right : Fin 4) : Bool :=
  match input.compareRuleMajorAt? center context left right with
  | none => false
  | some certificate => certificate.outcome != Ordering.eq

/-- All six distinct ligand pairs must have successful, decisive rule-major comparisons. -/
def ruleMajorResolvedAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) : Bool :=
  (List.finRange 4).all fun left =>
    (List.finRange 4).all fun right =>
      decide (left = right) || input.ruleMajorPairResolvedAt? center context left right

/-- Tie-, failure-, and cycle-refusing rule-major ligand order. Pairwise decisiveness alone is not
enough when external later-rule contexts are partial, so the actual order is also checked against
all six earlier/later comparisons. -/
def ruleMajorLigandOrderAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    Option (List (Fin 4)) :=
  if input.ruleMajorResolvedAt? center context &&
      input.ruleMajorOrderCoherentAt? center context then
    some (input.ruleMajorLigandOrderAt center context)
  else none

@[simp] theorem ruleMajorPairResolvedAt?_eq_true_iff
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (left right : Fin 4) :
    input.ruleMajorPairResolvedAt? center context left right = true ↔
      ∃ certificate,
        input.compareRuleMajorAt? center context left right = some certificate ∧
          certificate.outcome ≠ Ordering.eq := by
  cases computed : input.compareRuleMajorAt? center context left right with
  | none => simp [ruleMajorPairResolvedAt?, computed]
  | some certificate => simp [ruleMajorPairResolvedAt?, computed]

theorem ruleMajorLigandOrderAt?_eq_some_iff
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (order : List (Fin 4)) :
    input.ruleMajorLigandOrderAt? center context = some order ↔
      input.ruleMajorResolvedAt? center context = true ∧
        input.ruleMajorOrderCoherentAt? center context = true ∧
        input.ruleMajorLigandOrderAt center context = order := by
  cases resolved : input.ruleMajorResolvedAt? center context <;>
    cases coherent : input.ruleMajorOrderCoherentAt? center context <;>
      simp [ruleMajorLigandOrderAt?, resolved, coherent]

/-- Independent priority-order specification: the list contains all four canonical ligands once,
and every earlier ligand has a declarative full-rule `gt` witness over recursive provenance trees. -/
def DeclarativeRuleMajorPriorityOrder (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (order : List (Fin 4)) : Prop :=
  order.Perm (List.finRange 4) ∧
    order.Pairwise fun left right =>
      input.DeclarativeRuleMajorOutcome center context left right Ordering.gt

/-- Every accepted safe order conforms to the independent recursive rule-major priority relation.
In particular, this theorem is false for a merely decisive cyclic tournament, which the new
coherence gate refuses. -/
theorem ruleMajorLigandOrderAt?_sound_declarative
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (order : List (Fin 4))
    (computed : input.ruleMajorLigandOrderAt? center context = some order) :
    input.DeclarativeRuleMajorPriorityOrder center context order := by
  have accepted := (input.ruleMajorLigandOrderAt?_eq_some_iff
    center context order).mp computed
  rcases accepted with ⟨_resolved, coherent, rfl⟩
  constructor
  · unfold ruleMajorLigandOrderAt
    exact List.mergeSort_perm _ _
  · exact ((input.ruleMajorOrderCoherentListAt?_eq_true_iff center context
      (input.ruleMajorLigandOrderAt center context)).mp coherent).imp (by
        rintro left right ⟨certificate, certificateComputed, outcome⟩
        rw [← outcome]
        exact input.compareRuleMajorAt?_sound_declarative center context
          left right certificate certificateComputed)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
