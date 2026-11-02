import TetraStereo.OneCenter.AuthoritativeSemanticOpenCumuleneFiniteCompleteness
import TetraStereo.OneCenter.AuthoritativeSemanticOpenCumuleneExactOnceCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Computed terminal data and terminal-free open-cumulene readiness

The finite-completeness evidence records of
`AuthoritativeSemanticOpenCumuleneFiniteCompleteness` take the terminal pair `terminals` and its
declarative extraction proof `terminalsDerived` from the caller. That proof already forces exact
agreement with the terminal selector. This module derives extraction totality and removes the
redundant caller-supplied pair and its extraction proof.  For every canonical enumerated open unit the
terminal pair is read *literally* out of `aromaticCanonicalOpenCumuleneTerminals?` with
`Option.get` at the derived `isSome` witness, its declarative refinement is proved, and the
remaining readiness fields are re-exposed as an explicitly named residual.

What is *not* removed: the endpoint Rules-1a--5 key/index dependency, the Rule-5 strict-selection
existence, and the nondegenerate exact-geometry obligations stay explicit, because they are
source-policy and geometric residuals rather than consequences of canonical ownership.  The
terminal-free constructors therefore do not, and do not pretend to, establish universal priority
or geometry readiness.

This is the represented open-cumulene domain only.  Fully cyclic cumulenes remain governed by the
separate P-93 nonterminal descriptor policy boundary and are not addressed here.
-/

/-! ## Literal terminal extraction from the canonical unit list -/

/-- The executable terminal extractor accepts every canonical enumerated open unit.  This is the
`isSome` witness used to read the pair back with `Option.get` instead of `Classical.choose`. -/
theorem computedAromaticCanonicalOpenCumuleneTerminals_isSome
    (source : AuthoritativeChemicalInput)
    (route : BlueBookP93.Acyclic.DoubleBondAnalysisRoute)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalOpenCumuleneUnits route) :
    (source.aromaticCanonicalOpenCumuleneTerminals? unit).isSome = true :=
  Option.isSome_iff_exists.mpr
    (source.exists_aromaticCanonicalOpenCumuleneTerminals?_of_mem_openCumuleneUnits
      route unit owner)

/-- The literal terminal pair of a canonical enumerated open unit, read out of the executable
extractor at the derived `isSome` witness.  `Option.get` returns the computed pair; it is not an
arbitrary chooser witness. -/
noncomputable def computedAromaticCanonicalOpenCumuleneTerminals
    (source : AuthoritativeChemicalInput)
    (route : BlueBookP93.Acyclic.DoubleBondAnalysisRoute)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalOpenCumuleneUnits route) :
    source.AromaticCanonicalOpenCumuleneTerminals :=
  (source.aromaticCanonicalOpenCumuleneTerminals? unit).get
    (source.computedAromaticCanonicalOpenCumuleneTerminals_isSome route unit owner)

/-- The executable extractor returns exactly the literal computed pair. -/
theorem computedAromaticCanonicalOpenCumuleneTerminals_spec
    (source : AuthoritativeChemicalInput)
    (route : BlueBookP93.Acyclic.DoubleBondAnalysisRoute)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalOpenCumuleneUnits route) :
    source.aromaticCanonicalOpenCumuleneTerminals? unit =
      some (source.computedAromaticCanonicalOpenCumuleneTerminals route unit owner) :=
  (Option.some_get
    (source.computedAromaticCanonicalOpenCumuleneTerminals_isSome route unit owner)).symm

/-- Refinement of the literal computed pair to the independent declarative terminal meaning. -/
theorem computedAromaticCanonicalOpenCumuleneTerminals_declarative
    (source : AuthoritativeChemicalInput)
    (route : BlueBookP93.Acyclic.DoubleBondAnalysisRoute)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalOpenCumuleneUnits route) :
    source.DeclarativeAromaticCanonicalOpenCumuleneTerminals unit
      (source.computedAromaticCanonicalOpenCumuleneTerminals route unit owner) :=
  (source.aromaticCanonicalOpenCumuleneTerminals?_eq_some_iff unit _).mp
    (source.computedAromaticCanonicalOpenCumuleneTerminals_spec route unit owner)

/-! ## Route-specialized computed terminals -/

/-- The literal terminal pair of a canonical odd-open-cumulene unit. -/
noncomputable def computedAromaticCanonicalOddOpenCumuleneTerminals
    (source : AuthoritativeChemicalInput)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits) :
    source.AromaticCanonicalOpenCumuleneTerminals :=
  source.computedAromaticCanonicalOpenCumuleneTerminals .oddOpenCumulene unit owner

/-- The literal terminal pair of a canonical even-open-cumulene unit. -/
noncomputable def computedAromaticCanonicalEvenOpenCumuleneTerminals
    (source : AuthoritativeChemicalInput)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits) :
    source.AromaticCanonicalOpenCumuleneTerminals :=
  source.computedAromaticCanonicalOpenCumuleneTerminals .evenOpenCumulene unit owner

/-- The odd extractor returns exactly the literal computed odd pair. -/
theorem computedAromaticCanonicalOddOpenCumuleneTerminals_spec
    (source : AuthoritativeChemicalInput)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits) :
    source.aromaticCanonicalOpenCumuleneTerminals? unit =
      some (source.computedAromaticCanonicalOddOpenCumuleneTerminals unit owner) :=
  source.computedAromaticCanonicalOpenCumuleneTerminals_spec .oddOpenCumulene unit owner

/-- The even extractor returns exactly the literal computed even pair. -/
theorem computedAromaticCanonicalEvenOpenCumuleneTerminals_spec
    (source : AuthoritativeChemicalInput)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits) :
    source.aromaticCanonicalOpenCumuleneTerminals? unit =
      some (source.computedAromaticCanonicalEvenOpenCumuleneTerminals unit owner) :=
  source.computedAromaticCanonicalOpenCumuleneTerminals_spec .evenOpenCumulene unit owner

/-- Declarative refinement of the literal computed odd pair. -/
theorem computedAromaticCanonicalOddOpenCumuleneTerminals_declarative
    (source : AuthoritativeChemicalInput)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits) :
    source.DeclarativeAromaticCanonicalOpenCumuleneTerminals unit
      (source.computedAromaticCanonicalOddOpenCumuleneTerminals unit owner) :=
  source.computedAromaticCanonicalOpenCumuleneTerminals_declarative .oddOpenCumulene unit owner

/-- Declarative refinement of the literal computed even pair. -/
theorem computedAromaticCanonicalEvenOpenCumuleneTerminals_declarative
    (source : AuthoritativeChemicalInput)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits) :
    source.DeclarativeAromaticCanonicalOpenCumuleneTerminals unit
      (source.computedAromaticCanonicalEvenOpenCumuleneTerminals unit owner) :=
  source.computedAromaticCanonicalOpenCumuleneTerminals_declarative .evenOpenCumulene unit owner

/-! ## Residual obligations that canonical ownership does not discharge

The following two records are exactly the parts of the finite-completeness evidence that are *not*
recovered from canonical ownership.  They are tagged by kind:

* endpoint Rules-1a--5 key/index dependency (`...DependenciesResolved`) and Rule-5 strict-selection
  existence (`...Selectable`) are **source-policy residuals**: they need a source clause that ranks
  the endpoint ligands and selects the strict reference;
* `spatiallyNondegenerate` is a **geometry residual**: it needs exact terminal/reference coordinates
  whose Rule-3/Rule-5 geometry is not `nonstereogenic`.

Neither residual is implied by membership in the canonical open-unit list. -/

/-- Residual endpoint-key, strict-selection and nondegenerate-geometry obligations of one odd
open-cumulene carrier, stated against a *given* terminal pair. -/
structure AromaticCanonicalOddOpenCumuleneEndpointResidual
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals) : Prop where
  leftDependencies :
    source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5DependenciesResolved
      carrierFuel terminals.left terminals.leftPartner
  rightDependencies :
    source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5DependenciesResolved
      carrierFuel terminals.right terminals.rightPartner
  leftSelectable : ∀ frame,
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel terminals.left terminals.leftPartner
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel terminals.left)
        (2 * (carrierFuel + 1)) frame →
      ∃ selection,
        source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
          frame selection
  rightSelectable : ∀ frame,
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel terminals.right terminals.rightPartner
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel terminals.right)
        (2 * (carrierFuel + 1)) frame →
      ∃ selection,
        source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
          frame selection
  spatiallyNondegenerate :
    ∀ (leftFrame rightFrame :
        source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame carrierFuel)
      (leftSelection rightSelection :
        source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection carrierFuel),
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        leftFrame leftSelection →
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
          rightFrame rightSelection →
      ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint geometry,
        source.SemanticAromaticCanonicalSpatialPointAt terminals.left leftPoint ∧
        source.SemanticAromaticCanonicalSpatialPointAt terminals.right rightPoint ∧
        source.SemanticAromaticCanonicalSpatialPointAt
          leftSelection.reference leftReferencePoint ∧
        source.SemanticAromaticCanonicalSpatialPointAt
          rightSelection.reference rightReferencePoint ∧
        RationalRule3SpatialGeometry leftPoint rightPoint
          leftReferencePoint rightReferencePoint geometry ∧
        geometry ≠ OfficialRule3Geometry.nonstereogenic

/-- Residual endpoint-key, strict-selection and nondegenerate-geometry obligations of one even
open-cumulene carrier, stated against a *given* terminal pair. -/
structure AromaticCanonicalEvenOpenCumuleneEndpointResidual
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals) : Prop where
  startDependencies :
    source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5DependenciesResolved
      carrierFuel terminals.left terminals.leftPartner
  endDependencies :
    source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5DependenciesResolved
      carrierFuel terminals.right terminals.rightPartner
  startSelectable : ∀ frame,
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel terminals.left terminals.leftPartner
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel terminals.left)
        (2 * (carrierFuel + 1)) frame →
      ∃ selection,
        source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
          frame selection
  endSelectable : ∀ frame,
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel terminals.right terminals.rightPartner
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel terminals.right)
        (2 * (carrierFuel + 1)) frame →
      ∃ selection,
        source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
          frame selection
  spatiallyNondegenerate :
    ∀ (startFrame endFrame :
        source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame carrierFuel)
      (startSelection endSelection :
        source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection carrierFuel),
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        startFrame startSelection →
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
          endFrame endSelection →
      ∃ axisStartPoint axisEndPoint startReferencePoint endReferencePoint descriptor,
        source.SemanticAromaticCanonicalSpatialPointAt terminals.left axisStartPoint ∧
        source.SemanticAromaticCanonicalSpatialPointAt terminals.right axisEndPoint ∧
        source.SemanticAromaticCanonicalSpatialPointAt
          startSelection.reference startReferencePoint ∧
        source.SemanticAromaticCanonicalSpatialPointAt
          endSelection.reference endReferencePoint ∧
        RationalAxialSpatialDescriptor axisStartPoint axisEndPoint
          startReferencePoint endReferencePoint descriptor

/-! ## Terminal-free smart constructors -/

/-- Build the odd finite-completeness evidence without a caller-supplied terminal pair: the pair is
the literal computed one, its declarative refinement is derived, and only the residual
endpoint-key/selection/geometry obligations remain as inputs. -/
noncomputable def aromaticCanonicalOddOpenCumuleneAutomaticDependencyEvidence_of_computed
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits)
    (residual : source.AromaticCanonicalOddOpenCumuleneEndpointResidual carrierFuel ruleFuel
      (source.computedAromaticCanonicalOddOpenCumuleneTerminals unit owner)) :
    source.AromaticCanonicalOddOpenCumuleneAutomaticDependencyEvidence carrierFuel ruleFuel unit
      (source.computedAromaticCanonicalOddOpenCumuleneTerminals unit owner) where
  owner := owner
  terminalsDerived :=
    source.computedAromaticCanonicalOddOpenCumuleneTerminals_declarative unit owner
  leftDependencies := residual.leftDependencies
  rightDependencies := residual.rightDependencies
  leftSelectable := residual.leftSelectable
  rightSelectable := residual.rightSelectable
  spatiallyNondegenerate := residual.spatiallyNondegenerate

/-- Build the even finite-completeness evidence without a caller-supplied terminal pair; the
terminal half is derived exactly as for the odd route. -/
noncomputable def aromaticCanonicalEvenOpenCumuleneAutomaticDependencyEvidence_of_computed
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits)
    (residual : source.AromaticCanonicalEvenOpenCumuleneEndpointResidual carrierFuel ruleFuel
      (source.computedAromaticCanonicalEvenOpenCumuleneTerminals unit owner)) :
    source.AromaticCanonicalEvenOpenCumuleneAutomaticDependencyEvidence carrierFuel ruleFuel unit
      (source.computedAromaticCanonicalEvenOpenCumuleneTerminals unit owner) where
  owner := owner
  terminalsDerived :=
    source.computedAromaticCanonicalEvenOpenCumuleneTerminals_declarative unit owner
  startDependencies := residual.startDependencies
  endDependencies := residual.endDependencies
  startSelectable := residual.startSelectable
  endSelectable := residual.endSelectable
  spatiallyNondegenerate := residual.spatiallyNondegenerate

/-! ## Terminal-free family readiness

`AromaticCanonicalOpenCumuleneComputedReadiness` is the terminal-free restatement of the odd/even
conjuncts of the molecule-level readiness contract: it quantifies only the residual obligations.
The bridge lemma recovers the original `∃ terminals, evidence` shape with the *computed* terminal
pair, so the terminal witness is no longer an independent assumption. -/

/-- Terminal-free readiness of both canonical open-cumulene families.  It mentions no terminal
witness: for each canonical unit it asks only for the residual endpoint-policy and geometry
obligations against the computed pair. -/
structure AromaticCanonicalOpenCumuleneComputedReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) : Prop where
  odd : ∀ (unit : List source.AromaticCanonicalAtom)
      (owner : unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits),
    source.AromaticCanonicalOddOpenCumuleneEndpointResidual carrierFuel ruleFuel
      (source.computedAromaticCanonicalOddOpenCumuleneTerminals unit owner)
  even : ∀ (unit : List source.AromaticCanonicalAtom)
      (owner : unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits),
    source.AromaticCanonicalEvenOpenCumuleneEndpointResidual carrierFuel ruleFuel
      (source.computedAromaticCanonicalEvenOpenCumuleneTerminals unit owner)

/-- Terminal-free readiness recovers the original `∃ terminals, evidence` conjuncts, with the
terminal pair supplied by the computed extractor rather than by the caller. -/
theorem exists_terminalEvidence_of_computedReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (ready : source.AromaticCanonicalOpenCumuleneComputedReadiness carrierFuel ruleFuel) :
    (∀ unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits,
        ∃ terminals,
          source.AromaticCanonicalOddOpenCumuleneAutomaticDependencyEvidence
            carrierFuel ruleFuel unit terminals) ∧
      (∀ unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits,
        ∃ terminals,
          source.AromaticCanonicalEvenOpenCumuleneAutomaticDependencyEvidence
            carrierFuel ruleFuel unit terminals) := by
  constructor
  · intro unit owner
    exact
      ⟨source.computedAromaticCanonicalOddOpenCumuleneTerminals unit owner,
        source.aromaticCanonicalOddOpenCumuleneAutomaticDependencyEvidence_of_computed
          carrierFuel ruleFuel unit owner (ready.odd unit owner)⟩
  · intro unit owner
    exact
      ⟨source.computedAromaticCanonicalEvenOpenCumuleneTerminals unit owner,
        source.aromaticCanonicalEvenOpenCumuleneAutomaticDependencyEvidence_of_computed
          carrierFuel ruleFuel unit owner (ready.even unit owner)⟩

/-- Existing odd evidence uses exactly the computed terminals; transport only its residual fields. -/
theorem oddEndpointResidual_of_dependencyEvidence
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals)
    (evidence : source.AromaticCanonicalOddOpenCumuleneAutomaticDependencyEvidence
      carrierFuel ruleFuel unit terminals) :
    source.AromaticCanonicalOddOpenCumuleneEndpointResidual carrierFuel ruleFuel
      (source.computedAromaticCanonicalOddOpenCumuleneTerminals unit owner) := by
  have original := (source.aromaticCanonicalOpenCumuleneTerminals?_eq_some_iff unit terminals).mpr
    evidence.terminalsDerived
  have equality : terminals = source.computedAromaticCanonicalOddOpenCumuleneTerminals unit owner :=
    Option.some.inj (original.symm.trans
      (source.computedAromaticCanonicalOddOpenCumuleneTerminals_spec unit owner))
  subst terminals
  exact ⟨evidence.leftDependencies, evidence.rightDependencies, evidence.leftSelectable,
    evidence.rightSelectable, evidence.spatiallyNondegenerate⟩

/-- Existing even evidence uses exactly the computed terminals; transport only its residual fields. -/
theorem evenEndpointResidual_of_dependencyEvidence
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals)
    (evidence : source.AromaticCanonicalEvenOpenCumuleneAutomaticDependencyEvidence
      carrierFuel ruleFuel unit terminals) :
    source.AromaticCanonicalEvenOpenCumuleneEndpointResidual carrierFuel ruleFuel
      (source.computedAromaticCanonicalEvenOpenCumuleneTerminals unit owner) := by
  have original := (source.aromaticCanonicalOpenCumuleneTerminals?_eq_some_iff unit terminals).mpr
    evidence.terminalsDerived
  have equality : terminals = source.computedAromaticCanonicalEvenOpenCumuleneTerminals unit owner :=
    Option.some.inj (original.symm.trans
      (source.computedAromaticCanonicalEvenOpenCumuleneTerminals_spec unit owner))
  subst terminals
  exact ⟨evidence.startDependencies, evidence.endDependencies, evidence.startSelectable,
    evidence.endSelectable, evidence.spatiallyNondegenerate⟩

/-- Converse of the terminal-free family readiness bridge; no scientific premise is strengthened. -/
theorem computedReadiness_of_exists_terminalEvidence
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (odd : ∀ unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits,
      ∃ terminals, source.AromaticCanonicalOddOpenCumuleneAutomaticDependencyEvidence
        carrierFuel ruleFuel unit terminals)
    (even : ∀ unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits,
      ∃ terminals, source.AromaticCanonicalEvenOpenCumuleneAutomaticDependencyEvidence
        carrierFuel ruleFuel unit terminals) :
    source.AromaticCanonicalOpenCumuleneComputedReadiness carrierFuel ruleFuel where
  odd := fun unit owner => by
    obtain ⟨terminals, evidence⟩ := odd unit owner
    exact source.oddEndpointResidual_of_dependencyEvidence carrierFuel ruleFuel unit owner
      terminals evidence
  even := fun unit owner => by
    obtain ⟨terminals, evidence⟩ := even unit owner
    exact source.evenEndpointResidual_of_dependencyEvidence carrierFuel ruleFuel unit owner
      terminals evidence

/-- Exact equivalence to the existing sufficient readiness, not to arbitrary analyzer success. -/
theorem computedReadiness_iff_terminalEvidence
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalOpenCumuleneComputedReadiness carrierFuel ruleFuel ↔
      ((∀ unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits,
        ∃ terminals, source.AromaticCanonicalOddOpenCumuleneAutomaticDependencyEvidence
          carrierFuel ruleFuel unit terminals) ∧
       (∀ unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits,
        ∃ terminals, source.AromaticCanonicalEvenOpenCumuleneAutomaticDependencyEvidence
          carrierFuel ruleFuel unit terminals)) :=
  ⟨source.exists_terminalEvidence_of_computedReadiness carrierFuel ruleFuel,
    fun evidence => source.computedReadiness_of_exists_terminalEvidence carrierFuel ruleFuel
      evidence.1 evidence.2⟩

/-! ## Downstream analyzer existence / literal count one

Feeding the constructed evidence into the existing exact-once API yields an actual analyzer
existence-and-count-one result.  Only the residual obligations remain as hypotheses. -/

/-- Under the odd residual obligations, the whole-molecule odd analyzer emits the unit exactly
once. -/
theorem exists_count_analyzeAromaticCanonicalOddOpenCumuleneSpatial_eq_one_of_computedResidual
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits)
    (residual : source.AromaticCanonicalOddOpenCumuleneEndpointResidual carrierFuel ruleFuel
      (source.computedAromaticCanonicalOddOpenCumuleneTerminals unit owner)) :
    ∃ assignment,
      assignment.unit = unit ∧
        (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
          carrierFuel ruleFuel).count assignment = 1 :=
  source.exists_count_analyzeAromaticCanonicalOddOpenCumuleneSpatial_eq_one_of_dependencies
    carrierFuel ruleFuel unit
    (source.computedAromaticCanonicalOddOpenCumuleneTerminals unit owner)
    (source.aromaticCanonicalOddOpenCumuleneAutomaticDependencyEvidence_of_computed
      carrierFuel ruleFuel unit owner residual)

/-- Under the even residual obligations, the whole-molecule even analyzer emits the unit exactly
once. -/
theorem exists_count_analyzeAromaticCanonicalEvenOpenCumuleneAxial_eq_one_of_computedResidual
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits)
    (residual : source.AromaticCanonicalEvenOpenCumuleneEndpointResidual carrierFuel ruleFuel
      (source.computedAromaticCanonicalEvenOpenCumuleneTerminals unit owner)) :
    ∃ assignment,
      assignment.unit = unit ∧
        (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
          carrierFuel ruleFuel).count assignment = 1 :=
  source.exists_count_analyzeAromaticCanonicalEvenOpenCumuleneAxial_eq_one_of_dependencies
    carrierFuel ruleFuel unit
    (source.computedAromaticCanonicalEvenOpenCumuleneTerminals unit owner)
    (source.aromaticCanonicalEvenOpenCumuleneAutomaticDependencyEvidence_of_computed
      carrierFuel ruleFuel unit owner residual)

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
