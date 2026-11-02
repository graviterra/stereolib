import TetraStereo.OneCenter.LocalizedRawGraphReadiness
import TetraStereo.OneCenter.LocalizedUniversalSemanticClosure
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Raw source admission into the unconditional universal reference closure

This module is the source-level endpoint that composes two already kernel-green developments:

* `TetraStereo.OneCenter.LocalizedRawGraphReadiness` derives the localized CIP graph domain
  directly from executable raw data (`RawLocalizedGraphSourceReady`) and constructs the actual
  `LocalizedReference.admitRawSpatial?` input, without assuming conversion, certification,
  graph readiness or admission success;
* `TetraStereo.OneCenter.LocalizedUniversalSemanticClosure` proves, for every existing
  `LocalizedUniversalReference.Input`, the unconditional exact-label semantics of the universal
  descriptor, the unique independent semantic reference model, and both pipeline branches'
  agreement with that model.

The endpoint theorem below starts **only** from

* a parsed `RawMolecule` satisfying `RawLocalizedGraphSourceReady`, and
* a spatial configuration with exactly one coordinate per parsed atom
  (`spatial.positions.length = molecule.atomCount`),

and derives the following in one statement, for the *same* admitted input:

1. the actual executable `LocalizedReference.admitRawSpatial?` returns `some input`;
2. the admitted input preserves the exact converted semantic molecule, the parser structure
   agreement, and the supplied spatial configuration;
3. the independent semantic reference model has a unique realizing state on that input, and the
   generated `LocalizedUniversalReference.referenceState` is a model (hence the unique one);
4. the actual runnable `LocalizedUniversalReference.evaluate` lookup is equivalent, pointwise, to
   the independent declarative universal-descriptor relation at its own dependency view.

## Domain constraint: fully materialized explicit graphs only

The preexisting conversion `RawMolecule.toSemanticMolecule?` reads only `molecule.atoms` and
`molecule.bonds`; it does **not** materialize hydrogens from `explicitHydrogens` metadata.  The
hypothesis `spatial.positions.length = molecule.atomCount` therefore asks for one coordinate per
*stored* atom, and the caller domain is a fully materialized explicit graph.  A caller starting
from a hydrogen-suppressed parse must first expand it (the production intake
`LocalizedReference.admitSmilesSpatial?` does this with `withExplicitHydrogens`).  This module
makes no claim that raw source materializes implicit hydrogens, and it introduces no such
hypothesis.

## Scope and residual chemical-fidelity obligations

This is a source-level constructor into the *existing formal semantics*, not a chemical
completeness theorem.  In particular:

* no claim is made that strict-depth dependency exclusion is chemically exhaustive;
* no claim is made that all organic stereochemistry is modeled or complete;
* `LocalizedCIPGraphReady` retains its existing genuine restrictions (explicit localized closed
  shells, positive-order two-atom pair records, frozen Rule-2 mass data, duplicate-free unordered
  endpoints); rings and double/triple bonds are retained wherever that predicate accepts them;
* an operational `none` remains an operational refusal, not a chemical nonexistence statement.

All residual chemical-fidelity obligations therefore remain exactly where the underlying
localized semantics leaves them.  Nothing below re-proves the generic fixed point, the ranked
invariants or the raw admission bridge; the existing statements are reused verbatim.
-/

namespace TetraStereo.OneCenter

namespace LocalizedRawUniversalReferenceClosure

open CertifiedLocalizedCIPInput TetraStereo.Certificate.Dependency

/-! ## The universal closure at an arbitrary admitted input

`LocalizedUniversalReference.Input` is definitionally the admitted `LocalizedReference.Input`
(through `LocalizedExtendedShortCircuit.Input`), so the unconditional closure can be stated on the
input produced by raw admission without any coercion. -/

/-- **Unconditional universal reference closure at a localized reference input.**

For any admitted input:

* the independent semantic reference model has a unique state;
* the generated `referenceState` realizes that model;
* every runnable `evaluate` result's lookup is pointwise equivalent to the independent
  declarative universal-descriptor relation at the result's own dependency view.

The existential uniqueness, the realization statement and the evaluator equivalence are the
already proved unconditional results of `LocalizedUniversalSemanticClosure`; this theorem only
packages them for the raw-admission endpoint below. -/
theorem universalReferenceClosure_of_input (input : LocalizedReference.Input) :
    (∃! state : input.certified.LocalizedAuxiliaryState
        (LocalizedUniversalReference.carrierFuel input),
      LocalizedUniversalReference.IndependentSemanticReferenceModel input state) ∧
      LocalizedUniversalReference.IndependentSemanticReferenceModel input
        (LocalizedUniversalReference.referenceState input) ∧
        (∀ (nodes : LocalizedUniversalReference.Nodes input)
            (target : LocalizedUniversalReference.Occurrence input)
            (descriptor : LocalizedAuxiliaryLabel),
          lookup
              (LocalizedUniversalReference.evaluate input nodes).facts target = some descriptor ↔
            ∃ evaluationBudget : Nat,
              input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
                (input.certified.localizedDependencyView
                  (lookup
                    (LocalizedUniversalReference.evaluate input nodes).facts) target)
                evaluationBudget descriptor) :=
  ⟨LocalizedUniversalReference.existsUnique_independentSemanticReferenceModel input,
    LocalizedUniversalReference.referenceState_realizes_independentSemanticReferenceModel input,
    fun nodes target descriptor =>
      LocalizedUniversalReference.evaluate_lookup_eq_some_iff_exists_declarativeUniversalDescriptor
        input nodes target descriptor⟩

/-! ## Raw source endpoint -/

/-- **Raw source admission into the unconditional universal reference closure.**

Given only the executable raw-source gate and one coordinate per parsed atom, the actual
`LocalizedReference.admitRawSpatial?` succeeds on a converted molecule that preserves the exact
semantic image, the parser structure agreement and the supplied spatial source; the admitted input
carries the unique independent semantic reference model realized by `referenceState`, and the
actual `evaluate` lookup is pointwise equivalent to the independent declarative universal
descriptor relation.

No conversion identity, graph-readiness proof, admission result, certificate or semantic model is
supplied: all of them are derived.  See the module docstring for the fully-materialized explicit
graph constraint and for the chemical-fidelity scope boundaries. -/
theorem rawSource_admits_universalReferenceClosure
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (rawReady : LocalizedRawGraphReadiness.RawLocalizedGraphSourceReady molecule)
    (spatialLength : spatial.positions.length = molecule.atomCount) :
    ∃ (semantic : SemanticMolecule) (input : LocalizedReference.Input),
      molecule.toSemanticMolecule? = some semantic ∧
        LocalizedReference.admitRawSpatial? molecule spatial = some input ∧
          input.certified.certified.input.molecule = semantic ∧
            molecule.AuthoritativeStructureAgreement input.certified.certified.input ∧
              input.certified.certified.input.spatial? = some spatial ∧
                (∃! state : input.certified.LocalizedAuxiliaryState
                    (LocalizedUniversalReference.carrierFuel input),
                  LocalizedUniversalReference.IndependentSemanticReferenceModel input state) ∧
                  LocalizedUniversalReference.IndependentSemanticReferenceModel input
                    (LocalizedUniversalReference.referenceState input) ∧
                    (∀ (nodes : LocalizedUniversalReference.Nodes input)
                        (target : LocalizedUniversalReference.Occurrence input)
                        (descriptor : LocalizedAuxiliaryLabel),
                      lookup
                          (LocalizedUniversalReference.evaluate input nodes).facts target =
                        some descriptor ↔
                        ∃ evaluationBudget : Nat,
                          input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
                            (input.certified.localizedDependencyView
                              (lookup
                                (LocalizedUniversalReference.evaluate input nodes).facts) target)
                            evaluationBudget descriptor) := by
  obtain ⟨semantic, input, converted, admitted, moleculeEq, agreement, spatialEq⟩ :=
    LocalizedRawGraphReadiness.admitRawSpatial?_of_raw molecule spatial rawReady spatialLength
  obtain ⟨uniqueModel, realized, evaluatorEquivalence⟩ :=
    universalReferenceClosure_of_input input
  exact ⟨semantic, input, converted, admitted, moleculeEq, agreement, spatialEq,
    uniqueModel, realized, evaluatorEquivalence⟩

end LocalizedRawUniversalReferenceClosure

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawUniversalReferenceClosure.universalReferenceClosure_of_input
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawUniversalReferenceClosure.rawSource_admits_universalReferenceClosure
