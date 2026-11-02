import TetraStereo.Certificate.Dependency

set_option autoImplicit false

namespace TetraStereo.Certificate.DependencySource

open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.DeclarativeCIP.OccurrenceScheduler
open TetraStereo.Certificate.Dependency

universe u v w
variable {FinalUnit : Type u} {Occurrence : Type v} {Label : Type w}

/-! A source adapter can interpret finite checked derivations without asserting that
every arbitrary runtime state already satisfies chemical semantics. The independent
meaning is preserved locally from meaningful dependencies. No final model or desired
outcome is supplied by the certificate. This also covers genuinely checked `none`.
-/

theorem certificate_source_sound
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence)
    (Meaning : Occurrence → Option Label → Prop)
    (localSound : ∀ target (inputs : ∀ inner, relation dependencies inner target → Option Label),
      (∀ inner h, Meaning inner (inputs inner h)) →
      Meaning target (system.executableStep
        (system.dependencyEnvironment (relation dependencies) target inputs) target))
    (target : Occurrence) (outcome : Option Label)
    (certificate : EvaluationCertificate system (relation dependencies) target outcome) :
    Meaning target outcome := by
  induction certificate with
  | node target inputs children computed ih =>
      rw [computed]
      exact localSound target inputs ih

theorem checked_source_sound [DecidableEq Occurrence] [DecidableEq Label]
    (system : OccurrenceSystem FinalUnit Occurrence Label)
    (dependencies : Occurrence → List Occurrence)
    (Meaning : Occurrence → Option Label → Prop)
    (localSound : ∀ target (inputs : ∀ inner, relation dependencies inner target → Option Label),
      (∀ inner h, Meaning inner (inputs inner h)) →
      Meaning target (system.executableStep
        (system.dependencyEnvironment (relation dependencies) target inputs) target))
    (nodes : List (Node Occurrence Label)) (result : List (Fact Occurrence Label))
    (accepted : check system dependencies nodes = some result)
    (fact : Fact Occurrence Label) (member : fact ∈ result) : Meaning fact.1 fact.2 := by
  obtain ⟨certificate⟩ := check_sound system dependencies nodes result accepted fact member
  exact certificate_source_sound system dependencies Meaning localSound fact.1 fact.2 certificate

end TetraStereo.Certificate.DependencySource
