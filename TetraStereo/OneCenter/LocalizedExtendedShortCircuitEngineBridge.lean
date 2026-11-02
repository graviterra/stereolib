import TetraStereo.OneCenter.LocalizedExtendedShortCircuitCachedPipeline
import TetraStereo.OneCenter.LocalizedEngineBridge

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedExtendedShortCircuit.EngineBridge

/-- The existing fast engine supplies candidates. The extended checker replays every occurrence,
and rejected or incomplete proposals select the cached reference producer. -/
abbrev propose := LocalizedReference.EngineBridge.propose

def evaluate (input : Input) : Evaluation input :=
  Cached.evaluate input (propose input)

def analyze (input : Input) : Report := report input (evaluate input).facts

theorem analyze_eq_reference (input : Input) :
    analyze input = LocalizedExtendedShortCircuit.analyze input :=
  evaluation_report_eq_reference input (evaluate input)

def evaluateSource? (source : AuthoritativeChemicalInput) :
    Option ((input : Input) × Evaluation input) :=
  Cached.evaluateSource? source propose

def analyzeSource? (source : AuthoritativeChemicalInput) : Option Report :=
  (evaluateSource? source).map fun result => report result.1 result.2.facts

theorem analyzeSource?_eq_reference (source : AuthoritativeChemicalInput) :
    analyzeSource? source = (admitSource? source).map LocalizedExtendedShortCircuit.analyze := by
  unfold analyzeSource? evaluateSource? Cached.evaluateSource?
  cases admitted : admitSource? source with
  | none => rfl
  | some input =>
      simp only [Option.map_some, evaluation_report_eq_reference]
      rfl

end TetraStereo.OneCenter.LocalizedExtendedShortCircuit.EngineBridge
