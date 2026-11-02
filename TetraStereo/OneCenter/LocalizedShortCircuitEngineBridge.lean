import TetraStereo.OneCenter.LocalizedShortCircuitCheckedPipeline
import TetraStereo.OneCenter.LocalizedEngineBridge

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedShortCircuit.EngineBridge




abbrev propose := LocalizedReference.EngineBridge.propose

def evaluate (input : Input) : Evaluation input :=
  LocalizedShortCircuit.evaluate input (propose input)

def analyze (input : Input) : Report := report input (evaluate input).facts

theorem analyze_eq_reference (input : Input) :
    analyze input = LocalizedShortCircuit.analyze input :=
  evaluation_report_eq_reference input (evaluate input)

def analyzeSource? (source : AuthoritativeChemicalInput) : Option Report :=
  LocalizedShortCircuit.analyzeSource? source propose

theorem analyzeSource?_eq_reference (source : AuthoritativeChemicalInput) :
    analyzeSource? source = (admitSource? source).map LocalizedShortCircuit.analyze :=
  LocalizedShortCircuit.analyzeSource?_eq_reference source propose

end TetraStereo.OneCenter.LocalizedShortCircuit.EngineBridge
