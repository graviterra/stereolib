import TetraStereo.OneCenter.OfficialCIPEngine

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace OfficialCIPEngine

open OneCenter

/-- Empty official contexts are the safe default: Rules 3/4/5 tie unless proved context exists. -/
def emptyContext : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext :=
  fun _ => CIPRuleEngine.OfficialLigandRuleContext.empty

/-- The public official engine's stored comparison is exactly the total comparison obtained from
the bounded rule-major certificate at the proved finite-atom bound. -/
example {V : Type*} [Fintype V] [DecidableEq V] (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4) :
    (m.cipOfficialEngine context).compare i j =
      m.cipOfficialCompare context i j := by
  exact m.cipOfficialEngine_compare context i j

/-- Extra fuel beyond the default atom-cardinality bound is irrelevant at the public API.  The
bounded comparison is an `Option`; its outcome projection is exactly the outcome of the engine's
stored default certificate. -/
example {V : Type*} [Fintype V] [DecidableEq V] (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4)
    (extra : ℕ) :
    (m.cipOfficialCompareWithFuel context ((Fintype.card V + 1) + extra) i j).map
        CIPTraceCertificate.outcome =
      some ((m.cipOfficialEngine context).compare i j).outcome := by
  exact (m.cipOfficialEngine context).stableOutcome i j extra

/-- Resolved official priorities make the safe permutation available. -/
example {V : Type*} [Fintype V] [DecidableEq V] (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (h : m.ResolvedOfficialCIP context) :
    (m.cipOfficialEngine context).safePermutation? =
      some (m.cipOfficialPermutation context) := by
  exact m.cipOfficialEngine_safePermutation?_eq_some_of_resolved context h

/-- Safe official `R/S` refuses unresolved ties and returns the canonical official assignment once
priorities are resolved. -/
example {V : Type*} [Fintype V] [DecidableEq V] (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (h : m.ResolvedOfficialCIP context) (g : TetrahedralGeometry.Realization) :
    m.rsOfficial? context g = some (m.rsOfficial context g) := by
  exact m.rsOfficial?_eq_some_of_resolved context h g

end OfficialCIPEngine
end Examples
end TetraStereo
