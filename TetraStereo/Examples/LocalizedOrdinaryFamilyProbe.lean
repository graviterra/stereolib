import TetraStereo.OneCenter.LocalizedFamilyReferencePipeline
import TetraStereo.Examples.LocalizedOmissionReadinessProbe

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedOrdinaryFamilyProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedShortCircuit

private def carbon : PeriodicElement := ⟨6, by decide, by decide⟩
private def hydrogen : PeriodicElement := ⟨1, by decide, by decide⟩
private def fluorine : PeriodicElement := ⟨9, by decide, by decide⟩
private def chlorine : PeriodicElement := ⟨17, by decide, by decide⟩
private def bromine : PeriodicElement := ⟨35, by decide, by decide⟩
private def bond (left right order : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent order }

def ordinarySource (cis : Bool) (tied : Bool := false) : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, carbon, if tied then hydrogen else fluorine,
          hydrogen, fluorine, hydrogen].map fun element => { element }
        interactions := [bond 0 1 2, bond 0 2 1, bond 0 3 1, bond 1 4 1, bond 1 5 1] }
    spatial? := some { positions :=
      [{ x := 0, y := 0, z := 0 }, { x := 2, y := 0, z := 0 },
       { x := 0, y := 1, z := 0 }, { x := 0, y := -1, z := 0 },
       { x := 2, y := if cis then 1 else -1, z := 0 },
       { x := 2, y := if cis then -1 else 1, z := 0 }] } }

/-- Reflection-related tetrahedral branches are otherwise constitutionally identical. -/
def interactingSource (flip : Bool) : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, carbon, carbon, carbon, fluorine, chlorine, bromine,
          fluorine, chlorine, bromine, fluorine, hydrogen].map fun element => { element }
        interactions := [bond 0 1 2, bond 0 2 1, bond 0 3 1,
          bond 2 4 1, bond 2 5 1, bond 2 6 1, bond 3 7 1, bond 3 8 1, bond 3 9 1,
          bond 1 10 1, bond 1 11 1] }
    spatial? := some { positions :=
      [{ x := 0, y := 0, z := 0 }, { x := 2, y := 0, z := 0 },
       { x := 0, y := 1, z := 0 }, { x := 0, y := -1, z := 0 },
       { x := 1, y := 2, z := 1 }, { x := -1, y := 2, z := 1 }, { x := 0, y := 2, z := -1 },
       { x := 1, y := -2, z := 1 }, { x := -1, y := -2, z := 1 }, { x := 0, y := -2, z := -1 },
       { x := 2, y := if flip then -1 else 1, z := 0 },
       { x := 2, y := if flip then 1 else -1, z := 0 }] } }

/-- The double bond is a bridge even though one substituent contains a saturated ring. -/
def remoteRingSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, carbon, fluorine, hydrogen, carbon, hydrogen, carbon, carbon,
          hydrogen, hydrogen, hydrogen, hydrogen, hydrogen].map fun element => { element }
        interactions := [bond 0 1 2, bond 0 2 1, bond 0 3 1, bond 1 4 1, bond 1 5 1,
          bond 4 6 1, bond 6 7 1, bond 7 4 1, bond 4 8 1,
          bond 6 9 1, bond 6 10 1, bond 7 11 1, bond 7 12 1] } }

private def checkTest (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

private def runSource (source : AuthoritativeChemicalInput) :
    IO ((input : Input) × Families.Result input) := do
  let some result := Families.evaluateSource? source | throw (IO.userError "ordinary input rejected")
  pure result

def main : IO Unit := do
  for cis in [false, true] do
    let result ← runSource (ordinarySource cis)
    checkTest "ordinary full pipeline emits exact E/Z with constitutional endpoint parity"
      (decide (result.2.ordinaryAcyclic.map (fun attempt => attempt.outcome.map fun a =>
        (a.outcome, a.left.selection.enantiomorphic, a.right.selection.enantiomorphic)) =
          [some (.alkene (if cis then .Z else .E), false, false)]))
  let missing ← runSource { ordinarySource true with spatial? := none }
  checkTest "missing geometry retains one refused ordinary candidate"
    (missing.2.ordinaryAcyclic.length == 1 && missing.2.ordinaryAcyclic.all (fun a => a.outcome.isNone))
  let tied ← runSource (ordinarySource true true)
  checkTest "a tied hydrogen endpoint yields no arbitrary planar assignment"
    (tied.2.ordinaryAcyclic.length == 1 && tied.2.ordinaryAcyclic.all (fun a => a.outcome.isNone))
  let cumulene ← runSource LocalizedOmissionReadinessProbe.alleneSource
  checkTest "ordinary family retains and refuses both cumulene bonds"
    (cumulene.2.ordinaryAcyclic.length == 2 && cumulene.2.ordinaryAcyclic.all (fun a => a.outcome.isNone))
  let ring ← runSource LocalizedOmissionReadinessProbe.ringSource
  checkTest "ordinary acyclic family retains and refuses the cyclic physical bond"
    (ring.2.ordinaryAcyclic.length == 1 && ring.2.ordinaryAcyclic.all (fun a => a.outcome.isNone))
  let some remote := admitSource? remoteRingSource | throw (IO.userError "remote-ring input rejected")
  let some remoteBond := (Families.canonicalDoubleBonds remote).head?
    | throw (IO.userError "remote-ring double bond absent")
  checkTest "a remote saturated ring does not prevent a physical bridge certificate"
    (OrdinaryPlanar.topology? remote.certified (carrierFuel remote) remoteBond).isSome
  let interacting ← runSource (interactingSource false)
  let labels := (report interacting.1 interacting.2.auxiliary.facts).map Prod.snd
  IO.println s!"interacting root labels: {repr labels}"
  checkTest "checked auxiliary evaluation constructs opposite R/S branch descriptors"
    (labels.length == 2 && decide (some (.chiral .R) ∈ labels) && decide (some (.chiral .S) ∈ labels))
  checkTest "the decisive Rule5 endpoint parity is retained in the assignment"
    (decide (interacting.2.ordinaryAcyclic.map (fun attempt => attempt.outcome.map fun a =>
      (a.left.selection.enantiomorphic, a.right.selection.enantiomorphic)) = [some (true, false)]))
  let flipped ← runSource (interactingSource true)
  let first := interacting.2.ordinaryAcyclic.map (fun attempt => attempt.outcome.map (fun a => a.outcome))
  let second := flipped.2.ordinaryAcyclic.map (fun attempt => attempt.outcome.map (fun a => a.outcome))
  IO.println s!"interacting planar outcomes: {repr first}, {repr second}"
  checkTest "opposite geometry produces both sequence descriptors rather than losing Rule5 parity"
    (decide ((first = [some (.enantiomorphicDoubleBond .seqCis)] ∧
        second = [some (.enantiomorphicDoubleBond .seqTrans)]) ∨
      (first = [some (.enantiomorphicDoubleBond .seqTrans)] ∧
        second = [some (.enantiomorphicDoubleBond .seqCis)])))

#eval main
end TetraStereo.Examples.LocalizedOrdinaryFamilyProbe
