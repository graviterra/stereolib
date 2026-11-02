import TetraStereo.OneCenter.LocalizedFamilyCertificate

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedFamilyCertificateProbe
open OneCenter OneCenter.LocalizedShortCircuit

private def source : AuthoritativeChemicalInput :=
  let carbon : PeriodicElement := ⟨6, by decide, by decide⟩
  let hydrogen : PeriodicElement := ⟨1, by decide, by decide⟩
  let fluorine : PeriodicElement := ⟨9, by decide, by decide⟩
  let bond (a b order : Nat) : SemanticInteraction :=
    { participants := [a, b], kind := .covalent order }
  { molecule :=
      { atoms := [carbon, carbon, fluorine, hydrogen, fluorine, hydrogen].map fun element => { element }
        interactions := [bond 0 1 2, bond 0 2 1, bond 0 3 1, bond 1 4 1, bond 1 5 1] }
    spatial? := some { positions :=
      [{ x := 0, y := 0, z := 0 }, { x := 2, y := 0, z := 0 },
       { x := 0, y := 1, z := 0 }, { x := 0, y := -1, z := 0 },
       { x := 2, y := 1, z := 0 }, { x := 2, y := -1, z := 0 }] } }

private def assertTest (name : String) (condition : Bool) : IO Unit := do
  if condition then IO.println s!"PASS {name}"
  else throw (IO.userError s!"FAIL {name}")

def main : IO Unit := do
  let some input := admitSource? source | throw (IO.userError "admission failed")
  let result := Families.evaluate input []
  let payload := FamilyCertificate.exportPayload result
  assertTest "ordinary Z data-only report"
    (decide (payload.report.ordinaryAcyclic = [((0, 1), some (.alkene .Z))]))
  assertTest "refused monocyclic candidate retained"
    (decide (payload.report.monocyclic = [((0, 1), none)]))
  assertTest "own complete report accepted" (FamilyCertificate.check? input payload).isSome
  let missing : FamilyCertificate.Payload input :=
    { payload with report := { payload.report with monocyclic := [] } }
  assertTest "omitted none candidate rejected" (FamilyCertificate.check? input missing).isNone
  let forged : FamilyCertificate.Payload input :=
    { payload with report := { payload.report with ordinaryAcyclic := [((0, 1), some (.alkene .E))] } }
  assertTest "forged E label rejected" (FamilyCertificate.check? input forged).isNone
  let sequence : FamilyCertificate.Payload input :=
    { payload with report := { payload.report with ordinaryAcyclic :=
        [((0, 1), some (.enantiomorphicDoubleBond .seqCis))] } }
  assertTest "sequence-cis remains distinct from Z" (FamilyCertificate.check? input sequence).isNone
  let wrongId : FamilyCertificate.Payload input :=
    { payload with report := { payload.report with ordinaryAcyclic := [((1, 0), some (.alkene .Z))] } }
  assertTest "noncanonical bond identifier rejected" (FamilyCertificate.check? input wrongId).isNone
  let noAuxiliary : FamilyCertificate.Payload input := { payload with auxiliaryNodes := [] }
  assertTest "missing auxiliary certificate rejected" (FamilyCertificate.check? input noAuxiliary).isNone

#eval main
end TetraStereo.Examples.LocalizedFamilyCertificateProbe
