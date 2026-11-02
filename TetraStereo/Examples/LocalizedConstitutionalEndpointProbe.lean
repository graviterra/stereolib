import TetraStereo.OneCenter.LocalizedShortCircuitReadiness
import TetraStereo.OneCenter.LocalizedShortCircuitCachedPipeline
import TetraStereo.Examples.LocalizedShortCircuitDoubleBondProbe

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedConstitutionalEndpointProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput

private def carbon : PeriodicElement := ⟨6, by decide, by decide⟩
private def hydrogen : PeriodicElement := ⟨1, by decide, by decide⟩
private def fluorine : PeriodicElement := ⟨9, by decide, by decide⟩
private def bond (a b order : Nat) : SemanticInteraction :=
  { participants := [a, b], kind := .covalent order }

/-- D/H on both alkene endpoints. Rule 1a and Rule 1b tie; isotope mass decides Rule 2. -/
def isotopeSource (cis : Bool) : AuthoritativeChemicalInput :=
  let base := LocalizedShortCircuitDoubleBondProbe.source cis true
  { base with molecule := { base.molecule with atoms := base.molecule.atoms.zipIdx.map fun (atom, i) =>
      if i = 2 ∨ i = 3 then { atom with isotopeMassNumber? := some 2 } else atom } }

/-- The two carbon references at atom 0 tie at their roots and their immediate child layer.
The first distinguishing atom is F versus H two bonds farther into their branches. -/
def deepSource (cis : Bool) : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, carbon, carbon, fluorine, carbon, hydrogen,
          carbon, carbon, fluorine, hydrogen, hydrogen, hydrogen, hydrogen, hydrogen,
          hydrogen, hydrogen, hydrogen, hydrogen].map (fun element => { element })
        interactions := [bond 0 1 2, bond 0 2 1, bond 0 4 1, bond 1 3 1, bond 1 5 1,
          bond 2 6 1, bond 4 7 1, bond 6 8 1, bond 7 9 1,
          bond 2 10 1, bond 2 11 1, bond 4 12 1, bond 4 13 1,
          bond 6 14 1, bond 6 15 1, bond 7 16 1, bond 7 17 1] }
    spatial? := some { positions :=
      [{ x := 0, y := 0, z := 0 }, { x := 2, y := 0, z := 0 },
       { x := 0, y := 1, z := 0 }, { x := 2, y := if cis then 1 else -1, z := 0 },
       { x := 0, y := -1, z := 0 }, { x := 2, y := if cis then -1 else 1, z := 0 }] ++
      (List.range 12).map (fun i => { x := (i + 3 : Nat), y := 2, z := 1 }) } }

private def assertThat (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

/-- Confirm intake, topology and exact references before inspecting the tied-root branch. -/
def comparisonReached (source : AuthoritativeChemicalInput) (isotope : Bool) : Option Bool := do
  let input ← LocalizedShortCircuit.admitSource? source
  let ci := input.certified
  let fuel := LocalizedShortCircuit.carrierFuel input
  let occurrence ← (ci.localizedOccurrenceCarrier fuel).find? fun item =>
    decide (item.val.root.val = 0 ∧ item.val.address.length = 1 ∧
      item.val.node.provenance = .realAtom) &&
      (item.val.node.current?.map (fun atom => atom.val) == some 1) &&
      (item.val.node.parent?.map (fun atom => atom.val) == some 0)
  let topology ← ci.localizedRule3PhysicalEndpointCursorFrameExec? occurrence
  match ci.localizedRule3ExplicitSubstituents topology.left topology.right with
  | [first, second] =>
      let fc ← ci.localizedRule3ReferenceCursorExec? topology.leftCursor first
      let sc ← ci.localizedRule3ReferenceCursorExec? topology.leftCursor second
      let fk ← ci.buildLocalizedRerootRuleMajorKeyExec? (2 * (fuel + 1) + 1) fc
      let sk ← ci.buildLocalizedRerootRuleMajorKeyExec? (2 * (fuel + 1) + 1) sc
      let result ← ci.localizedRule3ShortCircuitEndpointPriorityExec?
        occurrence (fun _ _ => none) (fun _ => none)
        topology.left topology.right topology.leftCursor
      let readiness ← ci.localizedRule3StrictEndpointCertificate?
        topology.left topology.right topology.leftCursor
      let frame ← ci.buildLocalizedShortCircuitRule3FrameExec?
        occurrence (fun _ _ => none) (2 * (fuel + 1) + 2)
        [topology.leftCursor, topology.rightCursor]
      pure (decide (ci.compareLocalizedRerootCursorConstitutionalRoot fc sc = .eq) &&
        decide (OfficialRuleMajorKey.compare fk sk = .gt) &&
        decide (result.priority = .senior first) && decide (readiness.result = result) &&
        decide (frame.keys.length = 2) &&
        if isotope then decide (fk.rule1a = sk.rule1a ∧ fk.rule1b = sk.rule1b ∧ fk.rule2 ≠ sk.rule2)
        else decide (fk.rule1a.take 2 = sk.rule1a.take 2 ∧ fk.rule1a ≠ sk.rule1a))
  | _ => none

private def ready (source : AuthoritativeChemicalInput) : Option Bool := do
  let input ← LocalizedShortCircuit.admitSource? source
  pure (input.certified.localizedRule3CallbackFreeCarrierCertificate?
    (LocalizedShortCircuit.carrierFuel input)).isSome

def main : IO Unit := do
  assertThat "isotope tie reaches Rule-2 decision, certificate and linear-bound frame"
    (comparisonReached (isotopeSource false) true == some true)
  assertThat "deep layer tie reaches constitutional decision and linear-bound frame"
    (comparisonReached (deepSource false) false == some true)
  for cis in [false, true] do
    let expected := if cis then OfficialRule3Geometry.seqcis else .seqtrans
    assertThat "isotope geometry succeeds with refusing full-stereo callback"
      (decide (LocalizedShortCircuitDoubleBondProbe.classify (isotopeSource cis) = some expected))
    assertThat "deep branch geometry succeeds with refusing full-stereo callback"
      (decide (LocalizedShortCircuitDoubleBondProbe.classify (deepSource cis) = some expected))
  assertThat "isotope carrier constructs linear-bound readiness"
    (ready (isotopeSource false) == some true)
  assertThat "deep comparison carrier constructs linear-bound readiness"
    (ready (deepSource false) == some true)
  assertThat "complete constitutional tie still reaches callback refusal"
    ((LocalizedShortCircuitDoubleBondProbe.classify
      (LocalizedShortCircuitDoubleBondProbe.source false true)).isNone)
  let some input := LocalizedShortCircuit.admitSource? (isotopeSource false)
    | throw (IO.userError "isotope admission failed")
  let result := LocalizedShortCircuit.Cached.evaluate input []
  assertThat "isotope fixed-point output certificate replays"
    ((LocalizedShortCircuit.Cached.checkProposals? input result.nodes).isSome)

#eval main
end TetraStereo.Examples.LocalizedConstitutionalEndpointProbe
