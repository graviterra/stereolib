import TetraStereo.OneCenter.LocalizedRule3ShortCircuitSpatial
import TetraStereo.OneCenter.LocalizedOccurrenceFiniteCarrier

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedShortCircuitDoubleBondProbe
open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput

private def element (atomicNumber : ℕ) (positive : 0 < atomicNumber)
    (bounded : atomicNumber ≤ 118) : PeriodicElement :=
  { atomicNumber, positive, atMost118 := bounded }

private def carbon : PeriodicElement := element 6 (by decide) (by decide)
private def hydrogen : PeriodicElement := element 1 (by decide) (by decide)
private def fluorine : PeriodicElement := element 9 (by decide) (by decide)

private def checkAssertion (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

/-- Two planar configurations of explicit difluoroethene; all coordinates are rational. -/
def source (cis : Bool) (tied : Bool := false) : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms :=
          [{ element := carbon }, { element := carbon },
           { element := if tied then hydrogen else fluorine },
           { element := if tied then hydrogen else fluorine },
           { element := hydrogen }, { element := hydrogen }]
        interactions :=
          [{ participants := [0, 1], kind := .covalent 2 },
           { participants := [0, 2], kind := .covalent 1 },
           { participants := [0, 4], kind := .covalent 1 },
           { participants := [1, 3], kind := .covalent 1 },
           { participants := [1, 5], kind := .covalent 1 }] }
    spatial? := some
      { positions :=
          [{ x := 0, y := 0, z := 0 }, { x := 2, y := 0, z := 0 },
           { x := 0, y := 1, z := 0 }, { x := 2, y := if cis then 1 else -1, z := 0 },
           { x := 0, y := -1, z := 0 }, { x := 2, y := if cis then -1 else 1, z := 0 }] } }

/-- The callback deliberately refuses every full-key request. Strict first-sphere priorities must
still produce geometry; tied priorities must preserve the refusal. -/
def classify (source : AuthoritativeChemicalInput) : Option OfficialRule3Geometry := do
  let certified ← source.certify?
  let input ← certified.certifyLocalizedCIP?
  let fuel := input.certified.input.molecule.atomCount + 1
  let carrier := input.localizedOccurrenceCarrier fuel
  let occurrence ← carrier.find? fun item =>
    decide (item.val.root.val = 0 ∧ item.val.address.length = 1 ∧
      item.val.node.provenance = .realAtom) &&
      (item.val.node.current?.map (fun atom => atom.val) == some 1) &&
      (item.val.node.parent?.map (fun atom => atom.val) == some 0)
  let result ← input.localizedRule3ShortCircuitSpatialUnitWithExec?
    occurrence occurrence (fun _ _ => none) (fun _ => none)
  pure result.unit.core.geometry

/-- Distinguish an actual tied-endpoint refusal from an earlier intake or topology failure. -/
def tiedRefusalReached : Option Bool := do
  let certified ← (source false true).certify?
  let input ← certified.certifyLocalizedCIP?
  let fuel := input.certified.input.molecule.atomCount + 1
  let occurrence ← (input.localizedOccurrenceCarrier fuel).find? fun item =>
    decide (item.val.root.val = 0 ∧ item.val.address.length = 1 ∧
      item.val.node.provenance = .realAtom) &&
      (item.val.node.current?.map (fun atom => atom.val) == some 1) &&
      (item.val.node.parent?.map (fun atom => atom.val) == some 0)
  let topology ← input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence
  match input.localizedRule3ExplicitSubstituents topology.left topology.right with
  | [first, second] =>
      let firstCursor ← input.localizedRule3ReferenceCursorExec? topology.leftCursor first
      let secondCursor ← input.localizedRule3ReferenceCursorExec? topology.leftCursor second
      pure (decide (input.compareLocalizedRerootCursorConstitutionalRoot
        firstCursor secondCursor = Ordering.eq) &&
        (input.localizedRule3ShortCircuitEndpointPriorityExec?
          occurrence (fun _ _ => none) (fun _ => none)
          topology.left topology.right topology.leftCursor).isNone)
  | _ => none

def main : IO Unit := do
  checkAssertion "trans difluoroethene yields seqtrans with refusing full-key callback"
    (decide (classify (source false) = some .seqtrans))
  checkAssertion "cis difluoroethene yields seqcis with refusing full-key callback"
    (decide (classify (source true) = some .seqcis))
  checkAssertion "H/H admission, topology, references, and root tie reach endpoint refusal"
    (tiedRefusalReached == some true)
  checkAssertion "tied H/H endpoint preserves callback refusal"
    ((classify (source false true)).isNone)

#eval main
end TetraStereo.Examples.LocalizedShortCircuitDoubleBondProbe
