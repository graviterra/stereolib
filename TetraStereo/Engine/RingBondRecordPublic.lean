import TetraStereo.Engine.RingBondRecordOrder
import TetraStereo.Engine.RingChemicalRenumbering

/-! Literal public API invariance under arbitrary permutations of the raw bond
records, for independently admitted hydrogen-complete molecular inputs. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingBondRecordOrder

open LocalizedChemicalRing (Input)
open RingHydrogenCompletion (plan)

variable {i j : Input}

/-- Every bond-table permutation preserves the complete public response on the
same requested identifiers, including refusals. No local stereochemical decision
or coordinate-admission hypothesis is supplied by the caller. -/
theorem closed_raw_public (p : Presentation i j)
    (closed : plan i.molecule = []) (closed' : plan j.molecule = []) (ids : List Nat) :
    RingHydrogenReport.fromRaw? j.molecule j.spatial ids =
      RingHydrogenReport.fromRaw? i.molecule i.spatial ids := by
  let r := (identityRenumbering p).toAtomMap
  have numbers : RingReportRenumber.renameId r = id := by
    funext n
    simp [RingReportRenumber.renameId, r, identityRenumbering,
      RingRawRenumbering.Renumbering.toAtomMap]
  have rows : RingRawRenumbering.AtomMap.renameRow r = id := by
    funext row
    rcases row with ⟨n, value⟩
    simp [RingRawRenumbering.AtomMap.renameRow, r, identityRenumbering,
      RingRawRenumbering.Renumbering.toAtomMap]
  have result := RingReportRenumber.closed_raw_report r closed closed' ids
  simpa [numbers,rows] using result

end TetraStereo.Engine.RingBondRecordOrder
assert_kernel_only TetraStereo.Engine.RingBondRecordOrder.closed_raw_public
