import TetraStereo.OneCenter.LocalizedF2SuppliedLabelFixture
import TetraStereo.OneCenter.LocalizedOccurrenceUniversalDepth
import TetraStereo.OneCenter.LocalizedOccurrenceExecutableRoots

set_option autoImplicit false





namespace TetraStereo.OneCenter.F2SuppliedLabelProbe

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.F2SuppliedLabelFixture

abbrev carrierFuel : Nat := 29
abbrev buildFuel : Nat := 60

def target12 : input.LocalizedCIPOccurrence carrierFuel :=
  input.localizedAtomRootOccurrenceExecutable carrierFuel atom12

def target20 : input.LocalizedCIPOccurrence carrierFuel :=
  input.localizedAtomRootOccurrenceExecutable carrierFuel atom20

def ligandCursorExec (center : input.TetrahedralCenter) (index : Fin 4) :
    input.LocalizedRerootCursor carrierFuel :=
  { occurrence :=
      ⟨{ root := center.1
         address := [input.localizedLigandRootSlot center index]
         node := input.localizedLigandRootNode center index
         remaining := carrierFuel }, by
          have rooted := input.localizedOccurrenceUniversalDepth_covers_ligand_moleculeWide
            center index (UnboundedOfficialSubtree.refl _)
          simpa [carrierFuel, input_atomCount,
            ← input.localizedLigandRootNode_eq_rootFromEdge center index] using rooted⟩
    previous? := some (input.localizedAtomRootOccurrenceExecutable carrierFuel center.1) }

def cursor12_0 : input.LocalizedRerootCursor carrierFuel :=
  ligandCursorExec center12 0

def cursor12_1 : input.LocalizedRerootCursor carrierFuel :=
  ligandCursorExec center12 1

def cursor20_0 : input.LocalizedRerootCursor carrierFuel :=
  ligandCursorExec center20 0

def cursor20_1 : input.LocalizedRerootCursor carrierFuel :=
  ligandCursorExec center20 1

/-- Decode source-assigned labels on the exact outward path rooted at `root`. Duplicate and
placeholder nodes have no real-atom label in the current Lean input language. -/
def exportedLabelAtFrame (root : Nat) (frame : input.LocalizedCIPOccurrenceFrame) :
    Option LocalizedAuxiliaryLabel :=
  if frame.node.provenance = OfficialCIPNodeProvenance.realAtom then
    let path := frame.node.history.reverse.map Fin.val
    let raw := if root = 12 then root12ExportedAuxLabel path
      else if root = 20 then root20ExportedAuxLabel path else none
    raw.bind toLocalizedAuxLabel
  else none

/-- A proof-restricted view of the supplied export. `Unknown` is preserved in the tagged export
table and mapped to `none` only by `toLocalizedAuxLabel`; this probe does not claim that this
projection is source-comparator-equivalent. -/
def suppliedView (root : Nat) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) :
    input.LocalizedDependencyView target :=
  fun source _ => exportedLabelAtFrame root source.1

end TetraStereo.OneCenter.F2SuppliedLabelProbe
