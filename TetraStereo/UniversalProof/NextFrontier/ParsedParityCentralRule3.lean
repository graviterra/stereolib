import TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralConstitutional
import TetraStereo.UniversalProof.NextFrontier.ParsedParityRule3NoDouble

set_option autoImplicit false









namespace TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralRule3

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.ParsedParitySourceIntake
open TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceFrames
open TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceArmCoordinates
open TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmSource
open TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralSourceLeaves
open TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralConstitutional

private theorem computed_keyFrame_rule3_empty
    (source : AuthoritativeChemicalInput)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view ruleFuel cursors = some frame)
    (slot : Fin 4) :
    (frame.keyAt slot).rule3.rule3 = [] := by
  have meaning := source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_sound
    target view ruleFuel cursors frame computed
  have empty := source.declarativeRule3SpatialKeyExceptList_rule3_eq_nil_of_noDouble
    noDouble meaning.1.2.2.2
  change (frame.rule3Frame.keys.get (Fin.cast frame.rule3Length.symm slot)).rule3 = []
  exact empty _ (List.get_mem _ _)

/-- Every slot of the internally computed central frame has empty Rule-3 layers.
No selected key or Rule-3 result is supplied by the caller. -/
theorem central_slot_rule3_empty (c l r : TetrahedralInputParity) (slot : Fin 4) :
    ((centralKeys c l r).keyAt slot).rule3.rule3 = [] := by
  exact computed_keyFrame_rule3_empty (ownSource (raw c l r))
    (actual_source_no_double (raw c l r) (raw_ordinary_source_input c l r))
    (centralTarget c l r) (centralView c l r) 4 (sourceFrame c l r).roots
    (centralKeys c l r) (central_keys_computed c l r) slot

/-- The actual central arm keys tie through all constitutional rules and Rule 3. -/
theorem central_arms_rule3_tie (c l r : TetrahedralInputParity) :
    (ownSource (raw c l r)).compareAromaticCanonicalUncancelledRule3SpatialKeys
      ((centralKeys c l r).keyAt (armSlot c l r true)).rule3
      ((centralKeys c l r).keyAt (armSlot c l r false)).rule3 = .eq := by
  rw [(ownSource (raw c l r)).compareAromaticCanonicalUncancelledRule3SpatialKeys_of_constitutional_eq
    _ _ (central_arms_constitutional_tie c l r)]
  rw [central_slot_rule3_empty c l r (armSlot c l r true),
    central_slot_rule3_empty c l r (armSlot c l r false)]
  rfl

end TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralRule3
