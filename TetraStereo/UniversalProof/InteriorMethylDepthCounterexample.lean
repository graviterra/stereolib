import TetraStereo.UniversalProof.NextFrontier.InteriorMethylPhysicalFixture
import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.OneCenter.CIPAuthoritativeMoleculeCursorRanking

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.UniversalProof.InteriorMethylDepthCounterexample

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking






-- carbon is re-exported from InteriorMethylPhysicalFixture.


-- hydrogen is re-exported from InteriorMethylPhysicalFixture.


-- fluorine is re-exported from InteriorMethylPhysicalFixture.


-- bond is re-exported from InteriorMethylPhysicalFixture.


-- molecule is re-exported from InteriorMethylPhysicalFixture.


-- tagOccurrence is re-exported from InteriorMethylPhysicalFixture.


-- incoming is re-exported from InteriorMethylPhysicalFixture.


-- outgoing is re-exported from InteriorMethylPhysicalFixture.


-- localLeft is re-exported from InteriorMethylPhysicalFixture.


-- localRight is re-exported from InteriorMethylPhysicalFixture.


-- swapMethyl is re-exported from InteriorMethylPhysicalFixture.


-- identical_constitution is re-exported from InteriorMethylPhysicalFixture.


-- raw_wellFormed is re-exported from InteriorMethylPhysicalFixture.


-- raw_valence is re-exported from InteriorMethylPhysicalFixture.


-- raw_saturated is re-exported from InteriorMethylPhysicalFixture.


-- exact_written_rows is re-exported from InteriorMethylPhysicalFixture.


-- actual_tag_generated is re-exported from InteriorMethylPhysicalFixture.


-- actual_incoming_generated is re-exported from InteriorMethylPhysicalFixture.


-- actual_outgoing_generated is re-exported from InteriorMethylPhysicalFixture.

theorem actual_frame_contains_both :
    incoming ∈ occurrenceLigandCursors molecule tagOccurrence ∧
    outgoing ∈ occurrenceLigandCursors molecule tagOccurrence := by decide +kernel

-- These branches are identical when compared in the same center-rooted frame.
theorem local_tie : compareCursorBranchAt molecule 1 .rule2 localLeft localRight =
    some Ordering.eq := by decide +kernel

-- Same branch atoms; only the retained original discovery ancestry differs.
theorem interior_fast_wrong_strict :
    compareCursorBranchAt molecule 1 .rule2 incoming outgoing = some Ordering.gt := by
  decide +kernel
theorem interior_authoritative_wrong_strict :
    compareCursorBranchAtAuthoritative? molecule 1 .rule2 incoming outgoing =
      some Ordering.gt := by decide +kernel
theorem interior_rule1a_tie :
    compareCursorBranchAt molecule 1 .rule1a incoming outgoing = some Ordering.eq := by
  decide +kernel
theorem original_depth_causes_strict :
    molecule.compareCanonicalNodeRule? .rule1b incoming.node outgoing.node =
      some Ordering.gt := by decide +kernel
theorem interior_fast_protocol_wrong_strict :
    compareOccurrenceBranches? molecule [] 1 incoming outgoing =
      some { ordering := Ordering.gt } := by decide +kernel
theorem interior_authoritative_protocol_wrong_strict :
    compareOccurrenceBranchesAuthoritative? molecule [] 1 incoming outgoing =
      some { ordering := Ordering.gt } := by decide +kernel
theorem interior_complete_protocol_wrong_strict :
    compareOccurrenceBranchesComplete? molecule [] 1 incoming outgoing =
      some { ordering := Ordering.gt } := by decide +kernel

-- The historical backend manufactured uppercase facts for these identical methyl ligands.
-- These two diagnostic names now explicitly identify that retained backend.
theorem interior_fast_spurious_fact :
    (legacyOccurrenceFact? molecule 1 [] tagOccurrence).isSome = true := by decide +kernel
theorem interior_authoritative_spurious_fact :
    (legacyOccurrenceFactAuthoritative? molecule 1 [] tagOccurrence).isSome = true := by
  decide +kernel

/-- The repaired public fast path retains the equal-ligand refusal. -/
theorem interior_fast_corrected_refusal :
    occurrenceFact? molecule 1 [] tagOccurrence = none := by decide +kernel

/-- The repaired public authoritative path retains the equal-ligand refusal. -/
theorem interior_authoritative_corrected_refusal :
    occurrenceFactAuthoritative? molecule 1 [] tagOccurrence = none := by decide +kernel

end TetraStereo.UniversalProof.InteriorMethylDepthCounterexample
