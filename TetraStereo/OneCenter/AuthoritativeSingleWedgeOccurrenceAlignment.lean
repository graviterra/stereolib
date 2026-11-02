import TetraStereo.OneCenter.AuthoritativeSingleWedgeSourcePerception
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRerootFrame
import Mathlib.Data.List.Permutation

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput
namespace SingleWedgeSource

/-!
# Source-only alignment to actual canonical occurrence roots

The finite matcher searches the 24 permutations of four slots, checking the actual atom IDs
of the returned canonical cursors. It does not equate carrier order with atom-index order.
Missing IDs, duplicate drawing endpoints and incompatible root lists fail closed.

This adapter supplies drawing parity in the actual occurrence order. It does not supply
CIP priority sorting, descriptor scheduling, auxiliary semantics, or scientific approval.
The completeness theorem states its exact atom-ID matching boundary explicitly; deriving
that boundary for every chemically admitted wedge source remains a separate obligation.
-/

/-- Independent, bijective correspondence from new occurrence slots to written drawing slots. -/
def ExactSlotAlignment (endpoints : List Nat) (rootIDs : List (Option Nat))
    (newToOld : List Nat) : Prop :=
  endpoints.length = 4 ∧ endpoints.Nodup ∧
    newToOld.Perm (List.range 4) ∧
      newToOld.map (fun slot => endpoints[slot]?) = rootIDs

/-- Bounded finite search; no caller permutation and no classical choice are used here. -/
def findSlotAlignment? (endpoints : List Nat) (rootIDs : List (Option Nat)) :
    Option (List Nat) :=
  if endpoints.length = 4 ∧ endpoints.Nodup then
    (List.range 4).permutations'.find? fun positions =>
      decide (positions.map (fun slot => endpoints[slot]?) = rootIDs)
  else none

theorem findSlotAlignment?_sound (endpoints : List Nat) (rootIDs : List (Option Nat))
    (positions : List Nat) (computed : findSlotAlignment? endpoints rootIDs = some positions) :
    ExactSlotAlignment endpoints rootIDs positions := by
  unfold findSlotAlignment? at computed
  split at computed
  · rename_i admitted
    have checked : decide (positions.map (fun slot => endpoints[slot]?) = rootIDs) = true :=
      List.find?_some (p := fun slots : List Nat =>
        decide (slots.map (fun slot => endpoints[slot]?) = rootIDs)) computed
    exact ⟨admitted.1, admitted.2,
      List.mem_permutations'.mp (List.mem_of_find?_eq_some computed),
      of_decide_eq_true checked⟩
  · simp at computed

theorem findSlotAlignment?_eq_none_iff (endpoints : List Nat)
    (rootIDs : List (Option Nat)) :
    findSlotAlignment? endpoints rootIDs = none ↔
      ¬∃ positions, ExactSlotAlignment endpoints rootIDs positions := by
  unfold findSlotAlignment?
  by_cases admitted : endpoints.length = 4 ∧ endpoints.Nodup
  · simp only [if_pos admitted, List.find?_eq_none]
    constructor
    · intro absent ⟨positions, matched⟩
      exact absent positions (List.mem_permutations'.mpr matched.2.2.1)
        (by simpa using matched.2.2.2)
    · intro absent positions present accepted
      apply absent
      exact ⟨positions, admitted.1, admitted.2, List.mem_permutations'.mp present,
        of_decide_eq_true accepted⟩
  · simp only [if_neg admitted]
    constructor
    · intro _ ⟨positions, matched⟩
      exact admitted ⟨matched.1, matched.2.1⟩
    · intro _
      trivial

/-- Any permutation of the four distinct endpoint IDs can be matched in finite search. -/
theorem findSlotAlignment?_exists_of_perm (endpoints : List Nat)
    (rootIDs : List (Option Nat)) (lengthFour : endpoints.length = 4)
    (distinct : endpoints.Nodup) (sameIDs : rootIDs.Perm (endpoints.map some)) :
    ∃ positions, findSlotAlignment? endpoints rootIDs = some positions := by
  have lookupRange : (List.range 4).map (fun slot => endpoints[slot]?) =
      endpoints.map some := by
    rcases List.length_eq_four.mp lengthFour with ⟨a, b, c, d, rfl⟩
    rfl
  have present : rootIDs ∈ ((List.range 4).map (fun slot => endpoints[slot]?)).permutations' :=
    List.mem_permutations'.mpr (by simpa [lookupRange] using sameIDs)
  rw [← List.map_permutations', List.mem_map] at present
  rcases present with ⟨positions, member, mapped⟩
  have matching : ExactSlotAlignment endpoints rootIDs positions :=
    ⟨lengthFour, distinct, List.mem_permutations'.mp member, mapped⟩
  have nonempty : findSlotAlignment? endpoints rootIDs ≠ none := by
    intro empty
    exact (findSlotAlignment?_eq_none_iff endpoints rootIDs).mp empty ⟨positions, matching⟩
  cases computed : findSlotAlignment? endpoints rootIDs with
  | none => exact False.elim (nonempty computed)
  | some result => exact ⟨result, rfl⟩

theorem ExactSlotAlignment.rootIDs_perm_endpoints (endpoints : List Nat)
    (rootIDs : List (Option Nat)) (positions : List Nat)
    (matching : ExactSlotAlignment endpoints rootIDs positions) :
    rootIDs.Perm (endpoints.map some) := by
  have lookupRange : (List.range 4).map (fun slot => endpoints[slot]?) =
      endpoints.map some := by
    rcases List.length_eq_four.mp matching.1 with ⟨a, b, c, d, rfl⟩
    rfl
  have reordered := matching.2.2.1.map (fun slot => endpoints[slot]?)
  simpa [matching.2.2.2, lookupRange] using reordered

theorem sourceFrame_endpoints_exactly_four_distinct (source : AuthoritativeChemicalInput)
    (center : Nat) (frame : Frame) (bound : SourceFrame source center frame) :
    frame.endpoints.length = 4 ∧ frame.endpoints.Nodup := by
  rcases bound with ⟨diagram, positions, _, _, admitted, rfl⟩
  rcases admitted with ⟨_, _, _, _, lengthFour, _, endpointDistinct, _⟩
  exact ⟨by simpa [frameOfDiagram] using lengthFour, endpointDistinct⟩

/-- The exact production cursor list, retaining its actual carrier order. -/
noncomputable def finalOccurrenceRoots (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    List (source.AromaticCanonicalRerootCursor fuel) :=
  source.aromaticCanonicalRerootChildren
    { occurrence := source.aromaticCanonicalFinalOccurrence fuel center, previous? := none }

theorem finalOccurrenceRoots_are_returned (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.aromaticCanonicalOccurrenceLigandFrame?
        (source.aromaticCanonicalFinalOccurrence fuel center) =
      some (finalOccurrenceRoots source fuel center) := by
  rfl

def cursorAtomID (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel) : Option Nat :=
  cursor.occurrence.1.node.current?.map Fin.val

noncomputable def finalOccurrenceRootIDs (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) : List (Option Nat) :=
  (finalOccurrenceRoots source fuel center).map (cursorAtomID source)

/-- Carrier order is only a permutation of official child order; its actual IDs are retained. -/
theorem finalOccurrenceRoots_frames_perm (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    ((finalOccurrenceRoots source fuel center).map (fun cursor => cursor.occurrence.1)).Perm
      (aromaticCanonicalFinalDirectChildFrames source fuel center) := by
  have exactCarrier : (finalOccurrenceRoots source fuel center).map
      (fun cursor => cursor.occurrence.1) =
      source.aromaticCanonicalCarrierOutwardChildFrames
        (fuel := fuel) (source.aromaticCanonicalFinalOccurrence fuel center).1 := by
    simp [finalOccurrenceRoots, aromaticCanonicalRerootChildren,
      aromaticCanonicalFinalOccurrence_intendedChildren_eq_outward]
  rw [exactCarrier]
  exact aromaticCanonicalCarrierOutwardChildFrames_final_perm source fuel center

def officialRootIDs (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalAtom) : List (Option Nat) :=
  (source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
    (OfficialCIPNode.root center)).map (fun node => node.current?.map Fin.val)

theorem finalOccurrenceRootIDs_perm_officialRootIDs (source : AuthoritativeChemicalInput)
    (fuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    (finalOccurrenceRootIDs source fuel center).Perm (officialRootIDs source center.1) := by
  have transported := (finalOccurrenceRoots_frames_perm source fuel center).map
    (fun frame => frame.node.current?.map Fin.val)
  have officialMapped : (aromaticCanonicalFinalDirectChildFrames source fuel center).map
      (fun frame => frame.node.current?.map Fin.val) = officialRootIDs source center.1 := by
    unfold aromaticCanonicalFinalDirectChildFrames officialRootIDs
    simpa only [List.map_map] using congrArg
      (List.map (fun node : OfficialCIPNode source.AromaticCanonicalAtom =>
        node.current?.map Fin.val))
      (List.zipIdx_map_fst 0 (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount (OfficialCIPNode.root center.1)))
  rw [officialMapped] at transported
  simpa [finalOccurrenceRootIDs, cursorAtomID, List.map_map] using transported

/-- Entire source-only adapter: drawing extraction followed by actual cursor-ID matching. -/
noncomputable def occurrenceAlignment? (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) : Option (Frame × List Nat) :=
  (extract? source center.1).bind fun frame =>
    (findSlotAlignment? frame.endpoints (finalOccurrenceRootIDs source fuel center)).map
      fun positions => (frame, positions)

/-- Independent meaning of an output, including the actual source and actual occurrence IDs. -/
def SourceOccurrenceAlignment (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (frame : Frame)
    (positions : List Nat) : Prop :=
  SourceFrame source center.1.val frame ∧
    ExactSlotAlignment frame.endpoints (finalOccurrenceRootIDs source fuel center) positions

/-- A drawing is admitted and the actual occurrence roots carry exactly its endpoint IDs.
This predicate does not mention the alignment search or any success equation. -/
def SourceOccurrenceAdmitted (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) : Prop :=
  ∃ frame, SourceFrame source center.1.val frame ∧
    (finalOccurrenceRootIDs source fuel center).Perm (frame.endpoints.map some)

theorem occurrenceAlignment?_sound (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (frame : Frame)
    (positions : List Nat)
    (computed : occurrenceAlignment? source fuel center = some (frame, positions)) :
    SourceOccurrenceAlignment source fuel center frame positions := by
  unfold occurrenceAlignment? at computed
  cases extracted : extract? source center.1 with
  | none => simp [extracted] at computed
  | some drawing =>
    cases found : findSlotAlignment? drawing.endpoints
        (finalOccurrenceRootIDs source fuel center) with
    | none => simp [extracted, found] at computed
    | some slots =>
      simp only [extracted, Option.bind_some, found, Option.map_some,
        Option.some.injEq, Prod.mk.injEq] at computed
      rcases computed with ⟨rfl, rfl⟩
      exact ⟨(extract?_eq_some_iff source center.1 drawing).mp extracted,
        findSlotAlignment?_sound drawing.endpoints _ slots found⟩

theorem occurrenceAlignment?_exists_iff_admitted (source : AuthoritativeChemicalInput)
    (fuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    (∃ aligned, occurrenceAlignment? source fuel center = some aligned) ↔
      SourceOccurrenceAdmitted source fuel center := by
  constructor
  · rintro ⟨⟨frame, positions⟩, computed⟩
    have matching := occurrenceAlignment?_sound source fuel center frame positions computed
    exact ⟨frame, matching.1,
      ExactSlotAlignment.rootIDs_perm_endpoints _ _ _ matching.2⟩
  · rintro ⟨frame, sourceBound, sameIDs⟩
    have drawing := (extract?_eq_some_iff source center.1 frame).mpr sourceBound
    have bounds := sourceFrame_endpoints_exactly_four_distinct source center.1.val frame
      sourceBound
    rcases findSlotAlignment?_exists_of_perm frame.endpoints _ bounds.1 bounds.2 sameIDs with
      ⟨positions, found⟩
    exact ⟨(frame, positions), by simp [occurrenceAlignment?, drawing, found]⟩

def transportSlotParity (parity : TetrahedralInputParity) (positions : List Nat) :
    TetrahedralInputParity :=
  if RawMolecule.permutationIsEven positions then parity
  else reverseTetrahedralInputParity parity

/-- Exact point-parity transport for a matched production slot list, including `none`. -/
theorem aligned_point_parity_transport (frame : Frame) (rootIDs : List (Option Nat))
    (positions : List Nat) (matching : ExactSlotAlignment frame.endpoints rootIDs positions) :
    ∃ newToOld : Equiv.Perm (Fin 4),
      Rule6HandednessSemantics.finFourPermutationList newToOld = positions ∧
      tetrahedralInputParityOfPoints?
          (RationalTetrahedralPermutation.permutedPoints
            frame.first frame.second frame.third frame.fourth newToOld) =
        (tetrahedralInputParityOfPoints? frame.points).map
          (fun parity => transportSlotParity parity positions) := by
  let newToOld := Rule6HandednessSemantics.finFourEquivOfPermutationList positions
    matching.2.2.1
  have positionsEq : Rule6HandednessSemantics.finFourPermutationList newToOld = positions :=
    Rule6HandednessSemantics.finFourPermutationList_equivOfPermutationList
      positions matching.2.2.1
  refine ⟨newToOld, positionsEq, ?_⟩
  rw [tetrahedralInputParityOfPoints?_permutedPoints]
  simp only [Frame.points, reindexTetrahedralInputParity, transportSlotParity,
    positionsEq]

/-- Drawing parity in actual returned occurrence order, without requesting a guessed frame. -/
noncomputable def occurrenceParity? (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) : Option TetrahedralInputParity :=
  (occurrenceAlignment? source fuel center).bind fun aligned =>
    (tetrahedralInputParityOfPoints? aligned.1.points).map fun parity =>
      transportSlotParity parity aligned.2

theorem occurrenceParity?_of_alignment (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (frame : Frame) (positions : List Nat)
    (computed : occurrenceAlignment? source fuel center = some (frame, positions)) :
    occurrenceParity? source fuel center =
      (tetrahedralInputParityOfPoints? frame.points).map
        (fun parity => transportSlotParity parity positions) := by
  simp [occurrenceParity?, computed]

/-- Successful occurrence-ID alignment always retains the source's nondegenerate parity. -/
theorem occurrenceParity?_exists_iff_admitted (source : AuthoritativeChemicalInput)
    (fuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    (∃ parity, occurrenceParity? source fuel center = some parity) ↔
      SourceOccurrenceAdmitted source fuel center := by
  constructor
  · rintro ⟨parity, computed⟩
    apply (occurrenceAlignment?_exists_iff_admitted source fuel center).mp
    cases aligned : occurrenceAlignment? source fuel center with
    | none => simp [occurrenceParity?, aligned] at computed
    | some value => exact ⟨value, rfl⟩
  · intro admitted
    rcases (occurrenceAlignment?_exists_iff_admitted source fuel center).mpr admitted with
      ⟨⟨frame, positions⟩, aligned⟩
    have sourceBound := (occurrenceAlignment?_sound source fuel center frame positions aligned).1
    have drawing := (extract?_eq_some_iff source center.1 frame).mpr sourceBound
    have nonempty := extracted_frame_parity_not_none source center.1 frame drawing
    rw [occurrenceParity?_of_alignment source fuel center frame positions aligned]
    cases observed : tetrahedralInputParityOfPoints? frame.points with
    | none => exact False.elim (nonempty observed)
    | some parity => exact ⟨transportSlotParity parity positions, rfl⟩

end SingleWedgeSource
end AuthoritativeChemicalInput

namespace SingleWedgeOccurrenceAlignmentRegression

open AuthoritativeChemicalInput AuthoritativeChemicalInput.SingleWedgeSource

theorem ordered_ids_match :
    findSlotAlignment? [1, 2, 3, 4] [some 1, some 2, some 3, some 4] =
      some [0, 1, 2, 3] := by decide +kernel

theorem permuted_actual_ids_are_matchable :
    (findSlotAlignment? [1, 2, 3, 4] [some 4, some 1, some 3, some 2]).isSome = true := by
  decide +kernel

theorem duplicate_endpoint_refused :
    findSlotAlignment? [1, 1, 3, 4] [some 1, some 1, some 3, some 4] = none := by decide +kernel

theorem missing_root_id_refused :
    findSlotAlignment? [1, 2, 3, 4] [some 1, some 2, none, some 4] = none := by decide +kernel

theorem extra_root_refused :
    findSlotAlignment? [1, 2, 3, 4] [some 1, some 2, some 3, some 4, some 5] = none := by decide +kernel

theorem duplicated_actual_root_refused :
    findSlotAlignment? [1, 2, 3, 4] [some 1, some 2, some 2, some 4] = none := by decide +kernel

theorem incompatible_actual_atom_refused :
    findSlotAlignment? [1, 2, 3, 4] [some 1, some 2, some 3, some 5] = none := by decide +kernel

/-- These are actual official CIP child IDs computed from the semantic CFClBrI source.
The subsequent carrier permutation theorem transfers this binding to returned cursors. -/
theorem cfclbri_official_root_ids :
    officialRootIDs SingleWedgeSourceRegression.source ⟨0, by decide⟩ =
      [some 1, some 2, some 3, some 4] := by decide +kernel

theorem cfclbri_returned_root_ids (fuel : Nat)
    (center : SingleWedgeSourceRegression.source.AromaticCanonicalTetrahedralCenter)
    (centerID : center.1.val = 0) :
    (finalOccurrenceRootIDs SingleWedgeSourceRegression.source fuel center).Perm
      [some 1, some 2, some 3, some 4] := by
  have centerEq : center.1 = (⟨0, by decide⟩ :
      SingleWedgeSourceRegression.source.AromaticCanonicalAtom) := Fin.ext centerID
  have binding := finalOccurrenceRootIDs_perm_officialRootIDs
    SingleWedgeSourceRegression.source fuel center
  rw [centerEq, cfclbri_official_root_ids] at binding
  exact binding

/-- Actual CFClBrI drawing endpoints bind every returned-root ordering, not one guessed order.
The center argument is the production candidate and only its identity is specified. -/
theorem cfclbri_occurrence_alignment_exists (fuel : Nat)
    (center : SingleWedgeSourceRegression.source.AromaticCanonicalTetrahedralCenter)
    (centerID : center.1.val = 0) :
    ∃ aligned, occurrenceAlignment? SingleWedgeSourceRegression.source fuel center =
      some aligned := by
  have centerEq : center.1 = SingleWedgeSourceRegression.center
      SingleWedgeSourceRegression.source (by decide) := Fin.ext centerID
  have observed := SingleWedgeSourceRegression.solid_source_recognized
  have extracted : ∃ frame, extract? SingleWedgeSourceRegression.source center.1 =
      some frame := by
    rw [centerEq]
    exact Option.isSome_iff_exists.mp observed
  rcases extracted with ⟨frame, extracted⟩
  have endpoints := SingleWedgeSourceRegression.wedge_last_endpoint_order_is_source_order
  rw [← centerEq, extracted] at endpoints
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at endpoints
  apply (occurrenceAlignment?_exists_iff_admitted _ fuel center).mpr
  refine ⟨frame, (extract?_eq_some_iff _ _ frame).mp extracted, ?_⟩
  rw [endpoints.1]
  exact cfclbri_returned_root_ids fuel center centerID

theorem cfclbri_occurrence_parity_exists (fuel : Nat)
    (center : SingleWedgeSourceRegression.source.AromaticCanonicalTetrahedralCenter)
    (centerID : center.1.val = 0) :
    ∃ parity, occurrenceParity? SingleWedgeSourceRegression.source fuel center = some parity :=
  (occurrenceParity?_exists_iff_admitted _ fuel center).mpr
    ((occurrenceAlignment?_exists_iff_admitted _ fuel center).mp
      (cfclbri_occurrence_alignment_exists fuel center centerID))

/-- The actual semantic carbon has four distinct normalized constitutional neighbours. -/
theorem cfclbri_actual_neighbor_set :
    SingleWedgeSourceRegression.source.aromaticCanonicalNeighborFinset ⟨0, by decide⟩ =
      {⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩} := by
  ext neighbor
  rw [mem_aromaticCanonicalNeighborFinset_iff]
  fin_cases neighbor <;> unfold AromaticCanonicalAdjacent <;> decide +kernel

theorem cfclbri_actual_neighbor_card :
    (SingleWedgeSourceRegression.source.aromaticCanonicalNeighborFinset ⟨0, by decide⟩).card =
      4 := by
  rw [cfclbri_actual_neighbor_set]
  decide +kernel

/-- An inhabited production center, constructed from source chemistry and neighbour count.
No caller supplies candidate membership, an alignment, or a successful descriptor. -/
def cfclbriProductionCenter :
    SingleWedgeSourceRegression.source.AromaticCanonicalTetrahedralCenter :=
  ⟨⟨0, by decide⟩, (mem_aromaticCanonicalTetrahedralCenterSet_iff _ _).mpr ⟨by
      unfold ConnectivityOnlyTetrahedralCenterAtom ConnectivityOnlyTetrahedralPeriodicElement
      decide +kernel,
    cfclbri_actual_neighbor_card⟩⟩

theorem cfclbri_constructed_center_alignment (fuel : Nat) :
    ∃ aligned, occurrenceAlignment? SingleWedgeSourceRegression.source fuel
      cfclbriProductionCenter = some aligned :=
  cfclbri_occurrence_alignment_exists fuel cfclbriProductionCenter rfl

theorem cfclbri_constructed_center_parity (fuel : Nat) :
    ∃ parity, occurrenceParity? SingleWedgeSourceRegression.source fuel
      cfclbriProductionCenter = some parity :=
  cfclbri_occurrence_parity_exists fuel cfclbriProductionCenter rfl

end SingleWedgeOccurrenceAlignmentRegression
end TetraStereo.OneCenter
