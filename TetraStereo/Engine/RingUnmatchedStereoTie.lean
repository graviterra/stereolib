import TetraStereo.Engine.RingUnmatchedStereoOrder

/-! On the F/Cl phosphane oxirane scaffold, the two arms admit a frozen
observed-tree exchange exactly when the phosphorus determinants agree.
The matched occurrences are the phosphorus, chlorine and fluorine on each arm. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace TetraStereo.Engine.RingUnmatchedStereoTie
open OneCenter CertifiedLocalizedCIPInput RingHydrogenSpelling
open RingUnmatchedStereoOrder (left right moved read)
open PhosRootKey (reference frameZero)
open private key_injective from TetraStereo.Engine.RingUnmatchedStereoOrder
open RingSpatialTransport (size)
open RingActivePairs (Arm)
open private kids from TetraStereo.Engine.RingGeometryExchange
open RingRetainedChemicalTrace (observation?)

private def nodes (side : Bool) (k : Fin 3) : Arm reference :=
  let p := PhosRootKey.arm (if side then 1 else 0)
  if k = 0 then p else (PhosRootKey.fastRerootChildren p).getD (k.val-1) p

private def successors (k : Fin 3) : List (Fin 3) := if k = 0 then [1,2] else []

private def index {i : LocalizedChemicalRing.Input} (q : Arm i) : Fin 3 :=
  match q.occurrence.val.node.current?.map Fin.val with
  | some 5 => 1
  | some 6 => 2
  | _ => 0

private theorem children (s : Bool) (k : Fin 3) :
    reference.certified.executableLocalizedRerootChildren (nodes s k) = (successors k).map (nodes s) := by
  rw [PhosRootKey.rerootChildren_eq]
  cases s <;> fin_cases k <;> decide +kernel

private theorem indexes (k : Fin 3) : index (nodes false k) = k := by fin_cases k <;> decide +kernel

private theorem records (k : Fin 3) :
    observation? reference (nodes false k) (successors k).isEmpty =
    observation? reference (nodes true k) (successors k).isEmpty := by fin_cases k <;> decide +kernel

private theorem labels (h : Option RS) (k : Fin 3) :
    PhosRootKey.canonicalReader h h (nodes false k).occurrence =
    PhosRootKey.canonicalReader h h (nodes true k).occurrence := by
  rcases h with _ | ⟨_ | _⟩ <;> fin_cases k <;> decide +kernel

theorem exchange_iff (x : SpatialConfiguration) (full : x.positions.length = size reference)
    (valid : LocalizedChemicalRing.coordinatesAdmitted (moved x full) = true)
    (fr : RingNestedActivePair.Frame (moved x full)
      (RingSpatialTransport.reindexSite reference x full (PhosRootKey.origin 0))) :
    Nonempty (RingObservedTreeMatch.Unmarked fr (read x full) 0 1) ↔ left x = right x := by
  constructor
  · intro yes
    by_contra ne
    exact RingUnmatchedStereoOrder.no_exchange x full valid ne fr yes
  intro equal
  let move := RingStereoKeyCoordinates.cursor reference x full
  let row (s : Bool) (k : Fin 3) := move (nodes s k)
  have idx (k : Fin 3) : index (row false k) = k := indexes k
  have rowKids (s : Bool) (k : Fin 3) :
      (moved x full).certified.executableLocalizedRerootChildren (row s k) =
        (successors k).map (row s) := by
    rw [show row s k = move (nodes s k) from rfl, ← RingStereoKeyCoordinates.children_atGeometry,
      children,List.map_map]
    rfl
  let image (q : Arm (moved x full)) := row true (index q)
  have matched (k : Fin 3) : image (row false k) = row true k := congrArg (row true) (idx k)
  let c : RingGeometryExchange.Carrier (moved x full) (moved x full) := {
    domain := fun q => ∃ k, row false k = q
    image := image
    below := by
      rintro _ ⟨k,rfl⟩ q h
      simp only [kids] at h
      rw [rowKids] at h
      obtain ⟨t,_,eqn⟩ := List.mem_map.mp h
      exact ⟨t,eqn⟩
    children := by
      rintro _ ⟨k,rfl⟩
      simp only [kids,matched,rowKids,List.map_map]
      apply List.Perm.of_eq
      exact List.map_congr_left (fun t _ => matched t)
    observation := by
      rintro _ ⟨k,rfl⟩
      simp only [kids,matched,rowKids,List.isEmpty_map]
      exact (RingStereoKeyCoordinates.observation_atGeometry reference x full _ _).trans
        ((records k).trans (RingStereoKeyCoordinates.observation_atGeometry reference x full _ _).symm) }
  have root (s : Bool) : RingGroupedCentre.cursor fr (if s then 1 else 0) = row s 0 := by
    rw [RingSpatialTransport.frame_cursor_eq reference x full frameZero fr,PhosRootKey.cursor_eq]
    rfl
  refine ⟨⟨c,⟨0,(root false).symm⟩,?_,?_⟩⟩
  · change image (RingGroupedCentre.cursor fr 0) = RingGroupedCentre.cursor fr 1
    rw [show RingGroupedCentre.cursor fr 0 = row false 0 from root false,matched]
    exact (root true).symm
  · rintro _ ⟨k,rfl⟩
    change read x full (row false k).occurrence = read x full (image (row false k)).occurrence
    rw [matched]
    have frozen := PhosphaneOxirane.frozen_c0 (moved x full) PhosRootKey.reference_molecule valid
    rw [RingWrittenPHReadings.inputGeometry_eq] at frozen
    unfold RingUnmatchedStereoOrder.read
    rw [frozen]
    change PhosRootKey.canonicalReader (left x) (right x) (nodes false k).occurrence =
      PhosRootKey.canonicalReader (left x) (right x) (nodes true k).occurrence
    rw [equal]
    exact labels _ _

/-- The full ordinary comparison ties on either pass exactly when a frozen
correspondence exists. A family with only this one auxiliary on each arm cannot
supply a counterexample in which the ordinary keys tie without such an exchange. -/
theorem ordinary_tie_iff_exchange (x : SpatialConfiguration) (full : x.positions.length = size reference)
    (valid : LocalizedChemicalRing.coordinatesAdmitted (moved x full) = true)
    (fr : RingNestedActivePair.Frame (moved x full)
      (RingSpatialTransport.reindexSite reference x full (PhosRootKey.origin 0))) (rev : Bool) :
    RingFullPathEligibility.key? (moved x full) (read x full) rev (RingUnmatchedStereoOrder.arm x full 0) =
      RingFullPathEligibility.key? (moved x full) (read x full) rev (RingUnmatchedStereoOrder.arm x full 1) ↔
    Nonempty (RingObservedTreeMatch.Unmarked fr (read x full) 0 1) := by
  obtain ⟨a,b⟩ := RingUnmatchedStereoOrder.actual_keys x full valid rev
  rw [a,b,exchange_iff x full valid fr,Option.some.injEq]
  exact (key_injective rev).eq_iff

end TetraStereo.Engine.RingUnmatchedStereoTie
assert_kernel_only TetraStereo.Engine.RingUnmatchedStereoTie.exchange_iff
assert_kernel_only TetraStereo.Engine.RingUnmatchedStereoTie.ordinary_tie_iff_exchange
