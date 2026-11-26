import TetraStereo.Engine.RingAtomicNeighborOrder

/-! Root-aware terminal-twin refusal from the four actual incident atoms and raw
terminal bond rows. No automorphism search or frozen-reader premise is used. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingRootTwinDecision
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Cell)
open RingHydrogenSpelling (TwinPair twinCandidate twinCandidate?)

private def pairs (i : Input) (c : i.certified.TetrahedralCenter) :
    List (i.certified.Atom × i.certified.Atom) :=
  let ns := (List.finRange 4).map (i.certified.canonicalLigandAtom c)
  ns.flatMap fun u => ns.map fun v => (u,v)

/-- Test every incident pair after excluding the original root. This can select
an alternate pair when the root is itself one of three identical leaves. -/
def detectedTwinPair? (i : Input) (root : i.certified.Atom)
    (c : i.certified.TetrahedralCenter) : Option (TwinPair i) :=
  (pairs i c).findSome? fun uv =>
    if root ≠ uv.1 ∧ root ≠ uv.2 then twinCandidate? i c uv.1 uv.2 else none

theorem detected_sound (i : Input) (root : i.certified.Atom)
    (c : i.certified.TetrahedralCenter) (p : TwinPair i)
    (found : detectedTwinPair? i root c = some p) :
    p.c = c ∧ root ≠ p.u ∧ root ≠ p.v := by
  obtain ⟨⟨u,v⟩,_,hit⟩ := List.exists_of_findSome?_eq_some found
  dsimp only at hit
  split at hit
  · rename_i outside
    unfold twinCandidate? at hit
    split at hit
    · cases Option.some.inj hit
      exact ⟨rfl,outside⟩
    · contradiction
  · contradiction

theorem detected_iff (i : Input) (root : i.certified.Atom)
    (c : i.certified.TetrahedralCenter) :
    (detectedTwinPair? i root c).isSome = true ↔
      ∃ p : TwinPair i, p.c = c ∧ root ≠ p.u ∧ root ≠ p.v := by
  constructor
  · intro found
    obtain ⟨p,hit⟩ := Option.isSome_iff_exists.mp found
    exact ⟨p,detected_sound i root c p hit⟩
  · rintro ⟨p,same,outside⟩
    subst c
    have candidate : twinCandidate i p.c p.u p.v :=
      ⟨p.distinct,p.records,p.lu,p.lv⟩
    apply List.findSome?_isSome_iff.mpr
    refine ⟨(p.u,p.v),?_,?_⟩
    · let d := RingWrittenPHReadings.tetraEnumeration i p.c
      obtain ⟨h,hu⟩ := d.surjective ⟨p.u,i.certified.moleculeGraph.adj_symm.mpr ((p.supportU _).mpr rfl)⟩
      obtain ⟨k,hv⟩ := d.surjective ⟨p.v,i.certified.moleculeGraph.adj_symm.mpr ((p.supportV _).mpr rfl)⟩
      have member {a : i.certified.Atom} {t : Fin 4} (hit : i.certified.canonicalLigandAtom p.c t = a) :
          a ∈ (List.finRange 4).map (i.certified.canonicalLigandAtom p.c) :=
        List.mem_map.mpr ⟨t,List.mem_finRange _,hit⟩
      exact List.mem_flatMap.mpr ⟨p.u,member (congrArg Subtype.val hu),
        List.mem_map.mpr ⟨p.v,member (congrArg Subtype.val hv),rfl⟩⟩
    · simp [outside,twinCandidate?,candidate]

/-- A successful graph-only decision emits the native completed-refusal cell. -/
def direct (i : Input) (q : Site i) : Option Cell :=
  match i.certified.localizedOccurrenceDescriptorCenter? q with
  | none => none
  | some c => (detectedTwinPair? i q.val.root c).map fun _ => some none

theorem sound (i : Input) (q : Site i)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (cell : Cell) (found : direct i q = some cell) :
    RingChemicalGraphProof.state i q = cell := by
  unfold direct at found
  cases center : i.certified.localizedOccurrenceDescriptorCenter? q with
  | none => simp [center] at found
  | some c =>
    rw [center] at found
    cases detector : detectedTwinPair? i q.val.root c with
    | none => simp [detector] at found
    | some p =>
      have facts := detected_sound i q.val.root c p detector
      have recognized := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mp center
      have refusal := p.occurrence_refusal admitted q facts.2.1 facts.2.2 recognized.1
        (facts.1 ▸ recognized.2)
      have eqn : some none = cell := by simpa [detector] using found
      exact refusal.trans eqn

end TetraStereo.Engine.RingRootTwinDecision
assert_kernel_only TetraStereo.Engine.RingRootTwinDecision.detected_iff
assert_kernel_only TetraStereo.Engine.RingRootTwinDecision.sound
