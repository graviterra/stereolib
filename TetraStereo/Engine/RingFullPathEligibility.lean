import TetraStereo.Engine.RingFullPathRule5

/-! # Ordinary ligand ties and eligibility for Rule 6

Hanson et al., p. 1762, consider a triple, a quadruple, or two pairs of
ligands that remain tied after Rule 5. The four molecular slots below are
ranked on the same frozen store before any atom is promoted. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingFullPathEligibility
open OneCenter RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Frame)
open RingActivePairReport (Slot)
open RingRetainedStereoRefinement (priority Derives)
open RingRetainedChemicalTrace (Word)

/-- Priorities that determine whether two ligands tie. The fixed S word
enters the magnitude of a strict Rule 5 decision. Its direction comes from R. -/
structure Key where
  throughFourA : List Word
  bestFourB : List Bool
  fourC : Word
  fixedR : List Bool
  deriving DecidableEq, Repr

def Reads (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) (key : Key) : Prop :=
  ∃ u l ar as' fr,
    Derives i r rev [] q u ∧ Derives i r rev [.lowercase] q l ∧
    RingFullPathPairs.FullSource i r rev .R q ar ∧ RingFullPathPairs.FullSource i r rev .S q as' ∧
    RingFullPathRule5.Word i r rev .R q fr ∧ key = ⟨u.deep,max ar as',l.word,fr⟩

def key? (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) : Option Key := do
  let u ← priority i r rev [] q
  let l ← priority i r rev [.lowercase] q
  let ar ← RingFullPathPairs.pairs? i r rev .R q
  let as' ← RingFullPathPairs.pairs? i r rev .S q
  let fr ← RingFullPathRule5.word? i r rev .R q
  return ⟨u.deep,max ar as',l.word,fr⟩

theorem key_exact {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) :
    ∃ k, key? i r rev q = some k ∧ ∀ h, Reads i r rev q h ↔ h = k := by
  obtain ⟨u,hu⟩ := RingOccurrenceStereo.rank_total ready rev [] q valid on
  obtain ⟨l,hl⟩ := RingOccurrenceStereo.rank_total ready rev [.lowercase] q valid on
  change priority i r rev [] q = some u at hu
  change priority i r rev [.lowercase] q = some l at hl
  obtain ⟨ar,hr,er⟩ := RingFullPathPairs.source_exact ready rev .R q valid on
  obtain ⟨as',hs,es⟩ := RingFullPathPairs.source_exact ready rev .S q valid on
  obtain ⟨fr,hf,ef⟩ := RingFullPathRule5.word_exact rev
    (RingOccurrenceStereo.rank_total ready rev [.lowercase]) .R q valid on
  have su := RingRetainedStereoRefinement.source [] q hu
  have sl := RingRetainedStereoRefinement.source [.lowercase] q hl
  refine ⟨⟨u.deep,max ar as',l.word,fr⟩,by simp [key?,hu,hl,hr,hs,hf],fun k => ⟨?_,?_⟩⟩
  · rintro ⟨w,z,m,n,t,sw,sz,sm,sn,st,rfl⟩
    rw [RingRetainedStereoRefinement.unique [] q _ _ sw su,
      RingRetainedStereoRefinement.unique [.lowercase] q _ _ sz sl,(er _).mp sm,(es _).mp sn,(ef _).mp st]
  · rintro rfl
    exact ⟨_,_,_,_,_,su,sl,(er _).mpr rfl,(es _).mpr rfl,(ef _).mpr rfl,rfl⟩

def tiedSlots (keys : Slot → Key) : List Slot :=
  (List.finRange 4).filter fun j => (List.finRange 4).any fun k => j != k && keys j == keys k

def candidates (keys : Slot → Key) : List Slot :=
  let tied := tiedSlots keys
  if 3 ≤ tied.length then tied else []

def candidates? {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (rev : Bool) :
    Option (List Slot) := do
  let keys ← RingActivePairReport.four? fun s => key? i r rev (RingGroupedCentre.cursor fr s)
  return candidates keys

theorem mem_tied (keys : Slot → Key) (s : Slot) :
    s ∈ tiedSlots keys ↔ ∃ j, s ≠ j ∧ keys s = keys j := by
  simp [tiedSlots,bne_iff_ne]

/-- The least numbered slot gives a name to a class solely for counting
its multiplicity. -/
def classOf (keys : Slot → Key) (s : Slot) : Slot :=
  (Finset.univ.filter fun j => keys s = keys j).min' ⟨s,by simp⟩

theorem class_eq (keys : Slot → Key) (s t : Slot) :
    classOf keys s = classOf keys t ↔ keys s = keys t := by
  have mem (j : Slot) : keys j = keys (classOf keys j) := by
    let cls := Finset.univ.filter fun t : Slot => keys j = keys t
    have inhabited : cls.Nonempty := ⟨j,by simp [cls]⟩
    exact (Finset.mem_filter.mp (Finset.min'_mem cls inhabited)).2
  constructor
  · intro h
    exact (mem s).trans ((congrArg keys h).trans (mem t).symm)
  · intro h
    unfold classOf
    simp only [h]

/-- Exact chemical gate on a four-ligand frame, including each possible
tie partition. -/
theorem promotion_patterns (keys : Slot → Key) :
    3 ≤ (tiedSlots keys).length ↔ RingRetainedChemicalPreorder.blockSizes (classOf keys) ∈
      ([[1,3],[2,2],[4]] : List (List Nat)) := by
  let tied (c : Slot → Slot) := (List.finRange 4).filter fun j =>
    (List.finRange 4).any fun k => j != k && c j == c k
  have same : tiedSlots keys = tied (classOf keys) := by
    apply List.filter_congr
    intro j _
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true,Bool.and_eq_true,beq_iff_eq,class_eq]
  have four : ∀ a b c d : Slot, let row : Slot → Slot := ![a,b,c,d]
      3 ≤ (tied row).length ↔ RingRetainedChemicalPreorder.blockSizes row ∈
        ([[1,3],[2,2],[4]] : List (List Nat)) := by decide +kernel
  let c := classOf keys
  have eta : classOf keys = ![c 0,c 1,c 2,c 3] := by funext j; fin_cases j <;> rfl
  rw [same,eta]
  exact four ..

/-- The four actual directions suffice to construct all candidates. Every
independent choice of molecular readings yields the same candidate list. -/
theorem frozen_candidates {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {f : Site i} (fr : Frame i f) (rev : Bool) :
    let r := RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f
    ∃ keys : Slot → Key, (∀ s, Reads i r rev (RingGroupedCentre.cursor fr s) (keys s)) ∧
      candidates? fr r rev = some (candidates keys) ∧
      ∀ ks, (∀ s, Reads i r rev (RingGroupedCentre.cursor fr s) (ks s)) →
        candidates ks = candidates keys := by
  intro r
  have ready : RingGroupedStereo.Ready f r := RingGroupedPublication.ready (RingGroupedGeometry.physical geom) f
  have each (s : Slot) := key_exact ready rev (RingGroupedCentre.cursor fr s)
    (RingGroupedCentre.valid fr s) (fr.direction s).property.1
  choose ks computed exactKey using each
  obtain ⟨keys,row⟩ := Option.isSome_iff_exists.mp
    (RingActivePairReport.four_full _ (fun s => Option.isSome_iff_exists.mpr ⟨ks s,computed s⟩))
  have same : keys = ks := funext fun s => Option.some.inj
    ((RingActivePairReport.four_at row s).symm.trans (computed s))
  subst keys
  refine ⟨ks,fun s => (exactKey s _).mpr rfl,by simp [candidates?,row],fun other legal => ?_⟩
  exact congrArg candidates (funext fun s => (exactKey s _).mp (legal s))

end TetraStereo.Engine.RingFullPathEligibility
assert_kernel_only TetraStereo.Engine.RingFullPathEligibility.frozen_candidates
assert_kernel_only TetraStereo.Engine.RingFullPathEligibility.promotion_patterns
