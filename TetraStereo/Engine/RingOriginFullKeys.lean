import TetraStereo.Engine.RingOriginSeedWords
import TetraStereo.Engine.RingOriginStereoRanking

/-! Rebuild the unmarked full-path keys used in both public local publishers
with distances measured from the current active focus. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginFullKeys
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingStereoSiblingPass (Branch)
open RingRetainedStereoRefinement (Observation)
open RingOriginStereoRanking (recode Shaped priorityWith)
open RingSingleCycleComparison (CommonOrigin rebuilt)
open RingFullPathPairs (wordWith stepKey)
open RingRetainedChemicalTrace (Word)

/-- Recode the duplicate word and preserve all stereochemical coordinates. -/
abbrev recodeKey := RingPriorityCoordinate.fullKey

private abbrev edges (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q

def fullKey (i : Input) (read : Reader i) (rev : Bool)
    (rank : List Observation → Arm i → Option Branch) (q : Arm i) : Option RingFullPathEligibility.Key := do
  let u ← rank [] q
  let l ← rank [.lowercase] q
  let r ← wordWith read rev (edges i) (rank []) .R q
  let s ← wordWith read rev (edges i) (rank []) .S q
  let fixed ← wordWith read rev (edges i) (rank [.lowercase]) .R q
  return ⟨u.deep,max r s,l.word,fixed⟩

/-- Rebuild all ranks in every internal sibling and full-path sphere sort,
at both reference seeds, before constructing the final key. -/
def active (i : Input) (f : Site i) (read : Reader i) (rev : Bool) :=
  fullKey i read rev (priorityWith i (rebuilt i f) read rev)

theorem native (i : Input) (read : Reader i) (rev : Bool) (q : Arm i) :
    RingFullPathEligibility.key? i read rev q =
      fullKey i read rev (RingRetainedStereoRefinement.priority i read rev) q := rfl

private theorem of_scale {i : Input} (read : Reader i) (rev : Bool) (q : Arm i)
    (base rank : List Observation → Arm i → Option Branch)
    (shape : ∀ s c k, base s c = some k → Shaped k)
    (g : Nat → Nat) (inc : StrictMono g)
    (reads : ∀ s (c : Arm i), c.occurrence.val.root = q.occurrence.val.root →
      rank s c = (base s c).map (recode g)) :
    fullKey i read rev rank q =
      (fullKey i read rev base q).map (recodeKey g) := by
  let encode := RingPriorityCoordinate.second (List.map (List.map g))
  have mono : StrictMono encode := RingPriorityCoordinate.second_strictMono
    (RingPriorityCoordinate.map_strictMono (RingPriorityCoordinate.map_strictMono inc))
  have bits (s : List Observation) (seed : RS) :
      wordWith read rev (edges i) (rank s) seed q = wordWith read rev (edges i) (base s) seed q := by
    have below (a : Arm i) (on : a.occurrence.val.root = q.occurrence.val.root) :
        ∀ b ∈ edges i a, b.occurrence.val.root = q.occurrence.val.root :=
      fun b edge => (i.certified.localizedRerootChildren_root_eq _ _ _
        (i.certified.executableLocalizedRerootChildren_declarative _) edge).trans on
    apply RingOriginSeedWords.wordWith_exact read rev seed q _ _ _
      (fun c => c.occurrence.val.root = q.occurrence.val.root) rfl below encode mono rfl
    · intro c on
      rw [reads s c on]
      cases hit : base s c with
      | none => rfl
      | some k =>
        have shaped := shape s c k hit
        have len : 2 ≤ k.deep.length := by
          have bound := shaped.2
          simp only [Branch.deep,List.length_append,List.length_singleton]
          omega
        simp only [Option.map_some,Option.some.injEq, RingOriginStereoRanking.recode_deep g k shaped]
        exact (RingPriorityCoordinate.second_append _ _ _ len).symm
  unfold fullKey
  rw [bits [] .R,bits [] .S,bits [.lowercase] .R,reads [] q rfl,reads [.lowercase] q rfl]
  cases u : base [] q with
  | none => rfl
  | some k =>
    cases base [.lowercase] q <;>
      cases wordWith read rev (edges i) (base []) .R q <;>
      cases wordWith read rev (edges i) (base []) .S q <;>
      cases wordWith read rev (edges i) (base [.lowercase]) .R q <;> try rfl
    rename_i l rs ss fixed
    exact congrArg (fun deep => some (⟨deep,max rs ss,l.word,fixed⟩ : RingFullPathEligibility.Key))
      (RingOriginStereoRanking.recode_deep g k (shape [] q k u))

/-- The complete keys at every rooted arm share the identical computed Rule
4a, like/unlike, lowercase and fixed-reference suffixes. Both optional
reads are positive recodings of one common key, for arbitrary prior stores. -/
theorem factorization {i : Input} (f : Site i) (common : CommonOrigin i f.val.root) :
    ∃ (base : Reader i → Bool → Arm i → Option RingFullPathEligibility.Key)
      (a b : Nat), 0 < a ∧ 0 < b ∧ ∀ read rev (q : Arm i), q.occurrence.val.root = f.val.root →
        RingFullPathEligibility.key? i read rev q = (base read rev q).map (recodeKey (· * a)) ∧
        active i f read rev q = (base read rev q).map (recodeKey (· * b)) := by
  obtain ⟨keys,a,b,ha,hb,ranks⟩ := RingOriginStereoRanking.recursive_priority_factorization f common
  refine ⟨fun read rev => fullKey i read rev (priorityWith i keys read rev),a,b,ha,hb,?_⟩
  intro read rev q on
  rw [native]
  constructor
  · exact of_scale read rev q _ _ (RingOriginStereoRanking.priorityWith_shaped i keys read rev)
      _ (fun _ _ lt => Nat.mul_lt_mul_of_pos_right lt ha) (fun s c hc => (ranks read rev s c (hc.trans on)).1)
  · exact of_scale read rev q _ _ (RingOriginStereoRanking.priorityWith_shaped i keys read rev)
      _ (fun _ _ lt => Nat.mul_lt_mul_of_pos_right lt hb) (fun s c hc => (ranks read rev s c (hc.trans on)).2)

end TetraStereo.Engine.RingOriginFullKeys
assert_kernel_only TetraStereo.Engine.RingOriginFullKeys.factorization
