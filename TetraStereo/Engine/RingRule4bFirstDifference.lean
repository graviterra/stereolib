import TetraStereo.Engine.RingRule4bPathDecoding

/-! # Molecular sphere boundaries remain synchronized before divergence -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingRule4bFirstDifference
open OneCenter RingStereoSiblingPass RingFullPathPairs RingRule5Shape RingRule5SeedExchange
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Word)
open RingRetainedReferenceGroup (Path)
open RingStereoPriorityBlocks (paths word)
open RingTypedSphereDecoding (shape decodeRow decodeRow_word)
open private Good Good.mk Good.edge slotKind nextSlots grow_row slot_descending classes class_shapes class_paths class_word slotShape
  from TetraStereo.Engine.RingRule4bPathDecoding

/-- The complete pre-sign slots at a sphere, including non-emitting visits.
The list is empty after the walk has terminated. -/
def slots (rows : List (List Path)) (n : Nat) : List Path :=
  (rows[n]?.getD []).map eraseEndpoint

/-- All bits emitted by the first `n` spheres. -/
def prefixBits (rows : List (List Path)) (n : Nat) : List Bool :=
  (rows.take n).flatten.filterMap bitOf

private def decodePrefix (children : List Word → List (List Word)) (d : List Word) :
    Nat → Nat → List Path → List Bool → Option (List (List Path) × List Path × List Bool)
  | 0, _, slots, bits => some ([],slots,bits)
  | _+1, _, [], bits => some ([],[],bits)
  | fuel+1, n, a::slots, bits => do
    let (cs,rest) := decodeRow ((a::slots).map (slotShape d n)) bits
    let row := paths cs
    let next := order id (row.flatMap fun p =>
      (children (slotKind d n (eraseEndpoint p))).map (fun k => p ++ [k]))
    let (rows,boundary,tail) ← decodePrefix children d fuel (n+1) next rest
    return (row::rows,boundary,tail)

private theorem first_slots {i r rev s row out rows}
    (walk : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev s)) row out rows) :
    slots rows 0 = row.map (fun v => eraseEndpoint v.path) := by
  cases walk <;> simp [slots,List.map_map,Function.comp_def]

private theorem row_bits {i f r rev s d n} {row : List (FullVisit i)}
    (good : ∀ v ∈ row, Good f r rev s d n v) :
    (row.map FullVisit.path).filterMap bitOf = row.filterMap (fun v => likeAt i r rev s v.cursor) := by
  rw [List.filterMap_map]
  apply List.filterMap_congr
  intro v hv
  obtain ⟨p,k,_,_,hp,_⟩ := Good.edge (good v hv)
  change bitOf v.path = likeAt i r rev s v.cursor
  rw [hp]
  exact bitOf_snoc _ _ _

private theorem decode_walk {i f r rev s d row out rows}
    (ready : @RingGroupedStereo.Ready i f r)
    (walk : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev s)) row out rows) :
    ∀ fuel n, (∀ v ∈ row, Good f r rev s d n v) → ∀ tail : List Bool,
      decodePrefix (RingUnitTypeTransitions.offspring f r rev) d fuel n
        (row.map (fun v => eraseEndpoint v.path)) (prefixBits rows fuel ++ tail) =
        some (rows.take fuel,slots rows fuel,tail) := by
  induction walk with
  | stop => intro fuel n good tail; cases fuel <;> rfl
  | @sphere a row blocks next rest layers grow sorted below ih =>
    intro fuel n good tail
    cases fuel with
    | zero =>
      simp only [decodePrefix,prefixBits,List.take_zero,List.flatten_nil,List.filterMap_nil,List.nil_append]
      rw [first_slots (.sphere grow sorted below)]
    | succ fuel =>
      let xs := a::row
      let bit := likeAt i r rev s
      have sh := class_shapes ready good
      have ps := class_paths good
      obtain ⟨gn,perm⟩ := grow_row ready good grow sorted
      have sc := slot_descending gn sorted.descending
      have legal : Legal id ((xs.map FullVisit.path).flatMap (nextSlots f r rev d n))
          (next.map (fun v => eraseEndpoint v.path)) := ⟨perm,by simpa using sc⟩
      have ns : order id ((xs.map FullVisit.path).flatMap (nextSlots f r rev d n)) =
          next.map (fun v => eraseEndpoint v.path) := by
        simpa using ((legal_iff ..).mp legal).2.symm
      have input : prefixBits ((xs.map FullVisit.path)::layers) (fuel+1) =
          word (classes bit xs) ++ prefixBits layers fuel := by
        simp only [prefixBits,List.take_succ_cons,List.flatten_cons,List.filterMap_append]
        rw [row_bits good,class_word]
      change (do
        let (cs,rest') := decodeRow ((xs.map (fun v : FullVisit i => eraseEndpoint v.path)).map (slotShape d n))
          (prefixBits ((xs.map FullVisit.path)::layers) (fuel+1) ++ tail)
        let (rows',boundary,tail') ← decodePrefix _ d fuel (n+1)
          (order id ((paths cs).flatMap (nextSlots f r rev d n))) rest'
        pure (paths cs :: rows',boundary,tail')) = _
      rw [input,List.append_assoc,← sh,decodeRow_word]
      dsimp only
      rw [ps,ns,ih fuel (n+1) gn tail]
      rfl

/-- Equal emitted prefixes force identical signed path rows, and identical
complete unsigned slots at the next sphere. The hypotheses do not assume any
previous signed-path equality; the root's through-4a type determines the widths. -/
theorem prefix_alignment {i f r rev s t} (ready : @RingGroupedStereo.Ready i f r)
    {a b : Arm i} (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (tie : RingUnitTypeTransitions.key i r rev a = RingUnitTypeTransitions.key i r rev b)
    {out rows out' rows'}
    (left : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev s))
      [Oracle.root (likeAt i r rev s) a] out rows)
    (right : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev t))
      [Oracle.root (likeAt i r rev t) b] out' rows') (n : Nat)
    (same : prefixBits rows n = prefixBits rows' n) :
    rows.take n = rows'.take n ∧ slots rows n = slots rows' n := by
  have ga : Good f r rev s (RingUnitTypeTransitions.key i r rev a) 0
      (Oracle.root (likeAt i r rev s) a) := Good.mk va oa ⟨[],[],rfl,rfl,rfl,rfl⟩
  have gb : Good f r rev t (RingUnitTypeTransitions.key i r rev b) 0
      (Oracle.root (likeAt i r rev t) b) := Good.mk vb ob ⟨[],[],rfl,rfl,rfl,rfl⟩
  have l := decode_walk ready left n 0 (fun v hv => List.mem_singleton.mp hv ▸ ga) []
  have rhs := decode_walk ready right n 0 (fun v hv => List.mem_singleton.mp hv ▸ gb) []
  simp only [List.append_nil] at l rhs
  have initial : [Oracle.root (likeAt i r rev s) a].map (fun v => eraseEndpoint v.path) =
      [Oracle.root (likeAt i r rev t) b].map (fun v => eraseEndpoint v.path) := by
    simp [Oracle.root,eraseEndpoint,stripBit_step]
  rw [tie,initial,same,rhs] at l
  have result := Option.some.inj l
  exact ⟨(congrArg Prod.fst result).symm,(congrArg (fun p => p.2.1) result).symm⟩

end TetraStereo.Engine.RingRule4bFirstDifference
assert_kernel_only TetraStereo.Engine.RingRule4bFirstDifference.prefix_alignment
