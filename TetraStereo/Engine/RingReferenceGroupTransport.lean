import TetraStereo.Engine.RingPathRankTransport

set_option autoImplicit false

namespace TetraStereo.Engine.RingReferenceGroupTransport
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader Labels unit upper)
open RingRetainedUnitPass (Reading)
open RingRetainedReferenceGroup (Path Hit Listing joinHits group senior)

private theorem flatMap_keys {α β κ γ : Type} [DecidableEq β]
    (keyA : α → κ) (keyB : β → κ) (f : α → List γ) (g : β → List γ)
    {xs : List α} {ys : List β} (keys : (xs.map keyA).Perm (ys.map keyB))
    (same : ∀ x ∈ xs, ∀ y ∈ ys, keyA x = keyB y → (f x).Perm (g y)) :
    (xs.flatMap f).Perm (ys.flatMap g) := by
  induction xs generalizing ys with
  | nil =>
    have : ys = [] := by simpa using keys.length_eq.symm
    subst ys
    exact .nil
  | cons x xs ih =>
    obtain ⟨y,hy,eqn⟩ := List.mem_map.mp (keys.mem_iff.mp (List.mem_cons_self))
    have move := List.perm_cons_erase hy
    have tails : (xs.map keyA).Perm ((ys.erase y).map keyB) := by
      have h := keys.trans (move.map keyB)
      simp only [List.map_cons] at h
      rw [eqn] at h
      exact h.cons_inv
    have rest := ih tails (fun a ha b hb e => same a (List.mem_cons_of_mem _ ha) b
      (List.mem_of_mem_erase hb) e)
    exact ((same x List.mem_cons_self y hy eqn.symm).append rest).trans
      (move.flatMap (fun _ _ => List.Perm.refl _)).symm

private theorem roots {i r q b v} (reading : Reading i r false q b)
    (seen : r q.occurrence = some v) : unit (v.map Prod.fst) = b.value := by
  cases reading with
  | node _ found _ _ _ _ _ _ =>
    obtain rfl := Option.some.inj (found.symm.trans seen)
    rfl

private theorem value_eq {a b : Branch} (tie : a.deep = b.deep) : a.value = b.value := by
  have words : a.word = b.word := by
    simpa [Branch.deep] using congrArg List.getLast? tie
  simpa [Branch.word] using congrArg (fun w => w.head?.map List.head?) words

private theorem join_paths (v : Option Labels) (parts : List (Branch × List Hit)) :
    (joinHits v parts).map Hit.path =
      (if unit (v.map Prod.fst) = 2 then [[]] else []) ++
      parts.flatMap (fun p => (p.2.map Hit.path).map (List.cons p.1.deep)) := by
  have tail : ((parts.flatMap fun (k, hs) => hs.map fun h => { h with path := k.deep :: h.path }).map Hit.path) =
      parts.flatMap (fun p => (p.2.map Hit.path).map (List.cons p.1.deep)) := by
    simp [List.map_flatMap,List.map_map,Function.comp_def]
  rw [joinHits,List.map_append]
  change (((upper (v.map Prod.fst)).map (fun h => Hit.mk [] h)).toList.map Hit.path) ++
    ((parts.flatMap fun (k, hs) => hs.map fun h => { h with path := k.deep :: h.path }).map Hit.path) = _
  rw [tail]
  rcases v with _ | ⟨(_|_),(_|_)⟩ <;> simp [unit,upper]

private theorem readings {i : Input} {r : Reader i} {q : Arm i}
    {parts : List (Branch × List Hit)} {lookup : Arm i → Option (Branch × List Hit)}
    (found : (i.certified.executableLocalizedRerootChildren q).mapM lookup = some parts)
    (rank : ∀ c ∈ i.certified.executableLocalizedRerootChildren q, ∀ {k hs},
      lookup c = some (k,hs) → Reading i r false c k) :
    List.Forall₂ (Reading i r false) (i.certified.executableLocalizedRerootChildren q)
      (parts.map Prod.fst) := by
  have h := TerminalTie.mapM_forall₂ _ _ _ found
  clear found
  generalize i.certified.executableLocalizedRerootChildren q = cs at *
  induction h with
  | nil => exact .nil
  | @cons c p cs ps head tail ih =>
    exact .cons (rank c List.mem_cons_self head)
      (ih (fun c hc => rank c (List.mem_cons_of_mem _ hc)))

/-- Through-4a equality fixes the multiset of complete structural paths to
uppercase occurrences, without retaining any hand values. -/
theorem Listing.paths_perm {i : Input} {r : Reader i} {q : Arm i} {xs : List Hit}
    (left : Listing i r q xs) {j : Input} {v : Reader j} {p : Arm j} {ys : List Hit}
    (right : Listing j v p ys) {a b : Branch} (ra : Reading i r false q a)
    (rb : Reading j v false p b) (tie : a.deep = b.deep) :
    (xs.map Hit.path).Perm (ys.map Hit.path) := by
  induction left generalizing j v p ys a b with
  | @node q u parts seen physical lookup found rank below ih =>
    cases right with
    | @node p w other seen' physical' lookup' found' rank' below' =>
      rw [join_paths,join_paths]
      have rootsEq : unit (u.map Prod.fst) = unit (w.map Prod.fst) :=
        (roots ra seen).trans ((value_eq tie).trans (roots rb seen').symm)
      rw [rootsEq]
      apply List.Perm.append (List.Perm.refl _)
      apply flatMap_keys (fun p : Branch × List Hit => p.1.deep)
        (fun p : Branch × List Hit => p.1.deep)
      · simpa [List.map_map,Function.comp_def] using
          RingPathRankTransport.sibling_keys ra rb tie (readings found rank) (readings found' rank')
      · rintro ⟨k,hs⟩ hp ⟨l,ts⟩ ht same
        obtain ⟨c,hc,get⟩ := RingRetainedUnitPass.forOutput found hp
        obtain ⟨d,hd,get'⟩ := RingRetainedUnitPass.forOutput found' ht
        have h := ih c hc get (below' d hd get') (rank c hc get) (rank' d hd get') same
        simpa [same] using h.map (List.cons l.deep)

/-- Selecting the senior structural path retains its full multiplicity. -/
theorem group_paths_perm {xs ys : List Hit}
    (same : (xs.map Hit.path).Perm (ys.map Hit.path)) :
    ((group xs).map Hit.path).Perm ((group ys).map Hit.path) := by
  have any_eq (p : Path) : xs.any (fun h => senior h.path p) = ys.any (fun h => senior h.path p) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [List.any_eq_true,List.mem_map,exists_exists_and_eq_and] using
      (show (∃ x ∈ xs.map Hit.path, senior x p = true) ↔
        (∃ y ∈ ys.map Hit.path, senior y p = true) by simp only [same.mem_iff])
  have left : (group xs).map Hit.path = (xs.map Hit.path).filter
      (fun p => !(ys.any fun h => senior h.path p)) := by
    rw [List.filter_map]
    simp only [Function.comp_def,group,any_eq]
  have right : (group ys).map Hit.path = (ys.map Hit.path).filter
      (fun p => !(ys.any fun h => senior h.path p)) := by rw [List.filter_map]; rfl
  rw [left,right]
  exact same.filter _

theorem group_length_eq {xs ys : List Hit}
    (same : (xs.map Hit.path).Perm (ys.map Hit.path)) : (group xs).length = (group ys).length := by
  simpa using (group_paths_perm same).length_eq

theorem Listing.group_length_eq {i : Input} {r : Reader i} {q : Arm i} {xs : List Hit}
    (left : Listing i r q xs) {j : Input} {v : Reader j} {p : Arm j} {ys : List Hit}
    (right : Listing j v p ys) {a b : Branch} (ra : Reading i r false q a)
    (rb : Reading j v false p b) (tie : a.deep = b.deep) :
    (group xs).length = (group ys).length :=
  RingReferenceGroupTransport.group_length_eq (Listing.paths_perm left right ra rb tie)

end TetraStereo.Engine.RingReferenceGroupTransport

assert_kernel_only TetraStereo.Engine.RingReferenceGroupTransport.Listing.paths_perm
assert_kernel_only TetraStereo.Engine.RingReferenceGroupTransport.Listing.group_length_eq
