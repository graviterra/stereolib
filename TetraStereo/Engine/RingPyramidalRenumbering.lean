import TetraStereo.Engine.RingChemicalRenumberingBase
import TetraStereo.Engine.RingCoordinateReportTransport

set_option autoImplicit false
namespace TetraStereo.Engine.RingReportRenumber
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingActiveDistanceSchedule (View)
open RingPyramidalPublication RingFrameTransport RingStereoSiblingPass
open RingRetainedChemicalTrace (Word)

/-- Optional completed traversals agree up to order, including traversal refusal. -/
def OptionPerm {α : Type} : Option (List α) → Option (List α) → Prop
  | none, none => True
  | some xs, some ys => xs.Perm ys
  | _, _ => False

theorem OptionPerm.mapM {α β : Type} (f : α → Option β) {xs ys : List α}
    (p : xs.Perm ys) : OptionPerm (xs.mapM f) (ys.mapM f) := by
  induction p with
  | nil => exact .nil
  | @cons a xs ys p ih =>
    simp only [List.mapM_cons]
    cases f a <;> cases hx : xs.mapM f <;> cases hy : ys.mapM f <;>
      simp [hx,hy,OptionPerm] at ih ⊢
    exact ih
  | @swap a b xs =>
    simp only [List.mapM_cons]
    cases f a <;> cases f b <;> cases xs.mapM f <;> simp [OptionPerm]
    exact List.Perm.swap ..
  | @trans xs ys zs p q ih ij =>
    cases hx : xs.mapM f <;> cases hy : ys.mapM f <;> cases hz : zs.mapM f <;>
      simp_all only [OptionPerm]
    exact ih.trans ij

theorem crossed_perm {hs hs' ms ms' : List (Option RS)}
    (h : hs.Perm hs') (m : ms.Perm ms') :
    RingFullPathPublication.crossed hs ms = RingFullPathPublication.crossed hs' ms' := by
  unfold RingFullPathPublication.crossed
  rw [LocalizedChemicalRingPromotionAggregation.readingBalance_perm h,
      LocalizedChemicalRingPromotionAggregation.readingBalance_perm m]

/-- Sorting a permuted row gives the same atom order whenever priorities distinguish
all rows. This does not use atom IDs to resolve a tie. -/
theorem order_perm_of_nodup {α κ : Type} [LinearOrder κ] (key : α → κ)
    {xs ys : List α} (p : xs.Perm ys) (nd : (xs.map key).Nodup) :
    order key xs = order key ys := by
  have a := legal_order key xs
  have b := legal_order key ys
  have keys : (order key xs).map key = (order key ys).map key :=
    List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab)
      a.descending b.descending ((a.perm.trans (p.trans b.perm.symm)).map key)
  apply List.ext_getElem
  · exact (a.perm.trans (p.trans b.perm.symm)).length_eq
  · intro n hn hm
    apply List.inj_on_of_nodup_map nd
      (a.perm.mem_iff.mp (List.getElem_mem hn))
      (p.symm.mem_iff.mp (b.perm.mem_iff.mp (List.getElem_mem hm)))
    have e := List.getElem_of_eq keys (i := n) (by simpa using hn)
    simp only [List.getElem_map] at e
    exact e

theorem finishS_perm (sense : List Nat → Option RS) (a : Nat)
    {xs ys : List (Nat × List (List Word))} (p : xs.Perm ys) :
    finishS sense a xs = finishS sense a ys := by
  unfold finishS
  by_cases nd : (xs.map Prod.snd).Nodup
  · have nd' := (p.map Prod.snd).nodup_iff.mp nd
    simp only [nd,nd']
    rw [order_perm_of_nodup Prod.snd p nd]
  · have nd' : ¬(ys.map Prod.snd).Nodup := fun h => nd ((p.map Prod.snd).nodup_iff.mpr h)
    simp [nd,nd']

/-- Permuting the actual retained direction row cannot change one completed trial. -/
theorem trialS_perm {i : Input} (sense : List Nat → Option RS) (r : View i)
    (a : i.certified.Atom) (mark : Option Nat) {xs ys : List (Ligand i)} (p : xs.Perm ys) :
    trialS sense r a xs mark = trialS sense r a ys mark := by
  unfold trialS
  have perm := OptionPerm.mapM (rowOf i r mark) p
  cases hx : xs.mapM (rowOf i r mark) <;> cases hy : ys.mapM (rowOf i r mark) <;>
    simp_all only [OptionPerm,Option.bind_none,Option.bind_some]
  exact finishS_perm sense a.val perm

def Uniform {i : Input} (xs : List (Ligand i)) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ xs, x.priority = y.priority

open Classical in
theorem marksOf_uniform {i : Input} (xs : List (Ligand i)) :
    marksOf xs = if xs.length = 3 then
      if Uniform xs then xs.map (fun x => some x.atom) else [none] else [] := by
  classical
  match xs with
  | [] | [_] | [_,_] => simp [marksOf]
  | [x,y,z] =>
    have iff : Uniform [x,y,z] ↔ x.priority = y.priority ∧ y.priority = z.priority := by
      simp only [Uniform,List.mem_cons,List.mem_nil_iff,or_false]
      constructor
      · intro h; exact ⟨h x (Or.inl rfl) y (Or.inr (Or.inl rfl)),h y (Or.inr (Or.inl rfl)) z (Or.inr (Or.inr rfl))⟩
      · rintro ⟨a,b⟩ u (rfl|rfl|rfl) v (rfl|rfl|rfl) <;> simp_all
    simp only [marksOf,List.length_cons,List.length_nil,if_true]
    simp only [Bool.and_eq_true,beq_iff_eq]
    rw [iff]
    split_ifs <;> rfl
  | _ :: _ :: _ :: _ :: _ => simp [marksOf]

theorem marksOf_perm {i : Input} {xs ys : List (Ligand i)} (p : xs.Perm ys) :
    (marksOf xs).Perm (marksOf ys) := by
  classical
  have eq : Uniform xs ↔ Uniform ys := by
    unfold Uniform
    constructor <;> intro h x hx y hy
    · exact h x (p.mem_iff.mpr hx) y (p.mem_iff.mpr hy)
    · exact h x (p.mem_iff.mp hx) y (p.mem_iff.mp hy)
  rw [marksOf_uniform,marksOf_uniform,←p.length_eq]
  by_cases len : xs.length = 3
  · simp only [len,if_true]
    by_cases un : Uniform xs
    · rw [if_pos un,if_pos (eq.mp un)]; exact p.map _
    · rw [if_neg un,if_neg (fun h => un (eq.mpr h))]
  · simp only [len,if_false]
    exact .nil

theorem trial_rows_perm {i : Input} (sense : List Nat → Option RS) (r : View i)
    (a : i.certified.Atom) {xs ys : List (Ligand i)} (p : xs.Perm ys) :
    OptionPerm ((marksOf xs).mapM (trialS sense r a xs))
      ((marksOf ys).mapM (trialS sense r a ys)) := by
  have fn : trialS sense r a xs = trialS sense r a ys := funext fun mark => trialS_perm sense r a mark p
  rw [fn]
  exact OptionPerm.mapM _ (marksOf_perm p)

variable {i j : Input}
open RingRawRenumbering (AtomMap)
open RingRawRenumbering.AtomMap (arm site)
open LocalizedChemicalRingPhysicalSense (inputGeometry)

def renameLigand (r : AtomMap i j) (x : Ligand i) : Ligand j :=
  ⟨arm r x.arm,renameId r x.atom,x.priority⟩

theorem ligandOf_ids (i : Input) (v : View i) (rev : Bool) (t : Arm i) :
    ligandOf i v rev t = (t.occurrence.val.node.current?.map Fin.val).bind fun n =>
      (RingFullPathEligibility.key? i v rev t).map fun p => (⟨t,n,p⟩ : Ligand i) := by
  unfold ligandOf
  cases t.occurrence.val.node.current? <;> cases RingFullPathEligibility.key? i v rev t <;> rfl

theorem ligandOf_rename (r : AtomMap i j) (v : View i) (w : View j) (rev : Bool) (t : Arm i)
    (key : RingFullPathEligibility.key? j w rev (arm r t) = RingFullPathEligibility.key? i v rev t) :
    ligandOf j w rev (arm r t) = (ligandOf i v rev t).map (renameLigand r) := by
  rw [ligandOf_ids,ligandOf_ids,id_current,key]
  cases t.occurrence.val.node.current?.map Fin.val <;> cases RingFullPathEligibility.key? i v rev t <;> rfl

theorem finishS_rename (r : AtomMap i j) (rev : Bool) (a : i.certified.Atom)
    (rows : List (Nat × List (List Word))) :
    finishS (senseOf (inputGeometry j.certified) rev) (r.atoms a).val
      (rows.map fun x => (renameId r x.1,x.2)) =
    finishS (senseOf (inputGeometry i.certified) rev) a.val rows := by
  have sort : order Prod.snd (rows.map fun x => (renameId r x.1,x.2)) =
      (order Prod.snd rows).map (fun x => (renameId r x.1,x.2)) := by
    unfold order
    exact (List.map_mergeSort (f := fun x : Nat × List (List Word) => (renameId r x.1,x.2)) (l := rows) (r := fun (a b : Nat × List (List Word)) => decide (b.2 ≤ a.2)) (s := fun (a b : Nat × List (List Word)) => decide (b.2 ≤ a.2)) (fun _ _ _ _ => rfl)).symm
  unfold finishS
  simp only [List.map_map,Function.comp_def]
  rw [sort]
  simp only [List.map_map,Function.comp_def]
  have sense := read_ids r rev ((order Prod.snd rows).map Prod.fst ++ [a.val])
  simp only [List.map_append,List.map_map,List.map_cons,List.map_nil,rename_val,Function.comp_def] at sense
  rw [←sense]

theorem marksOf_rename (r : AtomMap i j) (xs : List (Ligand i)) :
    marksOf (xs.map (renameLigand r)) = (marksOf xs).map (Option.map (renameId r)) := by
  match xs with
  | [] | [_] | [_,_] | _ :: _ :: _ :: _ :: _ => rfl
  | [x,y,z] =>
    simp only [marksOf,List.map_cons,List.map_nil,renameLigand]
    split <;> rfl

theorem ligands_rename (r : AtomMap i j) (v : View i) (w : View j) (q : Site i) (rev : Bool)
    (keys : ∀ t, t ∈ RingRetainedAuxiliary.frame i.certified q → RingFullPathEligibility.key? j w rev (arm r t) = RingFullPathEligibility.key? i v rev t) :
    OptionPerm ((ligands? i q v rev).map (List.map (renameLigand r)))
      (ligands? j (site r q) w rev) := by
  rw [ligands_unfold,ligands_unfold]
  have per := OptionPerm.mapM (ligandOf j w rev) (frame_perm r q)
  rw [List.mapM_map] at per
  simp only [Function.comp_def] at per
  rw [mapM_congr_mem _ (fun t => (ligandOf i v rev t).map (renameLigand r)) _
    (fun t ht => ligandOf_rename r v w rev t (keys t ht))] at per
  rw [RingSpatialTransport.mapM_option_map] at per
  exact per

theorem ligandOf_arm {i : Input} {v : View i} {rev : Bool} {t : Arm i} {x : Ligand i}
    (h : ligandOf i v rev t = some x) : x.arm = t := by
  unfold ligandOf at h
  cases hc : t.occurrence.val.node.current? <;> cases hk : RingFullPathEligibility.key? i v rev t <;>
    simp [hc,hk] at h
  cases h
  rfl

theorem ligands_arms (i : Input) (q : Site i) (v : View i) (rev : Bool) (xs : List (Ligand i))
    (h : ligands? i q v rev = some xs) : xs.map Ligand.arm = RingRetainedAuxiliary.frame i.certified q := by
  exact mapM_map (f := ligandOf i v rev) (p := Ligand.arm) (k := id)
    (fun _ _ h => ligandOf_arm h) _ xs h |>.trans (List.map_id _)

variable (r : AtomMap i j) (v : View i) (w : View j)
theorem rowOf_rename (mark : Option Nat) (x : Ligand i)
    (words : ∀ n, (RingGroupedMark.arm? j w (renameId r n) (arm r x.arm)).map (fun b => b.2.word) =
      (RingGroupedMark.arm? i v n x.arm).map (fun b => b.2.word)) :
    rowOf j w (mark.map (renameId r)) (renameLigand r x) =
      (rowOf i v mark x).map (fun z => (renameId r z.1,z.2)) := by
  unfold rowOf markWord?
  cases mark with
  | none => rfl
  | some n =>
    change ((RingGroupedMark.arm? j w (renameId r n) (arm r x.arm)).map _).bind _ = _
    rw [words n]
    simp only []
    cases (RingGroupedMark.arm? i v n x.arm).map (fun b => b.2.word) <;> rfl

theorem trialS_rename (rev : Bool) (a : i.certified.Atom) (xs : List (Ligand i)) (mark : Option Nat)
    (words : ∀ n x, x ∈ xs →
      (RingGroupedMark.arm? j w (renameId r n) (arm r x.arm)).map (fun b => b.2.word) =
      (RingGroupedMark.arm? i v n x.arm).map (fun b => b.2.word)) :
    trialS (senseOf (inputGeometry j.certified) rev) w (r.atoms a)
      (xs.map (renameLigand r)) (mark.map (renameId r)) =
    trialS (senseOf (inputGeometry i.certified) rev) v a xs mark := by
  unfold trialS
  rw [List.mapM_map]
  simp only [Function.comp_def]
  rw [mapM_congr_mem _ (fun x => (rowOf i v mark x).map (fun z => (renameId r z.1,z.2))) xs
    (fun x hx => rowOf_rename r v w mark x (fun n => words n x hx))]
  rw [RingSpatialTransport.mapM_option_map]
  cases xs.mapM (rowOf i v mark) with
  | none => rfl
  | some rows => exact finishS_rename r rev a rows

theorem trial_list_rename (rev : Bool) (a : i.certified.Atom) (xs : List (Ligand i))
    (words : ∀ n x, x ∈ xs →
      (RingGroupedMark.arm? j w (renameId r n) (arm r x.arm)).map (fun b => b.2.word) =
      (RingGroupedMark.arm? i v n x.arm).map (fun b => b.2.word)) :
    (marksOf (xs.map (renameLigand r))).mapM
      (trialS (senseOf (inputGeometry j.certified) rev) w (r.atoms a) (xs.map (renameLigand r))) =
    (marksOf xs).mapM (trialS (senseOf (inputGeometry i.certified) rev) v a xs) := by
  rw [marksOf_rename,List.mapM_map]
  apply congrArg (fun f => (marksOf xs).mapM f)
  funext mark
  exact trialS_rename r v w rev a xs mark words

theorem hands_rename (q : Site i) (rev : Bool) (a : i.certified.Atom)
    (words : ∀ n t, t ∈ RingRetainedAuxiliary.frame i.certified q →
      (RingGroupedMark.arm? j w (renameId r n) (arm r t)).map (fun b => b.2.word) =
      (RingGroupedMark.arm? i v n t).map (fun b => b.2.word))
    (keys : ∀ t, t ∈ RingRetainedAuxiliary.frame i.certified q → RingFullPathEligibility.key? j w rev (arm r t) = RingFullPathEligibility.key? i v rev t) :
    OptionPerm (handsS (senseOf (inputGeometry i.certified) rev) i q v a rev)
      (handsS (senseOf (inputGeometry j.certified) rev) j (site r q) w (r.atoms a) rev) := by
  have lig := ligands_rename r v w q rev keys
  unfold handsS
  cases hx : ligands? i q v rev with
  | none =>
    cases hy : ligands? j (site r q) w rev <;> simp [hx,hy,OptionPerm] at lig ⊢
  | some xs =>
    cases hy : ligands? j (site r q) w rev with
    | none => simp [hx,hy,OptionPerm] at lig
    | some ys =>
      simp only [hx,hy,Option.map_some,OptionPerm] at lig
      simp only [Option.bind_some]
      have arms := ligands_arms i q v rev xs hx
      have localWords : ∀ n x, x ∈ xs →
          (RingGroupedMark.arm? j w (renameId r n) (arm r x.arm)).map (fun b => b.2.word) =
          (RingGroupedMark.arm? i v n x.arm).map (fun b => b.2.word) := by
        intro n x hx
        apply words n x.arm
        rw [←arms]
        exact List.mem_map.mpr ⟨x,hx,rfl⟩
      rw [←trial_list_rename r v w rev a xs localWords]
      exact trial_rows_perm _ w (r.atoms a) lig

theorem pLabels_rename (q : Site i) (a : i.certified.Atom)
    (words : ∀ n t, t ∈ RingRetainedAuxiliary.frame i.certified q →
      (RingGroupedMark.arm? j w (renameId r n) (arm r t)).map (fun b => b.2.word) =
      (RingGroupedMark.arm? i v n t).map (fun b => b.2.word))
    (keys : ∀ rev t, t ∈ RingRetainedAuxiliary.frame i.certified q → RingFullPathEligibility.key? j w rev (arm r t) = RingFullPathEligibility.key? i v rev t) :
    pLabels j (site r q) w (r.atoms a) = pLabels i q v a := by
  rw [←pLabelsG_input,←pLabelsG_input]
  unfold pLabelsG
  have len := (frame_perm r q).length_eq
  rw [List.length_map] at len
  rw [←len]
  by_cases shape : (RingRetainedAuxiliary.frame i.certified q).length = 3
  swap
  · simp [guard,shape]
  simp only [guard,shape,if_true,pure,bind,Option.bind]
  have hs := hands_rename r v w q false a words (keys false)
  have ms := hands_rename r v w q true a words (keys true)
  cases hi : handsS (senseOf (inputGeometry i.certified) false) i q v a false <;>
    cases hj : handsS (senseOf (inputGeometry j.certified) false) j (site r q) w (r.atoms a) false <;>
    cases mi : handsS (senseOf (inputGeometry i.certified) true) i q v a true <;>
    cases mj : handsS (senseOf (inputGeometry j.certified) true) j (site r q) w (r.atoms a) true <;>
    simp [hi,hj,mi,mj,OptionPerm] at hs ms ⊢
  exact crossed_perm hs.symm ms.symm

theorem publish_phosphorus_rename (q : Site i) (a : i.certified.Atom)
    (focus : focusP i q = some a)
    (words : ∀ n t, t ∈ RingRetainedAuxiliary.frame i.certified q →
      (RingGroupedMark.arm? j w (renameId r n) (arm r t)).map (fun b => b.2.word) =
      (RingGroupedMark.arm? i v n t).map (fun b => b.2.word))
    (keys : ∀ rev t, t ∈ RingRetainedAuxiliary.frame i.certified q →
      RingFullPathEligibility.key? j w rev (arm r t) = RingFullPathEligibility.key? i v rev t) :
    publish j (site r q) w = publish i q v := by
  unfold publish
  rw [focus_atom,focus]
  simp only [Option.map_some]
  exact congrArg some (pLabels_rename r v w q a words keys)

end TetraStereo.Engine.RingReportRenumber
assert_kernel_only TetraStereo.Engine.RingReportRenumber.pLabels_rename
assert_kernel_only TetraStereo.Engine.RingReportRenumber.publish_phosphorus_rename
