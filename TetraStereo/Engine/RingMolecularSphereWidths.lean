import TetraStereo.Engine.RingMolecularDonorVerdict
import TetraStereo.Engine.RingUnitTypeTransitions

/-! A through-4a tie synchronizes complete molecular sphere widths, even
after the first signed disagreement and across different reference hands. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMolecularSphereWidths
open OneCenter CertifiedLocalizedCIPInput RingMolecularDonorClasses RingMolecularDonorVerdict
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingStereoSphereInventory (Visit SignedPath project)
open RingFullPathPairs (bitOf likeAt)
open RingUnitTypeTransitions (key kids Valid On Carrier offspring emits)
open RingRetainedChemicalTrace (Word)
open RingUnorderedSphereReading (layers?)
open private start nextWith eraseVisits from TetraStereo.Engine.RingStereoSphereInventory
abbrev TypeKey := List Word

private inductive Widths (children : TypeKey → List TypeKey) : List TypeKey → List Nat → Prop
  | stop : Widths children [] []
  | step {row next rest} (ne : row ≠ []) (p : next.Perm (row.flatMap children))
      (tail : Widths children next rest) : Widths children row (row.countP emits :: rest)

private theorem Widths.unique {kids xs ys a b} (l : Widths kids xs a) (r : Widths kids ys b)
    (perm : xs.Perm ys) : a = b := by
  induction l generalizing ys b with
  | stop => obtain rfl := perm.symm.eq_nil; cases r with
    | stop => rfl
    | step ne => contradiction
  | step ne p _ ih =>
    cases r with
    | stop => exact (ne perm.eq_nil).elim
    | step _ q tail => exact congrArg₂ List.cons (perm.countP_eq _) (ih tail (p.trans ((perm.flatMap_right _).trans q.symm)))

private def Good {i : Input} (f : Site i) (r : Reader i) (rev : Bool) (s : RS) (v : Visit i) : Prop :=
  Valid v.arm ∧ On f v.arm ∧ bitOf (project s v.path) = likeAt i r rev s v.arm

private def typeOf {i : Input} (r : Reader i) (rev : Bool) (v : Visit i) := key i r rev v.arm

private theorem source_mem {α β : Type} {R : α → β → Prop} {xs ys} (pairs : List.Forall₂ R xs ys)
    {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction pairs with
  | nil => contradiction
  | cons h _ ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_,List.mem_cons_self,h⟩
    · obtain ⟨x,hx,t⟩ := ih hy
      exact ⟨x,.tail _ hx,t⟩

private theorem refine_pairs {α β : Type} {P Q : α → β → Prop} {xs ys} (rel : List.Forall₂ P xs ys)
    (ok : ∀ x ∈ xs, ∀ y, P x y → Q x y) : List.Forall₂ Q xs ys := by
  induction rel with
  | nil => exact .nil
  | cons h _ ih => exact .cons (ok _ List.mem_cons_self _ h) (ih (fun x hx => ok x (.tail _ hx)))

private theorem next_facts {i f r rev s} (ready : @RingGroupedStereo.Ready i f r)
    {rank : Arm i → Option RingStereoSiblingPass.Branch} {v : Visit i} {cs}
    (good : Good f r rev s v) (found : nextWith r rev (kids i) rank v = some cs) :
    (∀ w ∈ cs, Good f r rev s w) ∧
      (cs.map (typeOf r rev)).Perm (offspring f r rev (typeOf r rev v)) := by
  let parent : Carrier f := ⟨v.arm,good.1,good.2.1⟩
  have rel := TerminalTie.mapM_forall₂ _ _ _ found
  have prop : List.Forall₂ (fun (c : Arm i) (w : Visit i) =>
      w.arm = c ∧ bitOf (project s w.path) = likeAt i r rev s c) (kids i v.arm) cs := by
    apply rel.imp
    intro c w produced
    obtain ⟨k,_,val⟩ := Option.bind_eq_some_iff.mp produced
    cases Option.some.inj val
    exact ⟨rfl,by simp [project,RingFullPathPairs.bitOf_snoc,likeAt]⟩
  have heads : cs.map Visit.arm = kids i v.arm := by
    generalize ha : kids i v.arm = as at prop ⊢
    clear * - prop
    induction prop with
    | nil => rfl
    | cons h _ ih => simp [h.1,ih]
  refine ⟨?_,?_⟩
  · intro w hw
    obtain ⟨c,hc,cur,bit⟩ := source_mem prop hw
    have frame := i.certified.executableLocalizedRerootChildren_declarative v.arm
    unfold Good
    rw [cur]
    exact ⟨i.certified.localizedRerootChild_valid _ _ _ frame hc,
      (i.certified.localizedRerootChildren_root_eq _ _ _ frame hc).trans good.2.1,bit⟩
  · have same := RingUnitTypeTransitions.offspring_exact ready rev parent
    have eqn : (RingUnitTypeTransitions.children parent).map (RingUnitTypeTransitions.kind r rev) =
        (kids i v.arm).map (key i r rev) := by
      rw [← RingUnitTypeTransitions.children_val parent,List.map_map]; rfl
    rw [eqn] at same
    change (cs.map (key i r rev ∘ Visit.arm)).Perm _
    rw [←List.map_map,heads]
    exact same.symm

private def rowBits {i : Input} (s : RS) (vs : List (Visit i)) :=
  word s (↑(vs.map Visit.path))

private theorem row_length {i f r rev s} (ready : @RingGroupedStereo.Ready i f r)
    {row : List (Visit i)} (good : ∀ v ∈ row, Good f r rev s v) :
    (rowBits s row).length = (row.map (typeOf r rev)).countP emits := by
  rw [rowBits,word_exact]
  change (RingUnorderedSphereReading.readRow (project s) bitOf (row.map Visit.path)).length = _
  unfold RingUnorderedSphereReading.readRow
  rw [List.length_filterMap_eq_countP]
  rw [((RingStereoSiblingPass.legal_order id _).perm.countP_eq _)]
  simp only [List.countP_filter,Bool.and_self,List.countP_map]
  apply List.countP_congr
  intro v hv
  have h := good v hv
  exact Bool.eq_iff_iff.mp ((congrArg Option.isSome h.2.2).trans (RingUnitTypeTransitions.emits_exact ready rev ⟨v.arm,h.1,h.2.1⟩ s))

private theorem layers_widths {i f r rev s} (ready : @RingGroupedStereo.Ready i f r)
    (rank : Arm i → Option RingStereoSiblingPass.Branch) (n : Nat) (row : List (Visit i))
    {rs : List (List (Visit i))} (good : ∀ v ∈ row, Good f r rev s v)
    (got : layers? (nextWith r rev (kids i) rank) n row = some rs) :
    Widths (offspring f r rev) (row.map (typeOf r rev)) (rs.map (fun vs => (rowBits s vs).length)) := by
  induction n generalizing row rs with
  | zero =>
    cases row with
    | nil => cases got; exact .stop
    | cons _ _ => contradiction
  | succ n ih =>
    cases row with
    | nil => cases got; exact .stop
    | cons v vs =>
      simp only [layers?] at got
      obtain ⟨blocks,found,h⟩ := Option.bind_eq_some_iff.mp got
      obtain ⟨rest,run,out⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj out
      have rel := TerminalTie.mapM_forall₂ _ _ _ found
      have each : List.Forall₂ (fun (w : Visit i) (bs : List (Visit i)) =>
        (∀ t ∈ bs, Good f r rev s t) ∧
          (bs.map (typeOf r rev)).Perm (offspring f r rev (typeOf r rev w))) (v::vs) blocks := by
        exact refine_pairs rel (fun w hw b prod => next_facts ready (good w hw) prod)
      have fresh (t : Visit i) (mem : t ∈ blocks.flatten) : Good f r rev s t := by
        obtain ⟨b,hb,hm⟩ := List.mem_flatten.mp mem
        obtain ⟨_,_,g,_⟩ := source_mem each hb
        exact g t hm
      have perm : (blocks.flatten.map (typeOf r rev)).Perm
          (((v::vs).map (typeOf r rev)).flatMap (offspring f r rev)) := by
        generalize hr : v::vs = qs at each ⊢
        clear * - each
        induction each with
        | nil => exact .nil
        | cons h _ ih => simpa using h.2.append ih
      simp only [List.map_cons,row_length ready good]
      exact .step (by simp) perm (ih _ fresh run)

private theorem from_groups {i f r rev s} (ready : @RingGroupedStereo.Ready i f r)
    (os : List RingRetainedStereoRefinement.Observation) (q : Arm i) (v : Valid q) (on : On f q)
    {gs : Spheres} (found : groups? i r rev os s q = some gs) :
    Widths (offspring f r rev) [key i r rev q] (gs.map (fun g => (g.flatMap Group.word).length)) := by
  unfold groups? RingStereoSphereInventory.inventory? RingStereoSphereInventory.inventoryWith at found
  obtain ⟨inv,h,rfl⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨vs,run,rfl⟩ := Option.map_eq_some_iff.mp h
  have good : Good f r rev s (start r rev q) := by
    refine ⟨v,on,?_⟩
    exact RingFullPathPairs.bitOf_snoc [] [] (likeAt i r rev s q)
  have out := layers_widths ready _ _ [start r rev q] (fun w hw => List.mem_singleton.mp hw ▸ good) run
  simpa only [eraseVisits,List.map_map,Function.comp_def,word,rowBits] using out

/-- Through-4a equality gives the same number of emitting donors in every
sphere. Geometry/reader are fixed, but the two seeds and the two subsequent
rank-stage lists may be chosen independently. -/
theorem equal_widths {i f r rev s t os ps} (ready : @RingGroupedStereo.Ready i f r)
    {u v : Arm i} (vu : Valid u) (vv : Valid v) (ou : On f u) (ov : On f v)
    (tie : key i r rev u = key i r rev v) {a b : Spheres}
    (left : groups? i r rev os s u = some a) (right : groups? i r rev ps t v = some b) :
    a.map (fun x => (x.flatMap Group.word).length) = b.map (fun x => (x.flatMap Group.word).length) :=
  (from_groups ready os u vu ou left).unique (from_groups ready ps v vv ov right) (by rw [tie])

def sphereWords (gs : Spheres) := gs.map (List.flatMap Group.word)

private theorem compare_blocks (a b x y : List Bool) (len : a.length = b.length) :
    compare (a++x) (b++y) = (compare a b).then (compare x y) := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons v vs ih =>
    cases b with
    | nil => simp at len
    | cons w ws =>
      rw [List.length_cons,List.length_cons] at len
      simp only [List.cons_append,List.compare_cons_cons,ih _ (Nat.succ.inj len),Ordering.then_assoc]

private theorem first_row (xs ys : List (List Bool)) (widths : xs.map List.length = ys.map List.length)
    (ne : xs.flatten ≠ ys.flatten) :
    ∃ prior x y later rest, xs = prior ++ x::later ∧ ys = prior ++ y::rest ∧
      x.length = y.length ∧ x ≠ y ∧ compare xs.flatten ys.flatten = compare x y := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at widths
    | cons y ys =>
      obtain ⟨size,tail⟩ := List.cons.inj widths
      by_cases e : x = y
      · subst y
        have different : xs.flatten ≠ ys.flatten := fun same => ne (by simp [same])
        obtain ⟨pr,u,v,as,bs,ha,hb,n,d,decisive⟩ := ih ys tail different
        exact ⟨x::pr,u,v,as,bs,congrArg (x::·) ha,congrArg (x::·) hb,n,d,by
          simpa [compare_blocks x x _ _ rfl] using decisive⟩
      · have strict : compare x y ≠ .eq := fun z => e (Std.compare_eq_eq_iff_eq.mp z)
        exact ⟨[],x,y,xs,ys,rfl,rfl,size,e,by
          simp only [List.flatten_cons,compare_blocks _ _ _ _ size]
          cases h : compare x y <;> simp_all⟩

/-- A strict fixed-seed comparison after a through-4a tie has a first
complete sphere of equal width that differs. Its own direction decides the
full comparison. All earlier sphere words agree, including silent spheres. -/
theorem first_sphere {i f r rev s t os ps} (ready : @RingGroupedStereo.Ready i f r)
    {u v : Arm i} (vu : Valid u) (vv : Valid v) (ou : On f u) (ov : On f v)
    (tie : key i r rev u = key i r rev v) {a b : Spheres}
    (left : groups? i r rev os s u = some a) (right : groups? i r rev ps t v = some b)
    (ne : bits a ≠ bits b) :
    ∃ prior x y later rest, sphereWords a = prior ++ x::later ∧ sphereWords b = prior ++ y::rest ∧
      x.length = y.length ∧ x ≠ y ∧ compare (bits a) (bits b) = compare x y := by
  have widths := equal_widths ready vu vv ou ov tie left right
  have same (g : Spheres) : (sphereWords g).flatten = bits g := by simp [sphereWords,bits,List.flatMap_def]
  simpa only [same] using first_row (sphereWords a) (sphereWords b)
    (by simpa only [sphereWords,List.map_map,Function.comp_def] using widths) (by simpa only [same] using ne)

/-- Rule 4b uses the best fixed-seed word. Rule 5 uses the fixed-R word
from the stage that includes the lowercase priority. -/
inductive Field where
  | bestFourB | fixedR
  deriving DecidableEq, Repr

def Field.value : Field → RingFullPathEligibility.Key → List Bool
  | .bestFourB,k => k.bestFourB
  | .fixedR,k => k.fixedR

def Field.stages : Field → List RingRetainedStereoRefinement.Observation
  | .bestFourB => []
  | .fixedR => [.lowercase]

private theorem chosen {i r rev} {q : Arm i} {k : RingFullPathEligibility.Key}
    (got : RingFullPathEligibility.key? i r rev q = some k) (field : Field) :
    key i r rev q = k.throughFourA ∧ ∃ s gs, (field = .fixedR → s = .R) ∧
      groups? i r rev field.stages s q = some gs ∧ bits gs = field.value k := by
  rw [←RingMolecularDonorVerdict.key_exact] at got
  unfold RingMolecularDonorVerdict.key? at got
  obtain ⟨u,hu,h⟩ := Option.bind_eq_some_iff.mp got
  obtain ⟨l,_,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨x,hx,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨y,hy,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨z,hz,out⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj out
  refine ⟨by simp [key,hu],?_⟩
  cases field with
  | fixedR =>
    obtain ⟨gs,found,values⟩ := Option.map_eq_some_iff.mp hz
    exact ⟨.R,gs,fun _ => rfl,found,values⟩
  | bestFourB =>
    rcases le_total x y with le | le
    · obtain ⟨gs,found,values⟩ := Option.map_eq_some_iff.mp hy
      exact ⟨.S,gs,by simp,found,by simpa [Field.value,max_eq_right le] using values⟩
    · obtain ⟨gs,found,values⟩ := Option.map_eq_some_iff.mp hx
      exact ⟨.R,gs,by simp,found,by simpa [Field.value,max_eq_left le] using values⟩

/-- For a strict native best-4b or fixed-R word, recover the actual reference
on each arm, both complete per-sphere words, and the first disputed sphere.
A fixed-R decision only determines the ordinary order if preceding fields tie. -/
theorem native_first_sphere {i f r rev} (ready : @RingGroupedStereo.Ready i f r)
    {u v : Arm i} (vu : Valid u) (vv : Valid v) (ou : On f u) (ov : On f v)
    {ka kb : RingFullPathEligibility.Key}
    (lu : RingFullPathEligibility.key? i r rev u = some ka)
    (rv : RingFullPathEligibility.key? i r rev v = some kb)
    (tie : ka.throughFourA = kb.throughFourA) (field : Field) (ne : field.value ka ≠ field.value kb) :
    ∃ s t a b, (field = .fixedR → s = .R ∧ t = .R) ∧
      groups? i r rev field.stages s u = some a ∧ groups? i r rev field.stages t v = some b ∧
      bits a = field.value ka ∧ bits b = field.value kb ∧
      ∃ prior x y later rest, sphereWords a = prior ++ x::later ∧ sphereWords b = prior ++ y::rest ∧
        x.length = y.length ∧ x ≠ y ∧ compare (field.value ka) (field.value kb) = compare x y := by
  obtain ⟨ku,s,a,fixa,ha,xa⟩ := chosen lu field
  obtain ⟨kv,t,b,fixb,hb,xb⟩ := chosen rv field
  refine ⟨s,t,a,b,fun h => ⟨fixa h,fixb h⟩,ha,hb,xa,xb,?_⟩
  rw [←xa,←xb] at ne ⊢
  exact first_sphere ready vu vv ou ov (ku.trans (tie.trans kv.symm)) ha hb ne

private theorem split_words (xs ys : List (List Bool)) (widths : xs.map List.length = ys.map List.length)
    (same : xs.flatten = ys.flatten) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at widths
    | cons y ys =>
      obtain ⟨w,rest⟩ := List.cons.inj widths
      change x ++ xs.flatten = y ++ ys.flatten at same
      have head := congrArg (List.take x.length) same
      simp only [List.take_left] at head
      rw [w,List.take_left] at head
      subst y
      exact congrArg (x::·) (ih ys rest (List.append_cancel_left same))

/-- Complete molecular evidence for the two ordinary fields read by donor sphere. -/
def Compared {i : Input} (r : Reader i) (rev : Bool) (a b : Arm i) : Prop :=
    ∃ ka kb, RingFullPathEligibility.key? i r rev a = some ka ∧
      RingFullPathEligibility.key? i r rev b = some kb ∧
      (ka.throughFourA = kb.throughFourA → ∀ field : Field, ∃ s t ga gb,
        (field = .fixedR → s = .R ∧ t = .R) ∧
        groups? i r rev field.stages s a = some ga ∧ groups? i r rev field.stages t b = some gb ∧
        bits ga = field.value ka ∧ bits gb = field.value kb ∧
        ((sphereWords ga = sphereWords gb ∧ field.value ka = field.value kb) ∨
          ∃ prior x y later rest, sphereWords ga = prior ++ x::later ∧ sphereWords gb = prior ++ y::rest ∧
            x.length = y.length ∧ x ≠ y ∧ compare (field.value ka) (field.value kb) = compare x y))

/-- At an actual publication or root call the public store supplies both keys and
class traces on every valid arm of this root, including inward rerooted arms. -/
theorem public_arms {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {root : i.certified.Atom} {batch : Nat} {f : Site i} (called : RingGlobalComparison.Called i root batch f)
    (rev : Bool) (a b : Arm i) (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b) :
    Compared (RingGlobalComparison.prior i root batch) rev a b := by
  let r := RingGlobalComparison.prior i root batch
  have ready : RingGroupedStereo.Ready f r := by
    dsimp only [r]
    rw [RingGlobalComparison.prior_exact called]
    exact RingChemicalGraphProof.ready geom f
  obtain ⟨ka,hu,_⟩ := RingFullPathEligibility.key_exact ready rev a va oa
  obtain ⟨kb,hv,_⟩ := RingFullPathEligibility.key_exact ready rev b vb ob
  refine ⟨ka,kb,hu,hv,?_⟩
  intro tie field
  by_cases eqn : field.value ka = field.value kb
  · obtain ⟨ku,s,ga,sa,ha,xa⟩ := chosen hu field
    obtain ⟨kv,t,gb,sb,hb,xb⟩ := chosen hv field
    refine ⟨s,t,ga,gb,fun p => ⟨sa p,sb p⟩,ha,hb,xa,xb,Or.inl ⟨?_,eqn⟩⟩
    apply split_words
    · simpa only [sphereWords,List.map_map,Function.comp_def] using
        equal_widths ready va vb oa ob (ku.trans (tie.trans kv.symm)) ha hb
    · simpa [sphereWords,bits,List.flatMap_def] using xa.trans (eqn.trans xb.symm)
  · obtain ⟨s,t,ga,gb,fixR,ha,hb,xa,xb,first⟩ :=
      native_first_sphere ready va vb oa ob hu hv tie field eqn
    exact ⟨s,t,ga,gb,fixR,ha,hb,xa,xb,Or.inr first⟩


/-- Any two slots in the tetrahedral frame of a reached public call. -/
theorem public_spheres {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {root : i.certified.Atom} {batch : Nat} {f : Site i} (called : RingGlobalComparison.Called i root batch f)
    (fr : RingNestedActivePair.Frame i f) (rev : Bool) (u v : RingActivePairReport.Slot) :
    Compared (RingGlobalComparison.prior i root batch) rev
      (RingGroupedCentre.cursor fr u) (RingGroupedCentre.cursor fr v) :=
  public_arms geom called rev _ _ (RingGroupedCentre.valid fr u) (RingGroupedCentre.valid fr v)
    (fr.direction u).property.1 (fr.direction v).property.1

/-- Any two real arms enumerated by the public pyramidal ligand reader. -/
theorem public_frame_arms {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {root : i.certified.Atom} {batch : Nat} {f : Site i} (called : RingGlobalComparison.Called i root batch f)
    (rev : Bool) (a b : Arm i) (ha : a ∈ RingRetainedAuxiliary.frame i.certified f)
    (hb : b ∈ RingRetainedAuxiliary.frame i.certified f) :
    Compared (RingGlobalComparison.prior i root batch) rev a b := by
  let top : Arm i := ⟨f,none⟩
  have frame := i.certified.executableLocalizedRerootChildren_declarative top
  exact public_arms geom called rev a b
    (i.certified.localizedRerootChild_valid top a _ frame ha)
    (i.certified.localizedRerootChild_valid top b _ frame hb)
    (i.certified.localizedRerootChildren_root_eq top a _ frame ha)
    (i.certified.localizedRerootChildren_root_eq top b _ frame hb)

end TetraStereo.Engine.RingMolecularSphereWidths
assert_kernel_only TetraStereo.Engine.RingMolecularSphereWidths.equal_widths
assert_kernel_only TetraStereo.Engine.RingMolecularSphereWidths.first_sphere
assert_kernel_only TetraStereo.Engine.RingMolecularSphereWidths.native_first_sphere
assert_kernel_only TetraStereo.Engine.RingMolecularSphereWidths.public_spheres
assert_kernel_only TetraStereo.Engine.RingMolecularSphereWidths.public_arms
assert_kernel_only TetraStereo.Engine.RingMolecularSphereWidths.public_frame_arms
