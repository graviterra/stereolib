import TetraStereo.Engine.RingPriorityCoordinate
import TetraStereo.Engine.RingFullPathPairs
import TetraStereo.Engine.RingCoordinateReportTransport

/-! Preserve the actual emitted like/unlike word when the complete priorities
at every edge of a retained path are recoded in a common order. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginSeedWords
open OneCenter RingFullPathPairs RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Word)
open RingPriorityCoordinate (second)
open private nextWith from TetraStereo.Engine.RingFullPathPairs

private theorem mapM_transport {α β γ : Type} (xs : List α) (f : α → Option β)
    (g : α → Option γ) (e : β → γ) (eqn : ∀ x ∈ xs, g x = (f x).map e) :
    xs.mapM g = (xs.mapM f).map (List.map e) :=
  (RingFrameTransport.mapM_congr_mem _ _ _ eqn).trans (RingSpatialTransport.mapM_option_map f e xs)

/-- Run both traversals on their own complete sorted frontiers. A rank lookup
can fail, and the frontier can end before or after the supplied fuel. -/
theorem sphere_transport {α κ : Type} [LinearOrder κ] (key : α → κ)
    (e : α → α) (D : α → Prop) (next alt : α → Option (List α))
    (order_eq : ∀ xs : List α, order key (xs.map e) = (order key xs).map e)
    (step : ∀ x, D x → alt (e x) = (next x).map (List.map e))
    (closed : ∀ x, D x → ∀ ys, next x = some ys → ∀ y ∈ ys, D y)
    (n : Nat) (xs : List α) (domain : ∀ x ∈ xs, D x) :
    sphereRun key alt n (xs.map e) = (sphereRun key next n xs).map (List.map e) := by
  induction n generalizing xs with
  | zero => cases xs <;> rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      let row := x :: xs
      have blocks : (row.map e).mapM alt = (row.mapM next).map (List.map (List.map e)) := by
        rw [List.mapM_map]
        exact mapM_transport row next _ _ (fun x hx => step x (domain x hx))
      simp only [List.map_cons,sphereRun]
      change ((row.map e).mapM alt >>= _) = Option.map _ (row.mapM next >>= _)
      rw [blocks]
      cases found : row.mapM next with
      | none => rfl
      | some bs =>
        have ok : ∀ u ∈ order key bs.flatten, D u := by
          intro u hu
          obtain ⟨b,hb,h⟩ := List.mem_flatten.mp ((legal_order key bs.flatten).perm.mem_iff.mp hu)
          obtain ⟨p,hp,hb'⟩ := RingRetainedUnitPass.forOutput found hb
          exact closed p (domain p hp) b hb' u h
        change (sphereRun key alt n (order key (bs.map (List.map e)).flatten) >>= fun rest =>
          some (row.map e ++ rest)) =
          (sphereRun key next n (order key bs.flatten) >>= fun rest => some (row ++ rest)).map (List.map e)
        rw [← List.map_flatten, order_eq, ih _ ok]
        cases sphereRun key next n (order key bs.flatten) <;> simp

private def visit {i : Input} (encode : List Word → List Word) (p : FullVisit i) : FullVisit i :=
  ⟨p.cursor,p.path.map encode⟩

/-- A graph-local law for complete rank reads suffices for all seed bits,
including ties across parents and failed reads. Recode each whole step
after appending its like/unlike bit. -/
theorem wordWith_exact {i : Input} (r : Reader i) (rev : Bool) (seed : RS) (q : Arm i)
    (edges : Arm i → List (Arm i)) (rank alt : Arm i → Option Branch)
    (D : Arm i → Prop) (start : D q) (below : ∀ a, D a → ∀ b ∈ edges a, D b)
    (encode : List Word → List Word) (mono : StrictMono encode)
    (initial : encode (stepKey [] (likeAt i r rev seed q)) = stepKey [] (likeAt i r rev seed q))
    (read : ∀ c, D c →
      (alt c).map (fun k => stepKey k.deep (likeAt i r rev seed c)) =
      (rank c).map (fun k => encode (stepKey k.deep (likeAt i r rev seed c)))) :
    wordWith r rev edges alt seed q = wordWith r rev edges rank seed q := by
  let e := visit (i := i) encode
  have step (p : FullVisit i) (on : D p.cursor) :
      nextWith r rev seed edges alt (e p) = (nextWith r rev seed edges rank p).map (List.map e) := by
    unfold nextWith
    apply mapM_transport
    intro c hc
    have obs := read c (below p.cursor on c hc)
    cases h : rank c <;> cases t : alt c <;> simp [h,t] at obs ⊢
    simp [e,visit,obs]
  have closed (p : FullVisit i) (on : D p.cursor) (ys : List (FullVisit i))
      (lookup : nextWith r rev seed edges rank p = some ys) (y : FullVisit i) (hy : y ∈ ys) : D y.cursor := by
    obtain ⟨c,hc,h⟩ := RingRetainedUnitPass.forOutput lookup hy
    cases k : rank c <;> simp [k] at h
    obtain rfl := h
    exact below _ on c hc
  have order_eq (xs : List (FullVisit i)) :
      order FullVisit.path (xs.map e) = (order FullVisit.path xs).map e := by
    symm
    apply List.map_mergeSort
    intro a _ b _
    change decide (b.path ≤ a.path) = decide (b.path.map encode ≤ a.path.map encode)
    congr 1
    exact propext (RingPriorityCoordinate.map_strictMono mono).le_iff_le.symm
  let root := rootVisit i r rev seed q
  have atRoot : e root = root := by
    simp [e,visit,root,Oracle.root,initial]
  have same := sphere_transport FullVisit.path e (fun p => D p.cursor) _ _ order_eq step closed
    (i.certified.localizedRerootCursorBudget q + 1) [root] (by simpa [root,rootVisit,Oracle.root] using start)
  simp only [List.map_singleton,atRoot] at same
  unfold wordWith
  rw [show rootVisit i r rev seed q = root from rfl,same]
  cases sphereRun FullVisit.path (nextWith r rev seed edges rank) (i.certified.localizedRerootCursorBudget q + 1) [root] <;>
    simp [List.filterMap_map,Function.comp_def,e,visit]

end TetraStereo.Engine.RingOriginSeedWords
assert_kernel_only TetraStereo.Engine.RingOriginSeedWords.wordWith_exact
