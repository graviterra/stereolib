import TetraStereo.Engine.RingPyramidalPairwise
import TetraStereo.Engine.RingPriorityCoordinate

/-! Complete pyramidal ballots depend on comparisons, including the ordinary
three-way tie that selects marked trials. The observation interface includes
failed reads and every marked arm; it assumes no equality of hands or labels. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginPyramidalTrials
open OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (View)
open RingPyramidalPairwise RingFrameTransport
attribute [local instance] lexOrd
open private map_origin from TetraStereo.Engine.RingMassDifference

/-- An independently computed key may change representation, provided all
strict comparisons on the actual ballot are preserved. IDs and multiplicities
remain those of the original list. -/
theorem extract_congr {α κ β : Type} [LinearOrder κ] [LinearOrder β]
    (ids : α → Nat) (key : α → κ) (other : α → β) (xs : List α)
    (same : ∀ a ∈ xs, ∀ b ∈ xs, key a < key b ↔ other a < other b) :
    extractRow ids key xs = extractRow ids other xs := by
  unfold extractRow
  congr 1
  funext a b
  exact Bool.decide_congr (same _ (List.get_mem ..) _ (List.get_mem ..))

/-- In particular, a strictly increasing recoding of the complete key does
not change a ballot. This lemma applies to ordinary and marked keys alike. -/
theorem extract_recode {α κ β : Type} [LinearOrder κ] [LinearOrder β]
    (ids : α → Nat) (key : α → κ) (xs : List α) (f : κ → β) (inc : StrictMono f) :
    extractRow ids key xs = extractRow ids (fun x => f (key x)) xs :=
  extract_congr ids key _ xs (fun _ _ _ _ => inc.lt_iff_lt.symm)

/-- Change only the duplicated constitutional coordinate, keeping all later
Rule 3/4/5 observations and the promoted mark word unchanged. -/
abbrev key := RingPriorityCoordinate.fullKey

private def first {α : Type*} (f : α → α) : List α → List α
  | [] => []
  | x :: xs => f x :: xs

private theorem first_strictMono {α : Type*} [LinearOrder α] {f : α → α}
    (h : StrictMono f) : StrictMono (first f) := by
  intro xs ys lt
  cases lt with
  | nil => exact List.Lex.nil
  | rel lt => exact List.Lex.rel (h lt)
  | cons tail => exact List.Lex.cons tail

/-- Recode the duplicate coordinate of every complete marked trial key.
The mark remains an independent final observation on each arm. -/
theorem extract_duplicate_recode {α : Type}
    (ids : α → Nat) (keys : α → RingFullPathEligibility.Key)
    (marks : α → RingRetainedChemicalTrace.Word) (xs : List α)
    (f : Nat → Nat) (inc : StrictMono f) :
    extractRow ids (fun x => RingFullPathTrialReadings.trialKey (keys x) (marks x)) xs =
      extractRow ids (fun x => RingFullPathTrialReadings.trialKey (key f (keys x)) (marks x)) xs := by
  let transform := first (RingPriorityCoordinate.second (List.map (List.map f)))
  have mono : StrictMono transform := first_strictMono
    (RingPriorityCoordinate.second_strictMono
      (RingPriorityCoordinate.map_strictMono (RingPriorityCoordinate.map_strictMono inc)))
  exact extract_recode ids (fun x => RingFullPathTrialReadings.trialKey (keys x) (marks x))
    xs transform mono

/-- The trial observation includes an unavailable row, a tied row, and a
coordinate read returning no hand as three distinct possibilities. -/
def trial (row : Option Row) (sense : List Nat → Option RS) (focus : Nat) :
    Option (Option RS) := row.map (fun r => r.read sense focus)

theorem trial_congr (row other : Option Row) (same : row = other)
    (sense : List Nat → Option RS) (focus : Nat) :
    trial row sense focus = trial other sense focus := by rw [same]

/-- The complete production trial factors through the comparison ballot,
including failed mark reads and successful ties with no hand. -/
theorem trial_native {i : Input} (r : View i) (a : i.certified.Atom) (rev : Bool)
    (xs : List (RingPyramidalPublication.Ligand i)) (mark : Option Nat) :
    RingPyramidalPublication.trial? r a rev xs mark =
      trial ((xs.mapM (rowOf i r mark)).map (extractRow Prod.fst Prod.snd))
        (senseOf (inputGeometry i.certified) rev) a.val := by
  rw [trial_input]
  unfold trialS trial
  cases rows : xs.mapM (rowOf i r mark) <;> simp [finishS_extract]

/-- A full alternative reader supplies ordinary ballots in both geometries
and each optional marked ballot. Consequently absence and repeated marks are
preserved, without assuming a successful read or three distinct atoms. -/
structure Observations (native other : Data) : Prop where
  shape : native.shape = other.shape
  ordinary : ∀ rev, native.ordinary rev = other.ordinary rev
  marked : ∀ rev mark, native.marked rev mark = other.marked rev mark

theorem hands_congr {native other : Data} (same : Observations native other)
    (sense : List Nat → Option RS) (focus : Nat) (rev : Bool) :
    native.hands sense focus rev = other.hands sense focus rev := by
  unfold Data.hands
  rw [same.ordinary rev]
  congr 1
  funext ordinary
  congr 1
  funext mark
  rw [same.marked rev mark]

theorem labels_congr {native other : Data} (same : Observations native other)
    (g : Geometry) (focus : Nat) : native.publish g focus = other.publish g focus := by
  unfold Data.publish
  rw [same.shape, hands_congr same _ _ false, hands_congr same _ _ true]

/-- Full equality with the production P/As/Sb/constrained-N publisher. The
ordinary three-ligand tie, all three selected marks, either mirrored trial,
missing reads, repeated identities and tied marked keys are included. -/
theorem pLabels_exact (i : Input) (q : Site i) (r : View i) (a : i.certified.Atom)
    (other : Data) (same : Observations (nativeData i q r) other) :
    RingPyramidalPublication.pLabels i q r a =
      other.publish (inputGeometry i.certified) a.val := by
  rw [← pLabelsG_input, pLabelsG_native, labels_congr same]

abbrev KeyReader (i : Input) := Bool → RingActivePairs.Arm i → Option RingFullPathEligibility.Key
abbrev WordReader (i : Input) := Option Nat → RingActivePairs.Arm i → Option RingRetainedChemicalTrace.Word

private def recodeLigand {i : Input} (f : Nat → Nat) (x : RingPyramidalPublication.Ligand i) :=
  {x with priority := key f x.priority}

/-- Full keys are read independently on each physical arm. -/
def ligandsWith (i : Input) (q : Site i) (keys : KeyReader i) (rev : Bool) :=
  (RingRetainedAuxiliary.frame i.certified q).mapM fun arm => do
    let atom ← arm.occurrence.val.node.current?
    let priority ← keys rev arm
    return (⟨arm,atom.val,priority⟩ : RingPyramidalPublication.Ligand i)

private def markedPairs {i : Input} (words : WordReader i) (mark : Option Nat)
    (xs : List (RingPyramidalPublication.Ligand i)) :=
  xs.mapM fun x => (words mark x.arm).map fun w => (x,w)

private def pairRow {i : Input}
    (p : RingPyramidalPublication.Ligand i × RingRetainedChemicalTrace.Word) :=
  (p.1.atom,RingFullPathTrialReadings.trialKey p.1.priority p.2)

/-- Complete alternative computation, including failed full-key/mark reads. -/
def dataWith (i : Input) (q : Site i) (keys : KeyReader i) (words : WordReader i) : Data where
  shape := decide ((RingRetainedAuxiliary.frame i.certified q).length = 3)
  ordinary rev := (ligandsWith i q keys rev).map
    (extractRow (fun x => x.atom) (fun x => RingFullPathTrialReadings.trialKey x.priority []))
  marked rev mark := do
    let xs ← ligandsWith i q keys rev
    let ps ← markedPairs words mark xs
    return extractRow (fun p => p.1.atom)
      (fun p => RingFullPathTrialReadings.trialKey p.1.priority p.2) ps

private theorem mapM_post {α β γ : Type} (f : α → Option β) (g : β → γ) (xs : List α) :
    xs.mapM (fun x => (f x).map g) = (xs.mapM f).map (List.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.mapM_cons,ih]; cases f x <;> cases xs.mapM f <;> rfl

private theorem extract_map {α β κ : Type} [LinearOrder κ]
    (ids : β → Nat) (keys : β → κ) (f : α → β) (xs : List α) :
    extractRow ids keys (xs.map f) = extractRow (fun x => ids (f x)) (fun x => keys (f x)) xs := by
  simp [extractRow,List.get_eq_getElem]
  constructor <;> congr! <;> simp

private theorem ligand_recode (i : Input) (q : Site i) (base : KeyReader i)
    (f : Nat → Nat) (rev : Bool) :
    ligandsWith i q (fun rev arm => (base rev arm).map (key f)) rev =
      (ligandsWith i q base rev).map (List.map (recodeLigand f)) := by
  unfold ligandsWith
  rw [← mapM_post]
  apply RingFrameTransport.mapM_congr_mem
  intro arm _
  cases hc : arm.occurrence.val.node.current? <;> cases hk : base rev arm <;> simp_all [recodeLigand]

private theorem marked_recode {i : Input} (words : WordReader i) (mark : Option Nat)
    (xs : List (RingPyramidalPublication.Ligand i)) (f : Nat → Nat) :
    markedPairs words mark (xs.map (recodeLigand f)) =
      (markedPairs words mark xs).map (List.map (fun p => (recodeLigand f p.1,p.2))) := by
  unfold markedPairs
  rw [List.mapM_map,← mapM_post]
  apply RingFrameTransport.mapM_congr_mem
  intro x _
  simp only [Function.comp_apply,recodeLigand]
  cases hw : words mark x.arm <;> rfl

private theorem data_ext {x y : Data} (shape : x.shape = y.shape)
    (ordinary : x.ordinary = y.ordinary) (marked : x.marked = y.marked) : x = y := by
  cases x
  cases y
  cases shape
  cases ordinary
  cases marked
  rfl

private theorem data_recode (i : Input) (q : Site i) (base : KeyReader i)
    (words : WordReader i) (f : Nat → Nat) (inc : StrictMono f) :
    dataWith i q (fun rev arm => (base rev arm).map (key f)) words = dataWith i q base words := by
  apply data_ext
  · rfl
  · funext rev
    simp only [dataWith,ligand_recode]
    cases hx : ligandsWith i q base rev with
    | none => rfl
    | some xs =>
      simp only [Option.map_some,extract_map]
      exact congrArg some (extract_duplicate_recode (fun x => x.atom) (fun x => x.priority) (fun _ => []) xs f inc).symm
  · funext rev mark
    simp only [dataWith,ligand_recode]
    cases hx : ligandsWith i q base rev with
    | none => rfl
    | some xs =>
      simp only [Option.map_some,bind,pure,Option.bind_some,marked_recode]
      cases hp : markedPairs words mark xs with
      | none => rfl
      | some ps =>
        simp only [Option.map_some,Option.bind_some,extract_map]
        exact congrArg some
          (extract_duplicate_recode (fun p => p.1.atom) (fun p => p.1.priority) (fun p => p.2) ps f inc).symm

private theorem native_data (i : Input) (q : Site i) (r : View i) :
    dataWith i q (RingFullPathEligibility.key? i r) (markWord? i r) = nativeData i q r := by
  apply data_ext
  · rfl
  · rfl
  · funext rev mark
    change (RingPyramidalPublication.ligands? i q r rev).bind _ =
      (RingPyramidalPublication.ligands? i q r rev).bind _
    apply congrArg (Option.bind (RingPyramidalPublication.ligands? i q r rev))
    funext xs
    have rows : xs.mapM (rowOf i r mark) =
        (markedPairs (markWord? i r) mark xs).map (List.map pairRow) := by
      unfold markedPairs
      rw [← mapM_post]
      apply RingFrameTransport.mapM_congr_mem
      intro x _
      cases hw : markWord? i r mark x.arm <;> simp [rowOf,hw,pairRow]
    rw [rows]
    cases hp : markedPairs (markWord? i r) mark xs with
    | none => rfl
    | some ps => simp only [Option.map_some,bind,pure,Option.bind_some,extract_map]; rfl

private theorem ligandsWith_member {i : Input} {q : Site i} {keys : KeyReader i} {rev : Bool}
    {xs : List (RingPyramidalPublication.Ligand i)}
    (got : ligandsWith i q keys rev = some xs) {x : RingPyramidalPublication.Ligand i}
    (mem : x ∈ xs) : x.arm ∈ RingRetainedAuxiliary.frame i.certified q := by
  unfold ligandsWith at got
  obtain ⟨arm,ha,read⟩ := map_origin got mem
  cases hc : arm.occurrence.val.node.current? with
  | none => simp [hc] at read
  | some atom =>
    cases hk : keys rev arm with
    | none => simp [hc,hk] at read
    | some k =>
      have eqn : (⟨arm,atom.val,k⟩ : RingPyramidalPublication.Ligand i) = x := by
        simpa [hc,hk] using read
      rw [← eqn]
      exact ha

/-- Only actual frame arms are observed by the complete computation. -/
theorem dataWith_congr (i : Input) (q : Site i) (keys other : KeyReader i)
    (words words' : WordReader i)
    (hk : ∀ rev arm, arm ∈ RingRetainedAuxiliary.frame i.certified q → keys rev arm = other rev arm)
    (hw : ∀ mark arm, arm ∈ RingRetainedAuxiliary.frame i.certified q → words mark arm = words' mark arm) :
    dataWith i q keys words = dataWith i q other words' := by
  have ligands (rev : Bool) : ligandsWith i q keys rev = ligandsWith i q other rev := by
    unfold ligandsWith
    apply RingFrameTransport.mapM_congr_mem
    intro arm mem
    rw [hk rev arm mem]
  apply data_ext
  · rfl
  · funext rev
    change (ligandsWith i q keys rev).map _ = (ligandsWith i q other rev).map _
    rw [ligands]
  · funext rev mark
    change (ligandsWith i q keys rev).bind _ = (ligandsWith i q other rev).bind _
    rw [ligands]
    cases got : ligandsWith i q other rev with
    | none => rfl
    | some xs =>
      have pairs : markedPairs words mark xs = markedPairs words' mark xs := by
        apply RingFrameTransport.mapM_congr_mem
        intro x mem
        rw [hw mark x.arm (ligandsWith_member got mem)]
      simp only [Option.bind_some,pairs]

/-- Raw-reader substitution: complete keys on every physical arm are two
increasing duplicate-coordinate recodings of one base read, and mark words
agree before ranking. No hand, ballot or descriptor agreement is assumed. -/
theorem pLabels_raw (i : Input) (q : Site i) (r : View i) (a : i.certified.Atom)
    (base alternative : KeyReader i) (words : WordReader i)
    (f g : Nat → Nat) (hf : StrictMono f) (hg : StrictMono g)
    (native : ∀ rev arm, arm ∈ RingRetainedAuxiliary.frame i.certified q →
      RingFullPathEligibility.key? i r rev arm = (base rev arm).map (key f))
    (other : ∀ rev arm, arm ∈ RingRetainedAuxiliary.frame i.certified q →
      alternative rev arm = (base rev arm).map (key g))
    (marks : ∀ mark arm, arm ∈ RingRetainedAuxiliary.frame i.certified q →
      words mark arm = markWord? i r mark arm) :
    RingPyramidalPublication.pLabels i q r a =
      (dataWith i q alternative words).publish (inputGeometry i.certified) a.val := by
  have hn := dataWith_congr i q (RingFullPathEligibility.key? i r)
    (fun rev arm => (base rev arm).map (key f)) (markWord? i r) (markWord? i r)
    native (fun _ _ _ => rfl)
  have ho := dataWith_congr i q alternative
    (fun rev arm => (base rev arm).map (key g)) words (markWord? i r) other marks
  rw [← pLabelsG_input,pLabelsG_native,← native_data,hn,ho,
    data_recode i q base (markWord? i r) f hf,data_recode i q base (markWord? i r) g hg]

end TetraStereo.Engine.RingOriginPyramidalTrials
assert_kernel_only TetraStereo.Engine.RingOriginPyramidalTrials.extract_congr
assert_kernel_only TetraStereo.Engine.RingOriginPyramidalTrials.extract_recode
assert_kernel_only TetraStereo.Engine.RingOriginPyramidalTrials.hands_congr
assert_kernel_only TetraStereo.Engine.RingOriginPyramidalTrials.pLabels_exact

assert_kernel_only TetraStereo.Engine.RingOriginPyramidalTrials.trial_native

assert_kernel_only TetraStereo.Engine.RingOriginPyramidalTrials.extract_duplicate_recode

assert_kernel_only TetraStereo.Engine.RingOriginPyramidalTrials.pLabels_raw
