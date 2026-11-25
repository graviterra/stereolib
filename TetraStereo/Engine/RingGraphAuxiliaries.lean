import TetraStereo.Engine.RingGraphPaths
import TetraStereo.Engine.RingRebuiltStereo

/-! Derive auxiliary publications by recursion on simple molecular paths. A recursive call
carries the original root, the full sequence of atom identifiers and its bonded path proof.
The depth bound comes from the atom count. -/

set_option autoImplicit false

namespace TetraStereo.Engine.RingGraphAuxiliaries
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Cell View Rule distance frozen)
open RingGraphPaths (Path Represents site represents_site)

private theorem path_of_read {i : Input} {r a} (q : Site i) (on : q.val.root = r)
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a) :
    Path i r q.val.node.history a := by
  obtain ⟨b,found,path⟩ := RingGraphPaths.site_path q real
  obtain rfl := Option.some.inj (found.symm.trans current)
  exact on ▸ path

abbrev Continuation (i : Input) (r : i.certified.Atom) :=
  ∀ {h a}, Path i r h a → Cell

/-- Only a deeper simple path ending at a different four-neighbour atom can make a
recursive demand. Atoms in other digraphs are inaccessible. -/
def reader {i : Input} (r : i.certified.Atom) (length : Nat) (next : Continuation i r) : View i :=
  fun q =>
    if on : q.val.root = r then
      match current : q.val.node.current? with
      | none => some none
      | some a =>
        if ok : q.val.node.provenance = .realAtom ∧ length < q.val.node.history.length ∧
            a ≠ r ∧ Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 then
          next (path_of_read q on ok.1 current)
        else some none
    else none

/-- There is no publication table argument. On each recursive call the continuation
receives a strictly longer path in the same original graph. -/
def fold {i : Input} (localRule : Rule i) (r : i.certified.Atom) :
    Nat → Continuation i r
  | 0 => fun _ => none
  | fuel+1 => fun p => localRule (site p) (reader r (site p).val.node.history.length (fold localRule r fuel))

private theorem absent {i : Input} (q : Site i)
    (no : i.certified.localizedOccurrenceDescriptorCenter? q = none) :
    RingGroupedPublication.state i q = some none :=
  (RingGroupedPublication.state_eq i q).trans (RingSphereQueue.grouped_skips i q _ no)

private theorem recognized {i : Input} (q : Site i) :
    (i.certified.localizedOccurrenceDescriptorCenter? q).isSome = true ↔
      q.val.node.provenance = .realAtom ∧ ∃ a, q.val.node.current? = some a ∧
        Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨c,h⟩
    obtain ⟨real,atom⟩ := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mp h
    exact ⟨real,c.val,atom,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp c.property⟩
  · rintro ⟨real,a,atom,four⟩
    let c : i.certified.TetrahedralCenter := ⟨a,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr four⟩
    exact ⟨c,(i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mpr ⟨real,atom⟩⟩

/-- An inductively justified hand or absence at each required child supplies a
complete reader for the next local chemical calculation. -/
theorem reader_ready {i r h a} (p : Path i r h a)
    (next : ∀ {k b}, Path i r k b → Option RingNestedActivePair.Labels)
    (ok : ∀ {k b} (c : Path i r k b), h.length < k.length → b ≠ r →
      Fintype.card (i.certified.moleculeGraph.Neighbor b) = 4 →
      (next c).all RingNestedActivePair.consistent = true) :
    RingGroupedStereo.Ready (site p) (reader r h.length (fun c => some (next c))) := by
  intro q root
  have on := root.trans (represents_site p).1
  simp only [reader,dif_pos on]
  split
  · exact ⟨none,rfl,rfl,fun _ => rfl⟩
  · rename_i b current
    split
    · rename_i active
      refine ⟨_,rfl,ok _ active.2.1 active.2.2.1 active.2.2.2,?_⟩
      intro empty
      obtain ⟨c,known⟩ := Option.isSome_iff_exists.mp ((recognized q.occurrence).mpr
        ⟨active.1,b,current,active.2.2.2⟩)
      obtain ⟨fr,_⟩ := RingGroupedGeometry.frame_exists known
      have shape := RingFrontierProfileShape.cut_frame q
      change i.certified.executableLocalizedRerootChildren q = [] at empty
      rw [fr.four,empty] at shape
      contradiction
    · exact ⟨none,rfl,rfl,fun _ => rfl⟩

/-- Bonded-path lookup agrees with a frozen store whenever it supplies
every deeper tetrahedral site and the store gives absence at noncentres. -/
theorem reader_eq_frozen {i r h a} (store : View i)
    (empty : ∀ q, i.certified.localizedOccurrenceDescriptorCenter? q = none → store q = some none)
    (p : Path i r h a) (next : Continuation i r)
    (deeper : ∀ {k b} (child : Path i r k b), h.length < k.length → b ≠ r →
      Fintype.card (i.certified.moleculeGraph.Neighbor b) = 4 →
      next child = store (site child)) :
    reader r h.length next = frozen (store) (site p) := by
  funext q
  have rep := represents_site p
  have size := RingGraphPaths.path_length rep
  have len := i.certified.carrierOccurrence_history_length_eq_address_succ q
  change q.val.node.history.length = distance q + 1 at len
  have farther : (distance (site p) < distance q) ↔ h.length < q.val.node.history.length := by omega
  unfold reader frozen
  simp only [rep.1,farther]
  by_cases on : q.val.root = r
  · simp only [dif_pos on,if_neg (not_not_intro on)]
    split
    · rename_i current
      simp only [current,ne_eq,reduceCtorEq,not_false_eq_true,and_true]
      split
      · symm
        apply empty
        cases hc : i.certified.localizedOccurrenceDescriptorCenter? q with
        | none => rfl
        | some c =>
          have found := ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mp hc).2
          simp [current] at found
      · rfl
    · rename_i b current
      simp only [current,ne_eq,Option.some.injEq]
      by_cases ok : q.val.node.provenance = .realAtom ∧ h.length < q.val.node.history.length ∧
          b ≠ r ∧ Fintype.card (i.certified.moleculeGraph.Neighbor b) = 4
      · simp only [dif_pos ok,if_pos (And.intro ok.2.1 ok.2.2.1)]
        let child := path_of_read q on ok.1 current
        have same : site child = q := RingGraphPaths.unique_site (represents_site child) ⟨on,rfl,ok.1,current⟩
        exact (deeper child ok.2.1 ok.2.2.1 ok.2.2.2).trans (congrArg _ same)
      · simp only [dif_neg ok]
        split
        · rename_i visible
          symm
          apply empty
          cases hc : i.certified.localizedOccurrenceDescriptorCenter? q with
          | none => rfl
          | some c =>
            obtain ⟨real,b',found,four⟩ := (recognized q).mp (by simp [hc])
            obtain rfl := Option.some.inj (found.symm.trans current)
            exact (ok ⟨real,visible.1,visible.2,four⟩).elim
        · rfl
  · simp only [dif_neg on,if_pos on]

private theorem reader_exact {i r h a} (p : Path i r h a) (next : Continuation i r)
    (deeper : ∀ {k b} (child : Path i r k b), h.length < k.length → b ≠ r →
      Fintype.card (i.certified.moleculeGraph.Neighbor b) = 4 →
      next child = RingGroupedPublication.state i (site child)) :
    reader r h.length next = frozen (RingGroupedPublication.state i) (site p) :=
  reader_eq_frozen _ absent p next deeper

theorem length_bound {i r h a} (p : Path i r h a) :
    h.length ≤ i.certified.certified.input.molecule.atomCount := by
  have distinct : h.Nodup := by
    induction p with
    | origin => simp
    | step _ _ fresh ih => exact List.nodup_cons.mpr ⟨fresh,ih⟩
  simpa only [List.toFinset_card_of_nodup distinct,Fintype.card_fin] using Finset.card_le_univ h.toFinset

/-- A local rule need only agree on the complete molecular reading at one occurrence.
The recursive graph calculation supplies every required deeper value itself. -/
theorem fold_exact {i : Input} (rule : Rule i)
    (one : ∀ q, rule q (frozen (RingGroupedPublication.state i) q) = RingGroupedPublication.state i q)
    {r h a} (p : Path i r h a) (fuel : Nat)
    (enough : i.certified.certified.input.molecule.atomCount < h.length + fuel) :
    fold rule r fuel p = RingGroupedPublication.state i (site p) := by
  induction fuel generalizing h a with
  | zero =>
    have upper := length_bound p
    omega
  | succ n ih =>
    simp only [fold,(represents_site p).2.1]
    rw [reader_exact p _ (fun c longer _ _ => ih c (by omega))]
    exact one _

def value {i : Input} (rule : Rule i) {r h a} (p : Path i r h a) : Cell :=
  fold rule r (i.certified.certified.input.molecule.atomCount + 1 - h.length) p

theorem value_exact {i : Input} (rule : Rule i)
    (one : ∀ q, rule q (frozen (RingGroupedPublication.state i) q) = RingGroupedPublication.state i q)
    {r h a} (p : Path i r h a) : value rule p = RingGroupedPublication.state i (site p) := by
  apply fold_exact rule one
  omega

open RingNestedActivePair (Labels)
abbrev LocalLaw (i : Input) := Site i → View i → Option Labels → Prop

/-- A tree of molecular decisions. Every child value used by the local derivation must
itself have a derivation at its full atom path. A completed refusal is a possible value.
A missing reading cannot witness coverage of a required child. -/
inductive Derives {i : Input} (law : LocalLaw i) (r : i.certified.Atom) :
    {h : List i.certified.Atom} → {a : i.certified.Atom} → Path i r h a → Option Labels → Prop where
  | step {h a v} (p : Path i r h a)
      (next : ∀ {k b}, Path i r k b → Option Labels)
      (observed : law (site p) (reader r h.length (fun c => some (next c))) v)
      (children : ∀ {k b} (c : Path i r k b), h.length < k.length → b ≠ r →
        Fintype.card (i.certified.moleculeGraph.Neighbor b) = 4 →
        Derives law r c (next c)) : Derives law r p v

/-- Agreement on deeper four-neighbour paths suffices for the whole local reader,
including the inward direction when a retained site is rerooted. -/
theorem reader_congr {i r} (len : Nat) (l m : Continuation i r)
    (same : ∀ {k b} (c : Path i r k b), len < k.length → b ≠ r →
      Fintype.card (i.certified.moleculeGraph.Neighbor b) = 4 → l c = m c) :
    reader r len l = reader r len m := by
  funext q
  unfold reader
  split
  · split
    · rfl
    · split
      · rename_i ok
        exact same _ ok.2.1 ok.2.2.1 ok.2.2.2
      · rfl
  · rfl

theorem Derives.unique {i r h a law} {p : Path i r h a} {v w}
    (one : ∀ f read x y, law f read x → law f read y → x = y)
    (x : Derives law r p v) (y : Derives law r p w) : v = w := by
  induction x generalizing w with
  | step p next observed _ ih =>
    cases y with
    | step _ next' observed' children' =>
      have eqn := reader_congr _ (fun c => some (next c)) (fun c => some (next' c)) (by
        intro k b child longer other four
        exact congrArg some (ih child longer other four (children' child longer other four)))
      rw [← eqn] at observed'
      exact one _ _ _ _ observed observed'

/-- It suffices to identify the local chemical judgement on the admitted reading. No
agreement on arbitrary, contradictory input labels is needed. -/
def Agrees {i : Input} (law : LocalLaw i) : Prop :=
  ∀ q v, law q (frozen (RingGroupedPublication.state i) q) v ↔
    RingGroupedPublication.state i q = some v

/-- A molecular derivation recurses on bonded paths. Its only store
requirements are coverage, absence at noncentres and local agreement. -/
theorem derives_iff_store {i : Input} (store : View i)
    (empty : ∀ q, i.certified.localizedOccurrenceDescriptorCenter? q = none → store q = some none)
    (coveredAt : ∀ q, (store q).isSome = true)
    {law : LocalLaw i} (localLaw : ∀ q v, law q (frozen store q) v ↔ store q = some v)
    {r h a} (p : Path i r h a) (v : Option Labels) :
    Derives law r p v ↔ store (site p) = some v := by
  constructor
  · intro tree
    induction tree with
    | step p next observed children ih =>
      have same := reader_eq_frozen store empty p (fun c => some (next c)) (by
        intro k b c deeper other four
        exact (ih c deeper other four).symm)
      rw [same] at observed
      exact (localLaw _ _).mp observed
  · suffices ∀ n {k b} (c : Path i r k b), i.certified.certified.input.molecule.atomCount < k.length + n →
        ∀ w, store (site c) = some w → Derives law r c w from
      this (i.certified.certified.input.molecule.atomCount + 1) p (by omega) v
    intro n
    induction n with
    | zero =>
      intro k b c enough
      have upper := length_bound c
      omega
    | succ n ih =>
      intro k b c enough w issued
      let next {l d} (child : Path i r l d) := (store (site child)).getD none
      have covered {l d} (child : Path i r l d) : store (site child) = some (next child) := by
        obtain ⟨z,hz⟩ := Option.isSome_iff_exists.mp
          (coveredAt (site child))
        simp [next,hz]
      apply Derives.step c next
      · rw [reader_eq_frozen store empty c (fun child => some (next child)) (fun child _ _ _ => (covered child).symm)]
        exact (localLaw _ _).mpr issued
      · intro l d child longer _ _
        exact ih child (by omega) _ (covered child)

theorem derives_iff {i : Input} (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {law : LocalLaw i} (localLaw : Agrees law) {r h a} (p : Path i r h a) (v : Option Labels) :
    Derives law r p v ↔ RingGroupedPublication.state i (site p) = some v :=
  derives_iff_store _ absent (RingGroupedPublication.complete (RingGroupedGeometry.physical coords)) localLaw p v

def Report {i : Input} (law : LocalLaw i) (atoms : List i.certified.Atom)
    (rows : RingGroupedReport.Report) : Prop :=
  List.Forall₂ (fun atom row => row.1 = atom.val ∧ Derives law atom .origin row.2) atoms rows

private theorem root_site (i : Input) (a : i.certified.Atom) :
    site (Path.origin (i := i) (root := a)) = RingGroupedReport.origin i a :=
  RingGroupedReport.origin_unique _ rfl

theorem report_iff {i : Input} (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {law : LocalLaw i} (localLaw : Agrees law) (atoms : List i.certified.Atom) (rows : RingGroupedReport.Report) :
    Report law atoms rows ↔ RingGroupedReport.forAtoms? i atoms = some rows := by
  rw [RingGroupedReport.correct_iff i coords]
  have perAtom (a : i.certified.Atom) (v : Option Labels) :
      Derives law a .origin v ↔ RingGroupedPublication.Molecular i (RingGroupedReport.origin i a) v := by
    rw [derives_iff coords localLaw (.origin : Path i a [a] a),root_site,RingGroupedPublication.molecular_iff (RingGroupedGeometry.physical coords)]
  exact ⟨fun hs => hs.imp (fun a row v => ⟨v.1,(perAtom a row.2).mp v.2⟩),
    fun hs => hs.imp (fun a row v => ⟨v.1,(perAtom a row.2).mpr v.2⟩)⟩

end TetraStereo.Engine.RingGraphAuxiliaries

assert_kernel_only TetraStereo.Engine.RingGraphAuxiliaries.fold_exact
assert_kernel_only TetraStereo.Engine.RingGraphAuxiliaries.value_exact
assert_kernel_only TetraStereo.Engine.RingGraphAuxiliaries.derives_iff
assert_kernel_only TetraStereo.Engine.RingGraphAuxiliaries.report_iff
