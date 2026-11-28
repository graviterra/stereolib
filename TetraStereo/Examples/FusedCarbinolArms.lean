import TetraStereo.Engine.RingAtomicNeighborOrder

/-! Rooted graph rigidity for the two octahydroinden-4-yl ligands of a carbinol.
The walk counts are topological invariants used to identify atoms. CIP
priorities are computed separately from the stereochemical frames. -/
set_option autoImplicit false
namespace TetraStereo.Examples.FusedCarbinolArms
open TetraStereo.OneCenter

def molecule : RawMolecule := {
  atoms := (([.C,.O] : List Element) ++ List.replicate 18 Element.C ++ List.replicate 32 Element.H).map AtomSpec.aliphatic
  bonds := [
    ⟨1,0,.single⟩, ⟨0,2,.single⟩, ⟨2,3,.single⟩, ⟨3,4,.single⟩, ⟨4,5,.single⟩,
    ⟨5,6,.single⟩, ⟨6,7,.single⟩, ⟨7,8,.single⟩, ⟨8,9,.single⟩, ⟨9,10,.single⟩,
    ⟨2,10,.single⟩, ⟨6,10,.single⟩, ⟨0,11,.single⟩, ⟨11,12,.single⟩, ⟨12,13,.single⟩,
    ⟨13,14,.single⟩, ⟨14,15,.single⟩, ⟨15,16,.single⟩, ⟨16,17,.single⟩, ⟨17,18,.single⟩,
    ⟨18,19,.single⟩, ⟨11,19,.single⟩, ⟨15,19,.single⟩, ⟨0,20,.single⟩, ⟨1,21,.single⟩,
    ⟨2,22,.single⟩, ⟨3,23,.single⟩, ⟨3,24,.single⟩, ⟨4,25,.single⟩, ⟨4,26,.single⟩,
    ⟨5,27,.single⟩, ⟨5,28,.single⟩, ⟨6,29,.single⟩, ⟨7,30,.single⟩, ⟨7,31,.single⟩,
    ⟨8,32,.single⟩, ⟨8,33,.single⟩, ⟨9,34,.single⟩, ⟨9,35,.single⟩, ⟨10,36,.single⟩,
    ⟨11,37,.single⟩, ⟨12,38,.single⟩, ⟨12,39,.single⟩, ⟨13,40,.single⟩, ⟨13,41,.single⟩,
    ⟨14,42,.single⟩, ⟨14,43,.single⟩, ⟨15,44,.single⟩, ⟨16,45,.single⟩, ⟨16,46,.single⟩,
    ⟨17,47,.single⟩, ⟨17,48,.single⟩, ⟨18,49,.single⟩, ⟨18,50,.single⟩, ⟨19,51,.single⟩] }

abbrev Carbon := Fin 9

/-- The perimeter follows C4,C5,C6,C7,C7a,C1,C2,C3,C3a. -/
def bonded (a b : Carbon) : Bool :=
  a.val+1 == b.val || b.val+1 == a.val ||
  (a == 8 && (b == 0 || b == 4)) || (b == 8 && (a == 0 || a == 4))

/-- The same indexed graph is induced on each nine-carbon arm of the raw molecule. -/
theorem raw_bonds : ∀ (right : Bool) (a b : Carbon),
    (molecule.bondOrder ((if right then 11 else 2) + a.val) ((if right then 11 else 2) + b.val) > 0) ↔
    bonded a b = true := by decide +kernel

/-- Follow the unique carbon successor at each CH₂ until a previously visited
carbon is duplicated. Verify both hydrogen children are terminal and the
whole forward neighbor list is accounted for. Prefix runs root through focus. -/
private def chain (m : RawMolecule) (stem : List Nat) (start : Nat) :
    Option (List (List Nat) × Nat × Nat) :=
  let ns := m.writtenNeighbors
  let z := TetraStereo.Engine.RingAtomicNeighborOrder.atomicNumber m
  let rec walk : Nat → List Nat → Nat → Option (List (List Nat) × Nat × Nat)
    | 0, _, _ => none
    | fuel+1, seen, cur => do
      let parent ← seen.getLast?
      guard (cur ∈ ns parent && z cur == 6)
      if cur ∈ seen then
        guard (cur ∈ stem)
        let origin := stem.idxOf cur
        return ([[6]],origin,stem.length-1-origin)
      let forward := (ns cur).erase parent
      let [next] := forward.filter (fun x => z x == 6) | none
      let hydrogens := forward.filter fun x => z x == 1
      guard (forward.length == 3 && hydrogens.length == 2 &&
        hydrogens.all (fun h => ns h == [cur]))
      let (shells,original,active) ← walk fuel (seen ++ [cur]) next
      return ([6,1,1] :: shells,original,active)
  do
    guard (stem.Nodup && (stem.zip (stem.drop 1)).all (fun edge => edge.2 ∈ ns edge.1))
    walk 4 stem start

/-- At either far junction, the two outward arms agree in atomic-number
profile and each closes once. Distances to their respective real ancestors
are (2,1) and (1,2), in construction-root and active-focus order.
The first 6 in each three-entry row is the carbon successor (possibly a
duplicate); the terminal singleton records reaching the duplicate itself. -/
theorem junction_paths : ∀ right : Bool,
    let b := if right then 11 else 2
    let stem := [0,b,b+8,b+4]
    let profile := [[6,1,1],[6,1,1],[6,1,1],[6]]
    chain molecule stem (b+5) = some (profile,2,1) ∧
    chain molecule stem (b+3) = some (profile,1,2) := by decide +kernel

/-- Counts walks of an exact length ending at the attachment. Applicable to
any finite heavy-atom graph, including graphs with cycles and repeated walks. -/
def rootWalks {V : Type} [Fintype V] [DecidableEq V] (edge : V → V → Bool) (root : V) :
    Nat → V → Nat
  | 0, x => if x = root then 1 else 0
  | n+1, x => ∑ y : V, if edge x y then rootWalks edge root n y else 0

/-- A correspondence between two arbitrary rooted graphs preserves every
walk count, even when the two graphs use different atom types or numberings. -/
theorem walks_equiv {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) {u : V} {v : W} (roots : e u = v)
    {l : V → V → Bool} {r : W → W → Bool} (edges : ∀ x y, r (e x) (e y) = l x y)
    (n : Nat) (x : V) : rootWalks r v n (e x) = rootWalks l u n x := by
  induction n generalizing x with
  | zero =>
    have atRoot : e x = v ↔ x = u := by simpa only [roots] using (e.injective.eq_iff (a := x) (b := u))
    simp only [rootWalks,atRoot]
  | succ n ih =>
    simp only [rootWalks]
    rw [← Equiv.sum_comp e (fun y => if r (e x) y then rootWalks r v n y else 0)]
    simp only [edges,ih]

/-- If one walk length distinguishes every vertex of a rooted skeleton,
two labellings admit a root-, edge- and label-preserving correspondence
exactly when the labels coincide on each vertex. -/
theorem marked_iff_of_walks {V Label : Type} [Fintype V] [DecidableEq V]
    (edge : V → V → Bool) (root : V) (n : Nat)
    (separates : Function.Injective (rootWalks edge root n)) (l r : V → Label) :
    (∃ e : V ≃ V, e root = root ∧ (∀ x y, edge (e x) (e y) = edge x y) ∧
      ∀ x, l x = r (e x)) ↔ l = r := by
  constructor
  · rintro ⟨e,h,k,labels⟩
    funext x
    simpa only [separates (walks_equiv e h k n x)] using labels x
  · rintro rfl
    exact ⟨Equiv.refl _,rfl,fun _ _ => rfl,fun _ => rfl⟩

private def counts (k : Fin 7) (a : Carbon) : Nat :=
  let table : List (List Nat) := [
  [1,0,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0,1], [2,0,1,0,1,0,0,1,0],
  [0,3,0,2,0,1,1,0,4], [7,0,5,0,7,1,1,5,0], [0,12,0,12,1,8,6,1,19],
  [31,0,24,1,39,7,9,25,2]]
  (table.getD k.val []).getD a.val 0

private theorem base : ∀ a : Carbon, counts 0 a = if a = 0 then 1 else 0 := by decide +kernel
private theorem step : ∀ (k : Fin 6) (a : Carbon),
    counts k.succ a = ∑ b : Carbon, if bonded a b then counts k.castSucc b else 0 := by decide +kernel
private theorem unique : ∀ a b : Carbon, counts 6 a = counts 6 b → a = b := by decide +kernel

/-- Every graph isomorphism between the two arms fixing the point of attachment
must carry every carbon to the carbon at the same indexed position. -/
theorem rigid (e : Carbon ≃ Carbon) (root : e 0 = 0)
    (edges : ∀ a b, bonded (e a) (e b) = bonded a b) (a : Carbon) : e a = a := by
  have certified : ∀ (k : Fin 7) (x : Carbon), counts k x = rootWalks bonded 0 k.val x := by
    intro k
    induction k using Fin.induction with
    | zero => intro x; exact base x
    | succ k ih => intro x; simp only [step,ih,Fin.val_succ,rootWalks,Fin.val_castSucc]
  apply unique
  simpa only [certified] using walks_equiv e root edges 6 a

structure Frame where
  attachment : Bool
  farJunction : Bool
  nearJunction : Bool
  deriving DecidableEq

def mark (f : Frame) (x : Carbon) : Option Bool :=
  if x = 0 then some f.attachment else if x = 4 then some f.farJunction else
  if x = 8 then some f.nearJunction else none

/-- The three signs use corresponding bonded carriers in the same order in
both arms. At every marked carbon the fourth carrier is its sole hydrogen. -/
def Exchange (l r : Frame) : Prop := ∃ e : Carbon ≃ Carbon, e 0 = 0 ∧
  (∀ a b, bonded (e a) (e b) = bonded a b) ∧ ∀ a, mark l a = mark r (e a)

theorem exchange_iff (l r : Frame) : Exchange l r ↔ l = r := by
  constructor
  · rintro ⟨e,root,edges,h⟩
    simp only [rigid e root edges] at h
    have a := h 0
    have f := h 4
    have n := h 8
    cases l; cases r
    simp_all [mark]
  · rintro rfl
    exact ⟨Equiv.refl _,rfl,fun _ _ => rfl,fun _ => rfl⟩

/-- Parity-based arm model checked independently against the pinned evaluator
for both conventions and every assignment of the seven molecular frame signs. -/
inductive Priority where
  | ordinary (leftWins : Bool)
  | pseudo (leftWins : Bool)
  | tie
  deriving DecidableEq

def near (f : Frame) := f.attachment == f.nearJunction
def far (f : Frame) := f.attachment == f.farJunction

def priority (active : Bool) (l r : Frame) : Priority :=
  if near l != near r then .ordinary (near l)
  else if far l != far r then .ordinary (far l == active)
  else if l.attachment != r.attachment then .pseudo l.attachment
  else .tie

theorem tie_iff_exchange (active : Bool) (l r : Frame) :
    priority active l r = .tie ↔ Exchange l r := by
  rw [exchange_iff]
  cases l; cases r
  decide +revert +kernel

/-- Exactly one quarter of pairs of arm frames have equal near parity and
different far parity. For every such pair the ordinary winner reverses. -/
theorem reversal_iff (l r : Frame) :
    (∃ w, priority false l r = .ordinary w ∧ priority true l r = .ordinary (!w)) ↔
    near l = near r ∧ far l ≠ far r := by
  cases l; cases r
  decide +revert +kernel

theorem stable_iff (l r : Frame) :
    priority false l r = priority true l r ↔ near l ≠ near r ∨ far l = far r := by
  cases l; cases r
  decide +revert +kernel

end TetraStereo.Examples.FusedCarbinolArms
assert_kernel_only TetraStereo.Examples.FusedCarbinolArms.raw_bonds
assert_kernel_only TetraStereo.Examples.FusedCarbinolArms.rigid
assert_kernel_only TetraStereo.Examples.FusedCarbinolArms.exchange_iff
assert_kernel_only TetraStereo.Examples.FusedCarbinolArms.tie_iff_exchange
assert_kernel_only TetraStereo.Examples.FusedCarbinolArms.reversal_iff
assert_kernel_only TetraStereo.Examples.FusedCarbinolArms.stable_iff
assert_kernel_only TetraStereo.Examples.FusedCarbinolArms.junction_paths
assert_kernel_only TetraStereo.Examples.FusedCarbinolArms.walks_equiv
assert_kernel_only TetraStereo.Examples.FusedCarbinolArms.marked_iff_of_walks
