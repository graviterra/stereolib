import TetraStereo.OneCenter.RS
import Mathlib.Algebra.Group.Action.Defs
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000










































namespace TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus

/-! ## Flipping an `R`/`S` reading by the local sign -/

/-- Apply the `R ↔ S` swap exactly when the local sign is odd.

`false` represents local sign `+1` and `true` represents local sign `-1`.  This is the
`Option RS` form of the actual `flipBy` used by generated-reading transport. -/
def flipReading (odd : Bool) : Option RS → Option RS
  | none => none
  | some value => some (if odd then RS.swap value else value)

@[simp] theorem flipReading_none (odd : Bool) : flipReading odd none = none := rfl

@[simp] theorem flipReading_some (odd : Bool) (value : RS) :
    flipReading odd (some value) = some (if odd then RS.swap value else value) := rfl

@[simp] theorem flipReading_false (reading : Option RS) :
    flipReading false reading = reading := by
  cases reading with
  | none => rfl
  | some value => rfl

@[simp] theorem flipReading_true_some (value : RS) :
    flipReading true (some value) = some (RS.swap value) := rfl

theorem rs_swap_swap (value : RS) : RS.swap (RS.swap value) = value := by
  cases value <;> rfl

theorem rs_swap_ne (value : RS) : RS.swap value ≠ value := by
  cases value <;> simp [RS.swap]

theorem flipReading_true_ne_some (value : RS) :
    flipReading true (some value) ≠ some value := by
  rw [flipReading_true_some]
  intro same
  exact rs_swap_ne value (Option.some.inj same)

theorem flipReading_true_involutive (reading : Option RS) :
    flipReading true (flipReading true reading) = reading := by
  cases reading with
  | none => rfl
  | some value =>
      rw [flipReading_true_some, flipReading_true_some, rs_swap_swap]

/-! ## Action-level hypotheses -/

/-- Every element of the acting group has even local sign. -/
abbrev AllEven {G : Type*} (sign : G → Bool) : Prop := ∀ g : G, sign g = false

/-- Some element of the acting group has odd local sign. -/
abbrev HasOdd {G : Type*} (sign : G → Bool) : Prop := ∃ g : G, sign g = true

/-- One common successful `R`/`S` value for every eligible reference. -/
abbrev CommonValue {E : Type*} (reading : E → Option RS) (value : RS) : Prop :=
  ∀ e : E, reading e = some value

/-- Consensus succeeds when all readings share one successful value. -/
abbrev ConsensusSuccess {E : Type*} (reading : E → Option RS) : Prop :=
  ∃ value : RS, CommonValue reading value

/-- `g` is an odd element of the stabilizer of the reference `e`. -/
abbrev OddStabilizer {G E : Type*} (act : G → E → E) (sign : G → Bool) (e : E) : Prop :=
  ∃ g : G, sign g = true ∧ act g e = e

theorem allEven_iff_not_hasOdd {G : Type*} (sign : G → Bool) :
    AllEven sign ↔ ¬ HasOdd sign := by
  constructor
  · intro hall hodd
    obtain ⟨g, hg⟩ := hodd
    rw [hall g] at hg
    cases hg
  · intro hno g
    cases hg : sign g with
    | false => rfl
    | true => exact absurd ⟨g, hg⟩ hno

/-- Every even group element leaves the optional reading of `e` unchanged. -/
theorem reading_invariant_of_allEven {G E : Type*} (act : G → E → E)
    (sign : G → Bool) (reading : E → Option RS) (hall : AllEven sign)
    (transport : ∀ (g : G) (e : E), reading (act g e) = flipReading (sign g) (reading e))
    (g : G) (e : E) : reading (act g e) = reading e := by
  rw [transport g e, hall g]
  exact flipReading_false (reading e)

/-- Under even signs, a failed reading would give an odd stabilizer element. -/
theorem reading_some_of_allEven {G E : Type*} (act : G → E → E)
    (sign : G → Bool) (reading : E → Option RS)
    (failure : ∀ e : E, reading e = none → OddStabilizer act sign e)
    (hall : AllEven sign) (e : E) : ∃ value : RS, reading e = some value := by
  cases h : reading e with
  | none =>
      obtain ⟨g, hodd, _⟩ := failure e h
      rw [hall g] at hodd
      cases hodd
  | some value => exact ⟨value, rfl⟩

/-- Under even signs, one successful reading propagates to every reference in its orbit.

This is the only place where transitivity of the action is used positively: it turns
orbit-wise invariance into a single common value on all of `E`. -/
theorem reading_eq_of_allEven {G E : Type*} (act : G → E → E)
    (sign : G → Bool) (reading : E → Option RS) (hall : AllEven sign)
    (transitive : ∀ e₁ e₂ : E, ∃ g : G, act g e₁ = e₂)
    (transport : ∀ (g : G) (e : E), reading (act g e) = flipReading (sign g) (reading e))
    {e₀ e : E} {value : RS} (hvalue₀ : reading e₀ = some value) :
    reading e = some value := by
  obtain ⟨g, hg⟩ := transitive e₀ e
  calc
    reading e = reading (act g e₀) := by rw [hg]
    _ = flipReading (sign g) (reading e₀) := transport g e₀
    _ = some value := by simp [hall g, hvalue₀]

/-! ## The abstract success/refusal dichotomy -/

/-- The general consensus lemma.

The `failure` hypothesis is the forward direction of the intended actual-domain contract
"reading `e` is missing iff some odd stabilizer element fixes `e`".  The converse is not used,
so the lemma is stated with the weaker soundness direction. -/
theorem consensusSuccess_iff_allEven_core {G E : Type*} (act : G → E → E)
    (sign : G → Bool) (reading : E → Option RS)
    (nonempty : Nonempty E)
    (transitive : ∀ e₁ e₂ : E, ∃ g : G, act g e₁ = e₂)
    (transport : ∀ (g : G) (e : E), reading (act g e) = flipReading (sign g) (reading e))
    (failure : ∀ e : E, reading e = none → OddStabilizer act sign e) :
    ConsensusSuccess reading ↔ AllEven sign := by
  constructor
  · rintro ⟨value, hvalue⟩ g
    cases hg : sign g with
    | false => rfl
    | true =>
        obtain ⟨e⟩ := nonempty
        have moved : reading (act g e) = some (RS.swap value) := by
          calc
            reading (act g e) = flipReading (sign g) (reading e) := transport g e
            _ = flipReading true (some value) := by rw [hg, hvalue e]
            _ = some (RS.swap value) := flipReading_true_some value
        have also : reading (act g e) = some value := hvalue (act g e)
        rw [moved] at also
        exact False.elim (rs_swap_ne value (Option.some.inj also))
  · intro hall
    obtain ⟨e₀⟩ := nonempty
    obtain ⟨value₀, hvalue₀⟩ := reading_some_of_allEven act sign reading failure hall e₀
    refine ⟨value₀, ?_⟩
    intro e
    exact reading_eq_of_allEven act sign reading hall transitive transport hvalue₀

/-- An odd acting element rules out a common successful value.

This direction needs no failed-reading hypothesis and no transitivity: it only uses
nonemptiness of `E` and transport for that one odd element. -/
theorem not_consensusSuccess_of_odd_core {G E : Type*} (act : G → E → E)
    (sign : G → Bool) (reading : E → Option RS) (nonempty : Nonempty E)
    (transport : ∀ (g : G) (e : E), reading (act g e) = flipReading (sign g) (reading e))
    (g : G) (hodd : sign g = true) :
    ¬ ConsensusSuccess reading := by
  rintro ⟨value, hvalue⟩
  obtain ⟨e⟩ := nonempty
  have moved : reading (act g e) = some (RS.swap value) := by
    calc
      reading (act g e) = flipReading (sign g) (reading e) := transport g e
      _ = flipReading true (some value) := by rw [hodd, hvalue e]
      _ = some (RS.swap value) := flipReading_true_some value
  have also : reading (act g e) = some value := hvalue (act g e)
  rw [moved] at also
  exact False.elim (rs_swap_ne value (Option.some.inj also))

theorem not_consensusSuccess_of_hasOdd_core {G E : Type*} (act : G → E → E)
    (sign : G → Bool) (reading : E → Option RS) (nonempty : Nonempty E)
    (transport : ∀ (g : G) (e : E), reading (act g e) = flipReading (sign g) (reading e))
    (odd : HasOdd sign) : ¬ ConsensusSuccess reading := by
  obtain ⟨g, hg⟩ := odd
  exact not_consensusSuccess_of_odd_core act sign reading nonempty transport g hg

/-- The success criterion expressed as absence of an odd acting element. -/
theorem consensusSuccess_iff_no_odd_core {G E : Type*} (act : G → E → E)
    (sign : G → Bool) (reading : E → Option RS) (nonempty : Nonempty E)
    (transitive : ∀ e₁ e₂ : E, ∃ g : G, act g e₁ = e₂)
    (transport : ∀ (g : G) (e : E), reading (act g e) = flipReading (sign g) (reading e))
    (failure : ∀ e : E, reading e = none → OddStabilizer act sign e) :
    ConsensusSuccess reading ↔ ¬ HasOdd sign :=
  (consensusSuccess_iff_allEven_core act sign reading nonempty transitive transport failure).trans
    (allEven_iff_not_hasOdd sign)

/-! ## `MulAction` formulation -/

section MulActionSemantics

variable {G E : Type*} [Group G] [MulAction G E]

/-- Consensus success under a `MulAction`, with the full failed-reading/stabilizer contract.

Only the forward direction of `failure` is used; the backward direction is included because it
is the shape of the intended actual-domain contract. -/
theorem consensusSuccess_iff_allEven (sign : G → Bool) (reading : E → Option RS)
    (nonempty : Nonempty E)
    (transitive : ∀ e₁ e₂ : E, ∃ g : G, g • e₁ = e₂)
    (transport : ∀ (g : G) (e : E), reading (g • e) = flipReading (sign g) (reading e))
    (failure : ∀ e : E, reading e = none ↔ ∃ g : G, sign g = true ∧ g • e = e) :
    ConsensusSuccess reading ↔ AllEven sign := by
  refine consensusSuccess_iff_allEven_core (fun g e => g • e) sign reading nonempty
    (fun e₁ e₂ => transitive e₁ e₂) (fun g e => transport g e) ?_
  intro e h
  obtain ⟨g, hg, hfix⟩ := (failure e).mp h
  exact ⟨g, hg, hfix⟩

/-- An odd acting element rules out a common successful value. -/
theorem not_consensusSuccess_of_odd (sign : G → Bool) (reading : E → Option RS)
    (nonempty : Nonempty E)
    (transport : ∀ (g : G) (e : E), reading (g • e) = flipReading (sign g) (reading e))
    (g : G) (hodd : sign g = true) : ¬ ConsensusSuccess reading :=
  not_consensusSuccess_of_odd_core (fun g e => g • e) sign reading nonempty transport g hodd

theorem not_consensusSuccess_of_hasOdd (sign : G → Bool) (reading : E → Option RS)
    (nonempty : Nonempty E)
    (transport : ∀ (g : G) (e : E), reading (g • e) = flipReading (sign g) (reading e))
    (odd : HasOdd sign) : ¬ ConsensusSuccess reading := by
  obtain ⟨g, hg⟩ := odd
  exact not_consensusSuccess_of_odd sign reading nonempty transport g hg

/-- Consensus success is equivalent to absence of an odd acting element. -/
theorem consensusSuccess_iff_no_odd (sign : G → Bool) (reading : E → Option RS)
    (nonempty : Nonempty E)
    (transitive : ∀ e₁ e₂ : E, ∃ g : G, g • e₁ = e₂)
    (transport : ∀ (g : G) (e : E), reading (g • e) = flipReading (sign g) (reading e))
    (failure : ∀ e : E, reading e = none ↔ ∃ g : G, sign g = true ∧ g • e = e) :
    ConsensusSuccess reading ↔ ¬ HasOdd sign :=
  (consensusSuccess_iff_allEven sign reading nonempty transitive transport failure).trans
    (allEven_iff_not_hasOdd sign)

end MulActionSemantics

/-! ## The runtime list consensus -/

/-- The exact list consensus used by the generated-reading evaluator: a common successful
value, refused on an empty list, a missing reading, or two different successful readings. -/
def consensus : List (Option RS) → Option RS
  | [] => none
  | [result] => result
  | result :: rest =>
      match result, consensus rest with
      | some a, some b => if a = b then some a else none
      | _, _ => none

theorem consensus_cons_cons (x y : Option RS) (rest : List (Option RS)) :
    consensus (x :: y :: rest) =
      match x, consensus (y :: rest) with
      | some a, some b => if a = b then some a else none
      | _, _ => none := rfl

/-- Characterization of the runtime consensus: it returns `some value` exactly when the list
is nonempty and every entry is that same successful value. -/
theorem consensus_eq_some_iff : ∀ (l : List (Option RS)) (value : RS),
    consensus l = some value ↔ l ≠ [] ∧ ∀ entry ∈ l, entry = some value
  | [], value => by simp [consensus]
  | [x], value => by simp [consensus]
  | x :: y :: rest, value => by
      rw [consensus_cons_cons]
      constructor
      · intro h
        rcases x with _ | a
        · simp at h
        · cases hc : consensus (y :: rest) with
          | none =>
              rw [hc] at h
              simp at h
          | some b =>
              rw [hc] at h
              simp only at h
              split_ifs at h with hab
              have hav : a = value := Option.some.inj h
              have tail := (consensus_eq_some_iff (y :: rest) value).mp (by rw [hc, ← hab, hav])
              refine ⟨by simp, ?_⟩
              intro entry member
              rcases List.mem_cons.mp member with rfl | later
              · rw [hav]
              · exact tail.2 entry later
      · rintro ⟨_, all⟩
        have head := all x List.mem_cons_self
        have tail : consensus (y :: rest) = some value :=
          (consensus_eq_some_iff (y :: rest) value).mpr
            ⟨by simp, fun entry member => all entry (List.mem_cons_of_mem x member)⟩
        rw [head, tail]
        simp

/-- A sufficient interface for transferring list-consensus results to a definitionally equal
aggregator without importing its (possibly heavy) module. -/
structure ConsensusLaw (C : List (Option RS) → Option RS) : Prop where
  eq_some_iff : ∀ (l : List (Option RS)) (value : RS),
    C l = some value ↔ l ≠ [] ∧ ∀ entry ∈ l, entry = some value

theorem consensusLaw_consensus : ConsensusLaw consensus :=
  ⟨consensus_eq_some_iff⟩

/-! ## List-level consensus results -/

/-- Under all-even signs, one successful reading fixes the value returned by consensus.

This positive result does not use the failed-reading/stabilizer hypothesis. -/
theorem consensus_map_eq_some_of_allEven_core {G E : Type*} (act : G → E → E)
    (sign : G → Bool) (reading : E → Option RS) (nonempty : Nonempty E)
    (transitive : ∀ e₁ e₂ : E, ∃ g : G, act g e₁ = e₂)
    (transport : ∀ (g : G) (e : E), reading (act g e) = flipReading (sign g) (reading e))
    (L : List E) (complete : ∀ e : E, e ∈ L)
    (hall : AllEven sign) (e : E) (value : RS) (hvalue : reading e = some value) :
    consensus (L.map reading) = some value := by
  apply (consensus_eq_some_iff (L.map reading) value).mpr
  constructor
  · obtain ⟨e₀⟩ := nonempty
    intro nil
    have member : reading e₀ ∈ L.map reading := List.mem_map.mpr ⟨e₀, complete e₀, rfl⟩
    rw [nil] at member
    simp at member
  · intro entry member
    obtain ⟨e', _, rfl⟩ := List.mem_map.mp member
    exact reading_eq_of_allEven act sign reading hall transitive transport hvalue

/-- If some odd acting element exists, the runtime consensus refuses on every complete list of
eligible references.  This needs only transport for that odd element and nonemptiness. -/
theorem consensusLaw_map_eq_none_of_odd {G E : Type*}
    (C : List (Option RS) → Option RS) (law : ConsensusLaw C)
    (act : G → E → E) (sign : G → Bool) (reading : E → Option RS)
    (nonempty : Nonempty E)
    (transport : ∀ (g : G) (e : E), reading (act g e) = flipReading (sign g) (reading e))
    (L : List E) (complete : ∀ e : E, e ∈ L)
    (g : G) (hodd : sign g = true) :
    C (L.map reading) = none := by
  have noValue := not_consensusSuccess_of_odd_core act sign reading nonempty transport g hodd
  cases h : C (L.map reading) with
  | none => rfl
  | some value =>
      exfalso
      apply noValue
      refine ⟨value, fun e => ?_⟩
      have entries := (law.eq_some_iff (L.map reading) value).mp h
      exact entries.2 (reading e) (List.mem_map.mpr ⟨e, complete e, rfl⟩)

/-- A list consensus returns `some value` exactly when every sign is even and every eligible
reading is that value. -/
theorem consensusLaw_map_eq_some_iff_allEven {G E : Type*}
    (C : List (Option RS) → Option RS) (law : ConsensusLaw C)
    (act : G → E → E) (sign : G → Bool) (reading : E → Option RS)
    (nonempty : Nonempty E)
    (transitive : ∀ e₁ e₂ : E, ∃ g : G, act g e₁ = e₂)
    (transport : ∀ (g : G) (e : E), reading (act g e) = flipReading (sign g) (reading e))
    (failure : ∀ e : E, reading e = none → OddStabilizer act sign e)
    (L : List E) (complete : ∀ e : E, e ∈ L) (value : RS) :
    C (L.map reading) = some value ↔ AllEven sign ∧ CommonValue reading value := by
  constructor
  · intro h
    have entries := (law.eq_some_iff (L.map reading) value).mp h
    have common : CommonValue reading value := by
      intro e
      exact entries.2 (reading e) (List.mem_map.mpr ⟨e, complete e, rfl⟩)
    exact
      ⟨(consensusSuccess_iff_allEven_core act sign reading nonempty transitive transport
          failure).mp ⟨value, common⟩,
        common⟩
  · rintro ⟨hall, common⟩
    refine (law.eq_some_iff (L.map reading) value).mpr ⟨?_, ?_⟩
    · obtain ⟨e⟩ := nonempty
      intro nil
      have member : reading e ∈ L.map reading := List.mem_map.mpr ⟨e, complete e, rfl⟩
      rw [nil] at member
      simp at member
    · intro entry member
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp member
      exact common e

/-- A list consensus refuses exactly when some acting element is odd. -/
theorem consensusLaw_map_eq_none_iff_hasOdd {G E : Type*}
    (C : List (Option RS) → Option RS) (law : ConsensusLaw C)
    (act : G → E → E) (sign : G → Bool) (reading : E → Option RS)
    (nonempty : Nonempty E)
    (transitive : ∀ e₁ e₂ : E, ∃ g : G, act g e₁ = e₂)
    (transport : ∀ (g : G) (e : E), reading (act g e) = flipReading (sign g) (reading e))
    (failure : ∀ e : E, reading e = none → OddStabilizer act sign e)
    (L : List E) (complete : ∀ e : E, e ∈ L) :
    C (L.map reading) = none ↔ HasOdd sign := by
  constructor
  · intro hnone
    by_contra hno
    have hall : AllEven sign := (allEven_iff_not_hasOdd sign).mpr hno
    obtain ⟨e⟩ := nonempty
    obtain ⟨value, hvalue⟩ := reading_some_of_allEven act sign reading failure hall e
    have common : CommonValue reading value := fun e' =>
      reading_eq_of_allEven act sign reading hall transitive transport hvalue
    have hsome : C (L.map reading) = some value :=
      (consensusLaw_map_eq_some_iff_allEven C law act sign reading ⟨e⟩ transitive transport
        failure L complete value).mpr ⟨hall, common⟩
    rw [hsome] at hnone
    cases hnone
  · intro hodd
    obtain ⟨g, hg⟩ := hodd
    exact consensusLaw_map_eq_none_of_odd C law act sign reading nonempty transport L complete g hg

/-! ## Concrete corollaries for the runtime consensus -/

theorem consensus_map_eq_none_of_odd_core {G E : Type*} (act : G → E → E)
    (sign : G → Bool) (reading : E → Option RS) (nonempty : Nonempty E)
    (transport : ∀ (g : G) (e : E), reading (act g e) = flipReading (sign g) (reading e))
    (L : List E) (complete : ∀ e : E, e ∈ L)
    (g : G) (hodd : sign g = true) :
    consensus (L.map reading) = none :=
  consensusLaw_map_eq_none_of_odd consensus consensusLaw_consensus act sign reading nonempty
    transport L complete g hodd

theorem consensus_map_eq_some_iff_allEven_core {G E : Type*} (act : G → E → E)
    (sign : G → Bool) (reading : E → Option RS) (nonempty : Nonempty E)
    (transitive : ∀ e₁ e₂ : E, ∃ g : G, act g e₁ = e₂)
    (transport : ∀ (g : G) (e : E), reading (act g e) = flipReading (sign g) (reading e))
    (failure : ∀ e : E, reading e = none → OddStabilizer act sign e)
    (L : List E) (complete : ∀ e : E, e ∈ L) (value : RS) :
    consensus (L.map reading) = some value ↔ AllEven sign ∧ CommonValue reading value :=
  consensusLaw_map_eq_some_iff_allEven consensus consensusLaw_consensus act sign reading nonempty
    transitive transport failure L complete value

theorem consensus_map_eq_none_iff_hasOdd_core {G E : Type*} (act : G → E → E)
    (sign : G → Bool) (reading : E → Option RS) (nonempty : Nonempty E)
    (transitive : ∀ e₁ e₂ : E, ∃ g : G, act g e₁ = e₂)
    (transport : ∀ (g : G) (e : E), reading (act g e) = flipReading (sign g) (reading e))
    (failure : ∀ e : E, reading e = none → OddStabilizer act sign e)
    (L : List E) (complete : ∀ e : E, e ∈ L) :
    consensus (L.map reading) = none ↔ HasOdd sign :=
  consensusLaw_map_eq_none_iff_hasOdd consensus consensusLaw_consensus act sign reading nonempty
    transitive transport failure L complete

/-! ## `MulAction` list corollaries -/

section MulActionConsensus

variable {G E : Type*} [Group G] [MulAction G E]

theorem consensus_map_eq_some_of_allEven (sign : G → Bool) (reading : E → Option RS)
    (nonempty : Nonempty E)
    (transitive : ∀ e₁ e₂ : E, ∃ g : G, g • e₁ = e₂)
    (transport : ∀ (g : G) (e : E), reading (g • e) = flipReading (sign g) (reading e))
    (L : List E) (complete : ∀ e : E, e ∈ L)
    (hall : AllEven sign) (e : E) (value : RS) (hvalue : reading e = some value) :
    consensus (L.map reading) = some value :=
  consensus_map_eq_some_of_allEven_core (fun g e => g • e) sign reading nonempty
    (fun e₁ e₂ => transitive e₁ e₂) (fun g e => transport g e) L complete hall e value hvalue

theorem consensus_map_eq_none_of_odd (sign : G → Bool) (reading : E → Option RS)
    (nonempty : Nonempty E)
    (transport : ∀ (g : G) (e : E), reading (g • e) = flipReading (sign g) (reading e))
    (L : List E) (complete : ∀ e : E, e ∈ L)
    (g : G) (hodd : sign g = true) :
    consensus (L.map reading) = none :=
  consensus_map_eq_none_of_odd_core (fun g e => g • e) sign reading nonempty transport
    L complete g hodd

theorem consensus_map_eq_some_iff_allEven (sign : G → Bool) (reading : E → Option RS)
    (nonempty : Nonempty E)
    (transitive : ∀ e₁ e₂ : E, ∃ g : G, g • e₁ = e₂)
    (transport : ∀ (g : G) (e : E), reading (g • e) = flipReading (sign g) (reading e))
    (failure : ∀ e : E, reading e = none ↔ ∃ g : G, sign g = true ∧ g • e = e)
    (L : List E) (complete : ∀ e : E, e ∈ L) (value : RS) :
    consensus (L.map reading) = some value ↔ AllEven sign ∧ CommonValue reading value := by
  refine consensus_map_eq_some_iff_allEven_core (fun g e => g • e) sign reading nonempty
    (fun e₁ e₂ => transitive e₁ e₂) (fun g e => transport g e) ?_ L complete value
  intro e h
  obtain ⟨g, hg, hfix⟩ := (failure e).mp h
  exact ⟨g, hg, hfix⟩

theorem consensus_map_eq_none_iff_hasOdd (sign : G → Bool) (reading : E → Option RS)
    (nonempty : Nonempty E)
    (transitive : ∀ e₁ e₂ : E, ∃ g : G, g • e₁ = e₂)
    (transport : ∀ (g : G) (e : E), reading (g • e) = flipReading (sign g) (reading e))
    (failure : ∀ e : E, reading e = none ↔ ∃ g : G, sign g = true ∧ g • e = e)
    (L : List E) (complete : ∀ e : E, e ∈ L) :
    consensus (L.map reading) = none ↔ HasOdd sign := by
  refine consensus_map_eq_none_iff_hasOdd_core (fun g e => g • e) sign reading nonempty
    (fun e₁ e₂ => transitive e₁ e₂) (fun g e => transport g e) ?_ L complete
  intro e h
  obtain ⟨g, hg, hfix⟩ := (failure e).mp h
  exact ⟨g, hg, hfix⟩

end MulActionConsensus

end TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus

/-! ## Kernel guards

Root should run these with the guarded exact-module build.  They are deliberately placed on the
principal results; helper lemmas unfold to the same accepted axioms. -/

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.rs_swap_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.flipReading_true_ne_some
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.allEven_iff_not_hasOdd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.reading_invariant_of_allEven
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.reading_some_of_allEven
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.reading_eq_of_allEven
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.consensusSuccess_iff_allEven_core
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.not_consensusSuccess_of_odd_core
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.not_consensusSuccess_of_hasOdd_core
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.consensusSuccess_iff_no_odd_core
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.consensusSuccess_iff_allEven
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.consensusSuccess_iff_no_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.consensus_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.consensusLaw_consensus
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.consensus_map_eq_some_of_allEven_core
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.consensusLaw_map_eq_none_of_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.consensusLaw_map_eq_some_iff_allEven
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.consensusLaw_map_eq_none_iff_hasOdd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.consensus_map_eq_some_of_allEven
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.consensus_map_eq_none_of_odd_core
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.consensus_map_eq_some_iff_allEven_core
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.consensus_map_eq_none_iff_hasOdd_core
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.consensus_map_eq_some_iff_allEven
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStabilizerConsensus.consensus_map_eq_none_iff_hasOdd
