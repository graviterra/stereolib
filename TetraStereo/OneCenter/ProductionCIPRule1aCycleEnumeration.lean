import TetraStereo.OneCenter.ProductionCIPRule1aSimpleCycle

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace MoleculeGraph

universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

private theorem Multiset.map_eq_replicate_of_forall
    {alpha beta : Type*} (values : Multiset alpha) (field : alpha → beta) (value : beta)
    (h : ∀ item ∈ values, field item = value) :
    values.map field = Multiset.replicate values.card value := by
  induction values using Multiset.induction_on with
  | empty => simp
  | @cons item values inductionHypothesis =>
      have hitem : field item = value := h item (by simp)
      have htail : ∀ other ∈ values, field other = value := by
        intro other hother
        exact h other (by simp [hother])
      simp [hitem, inductionHypothesis htail]

/-- Standard independent enumeration invariant for an even simple cycle: its maximum family is
exactly the two alternating matchings, pairing the attached vertex with its two neighbors. -/
def EvenCycleMaximumEnumeration (molecule : MoleculeGraph Atom)
    (attached first second : Atom) : Prop :=
  ∃ firstMatching secondMatching,
    (molecule.maximumMancudeMatchings attached).1 =
      {firstMatching, secondMatching} ∧
    molecule.mancudePartnerAtomicNumber attached firstMatching = molecule.atomZ first ∧
    molecule.mancudePartnerAtomicNumber attached secondMatching = molecule.atomZ second

/-- Standard independent enumeration invariant for an odd `2*k+1` cycle.  Its maximum matchings
split into `k` matchings pairing the attached vertex with each neighbor, plus one matching leaving
the attached vertex unmatched. -/
def OddCycleMaximumEnumeration (molecule : MoleculeGraph Atom)
    (attached first second : Atom) (k : ℕ) : Prop :=
  ∃ (firstFamily secondFamily : Multiset (Atom → Option Atom))
      (unmatched : Atom → Option Atom),
    (molecule.maximumMancudeMatchings attached).1 =
      firstFamily + secondFamily + {unmatched} ∧
    firstFamily.card = k ∧ secondFamily.card = k ∧
    (∀ matching ∈ firstFamily,
      molecule.mancudePartnerAtomicNumber attached matching = molecule.atomZ first) ∧
    (∀ matching ∈ secondFamily,
      molecule.mancudePartnerAtomicNumber attached matching = molecule.atomZ second) ∧
    molecule.mancudePartnerAtomicNumber attached unmatched = 0

/-- The standard two-matching enumeration yields the even contribution profile. -/
theorem evenSimpleCycleProfile_of_enumeration
    (molecule : MoleculeGraph Atom) (attached first second : Atom)
    (henumeration : molecule.EvenCycleMaximumEnumeration attached first second) :
    molecule.EvenSimpleCycleProfile attached first second := by
  obtain ⟨firstMatching, secondMatching, hfamily, hfirst, hsecond⟩ := henumeration
  unfold EvenSimpleCycleProfile
  rw [hfamily]
  simp [hfirst, hsecond]

/-- The standard `k+k+1` enumeration yields the odd contribution profile. -/
theorem oddSimpleCycleProfile_of_enumeration
    (molecule : MoleculeGraph Atom) (attached first second : Atom) (k : ℕ)
    (henumeration : molecule.OddCycleMaximumEnumeration attached first second k) :
    molecule.OddSimpleCycleProfile attached first second k := by
  obtain ⟨firstFamily, secondFamily, unmatched, hfamily,
    hfirstCard, hsecondCard, hfirst, hsecond, hunmatched⟩ := henumeration
  unfold OddSimpleCycleProfile
  rw [hfamily, Multiset.map_add, Multiset.map_add,
    Multiset.map_eq_replicate_of_forall firstFamily
      (molecule.mancudePartnerAtomicNumber attached) (molecule.atomZ first) hfirst,
    Multiset.map_eq_replicate_of_forall secondFamily
      (molecule.mancudePartnerAtomicNumber attached) (molecule.atomZ second) hsecond,
    hfirstCard, hsecondCard]
  simp [hunmatched]

end MoleculeGraph

end
end OneCenter
end TetraStereo
