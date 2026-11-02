import TetraStereo.OneCenter.ProductionCIPRule1aAssembly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace MoleculeGraph

universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Independent maximum-matching profile of an even localized simple cycle at one attached atom.
The two alternating maximum matchings pair it once with each cycle neighbor. -/
def EvenSimpleCycleProfile (molecule : MoleculeGraph Atom)
    (attached first second : Atom) : Prop :=
  ((molecule.maximumMancudeMatchings attached).1.map
      (molecule.mancudePartnerAtomicNumber attached)) =
    {molecule.atomZ first, molecule.atomZ second}

/-- Independent maximum-matching profile of an odd localized simple cycle of length `2*k+1`.
The attached atom is paired `k` times with each neighbor and is unmatched once. -/
def OddSimpleCycleProfile (molecule : MoleculeGraph Atom)
    (attached first second : Atom) (k : ℕ) : Prop :=
  ((molecule.maximumMancudeMatchings attached).1.map
      (molecule.mancudePartnerAtomicNumber attached)) =
    Multiset.replicate k (molecule.atomZ first) +
      Multiset.replicate k (molecule.atomZ second) + {0}

/-- Independent profile for a localized component in which every maximum matching gives the
attached atom the same atomic-number contribution. -/
def UniformPartnerProfile (molecule : MoleculeGraph Atom)
    (attached duplicated : Atom) : Prop :=
  ((molecule.maximumMancudeMatchings attached).1.map
      (molecule.mancudePartnerAtomicNumber attached)) =
    Multiset.replicate (molecule.maximumMancudeMatchings attached).card
      (molecule.atomZ duplicated)

/-- The independent exact average of an even simple-cycle profile is the unreduced mean of its
two alternating partners. -/
theorem exactMancudeAverage_eq_evenSimpleCycle
    (molecule : MoleculeGraph Atom) (attached first second : Atom)
    (hprofile : molecule.EvenSimpleCycleProfile attached first second) :
    molecule.exactMancudeAverage attached =
      ⟨molecule.atomZ first + molecule.atomZ second, 2, by decide⟩ := by
  apply ExactAtomicNumber.ext
  · simpa [exactMancudeAverage, EvenSimpleCycleProfile] using congrArg Multiset.sum hprofile
  · simpa [exactMancudeAverage, EvenSimpleCycleProfile] using congrArg Multiset.card hprofile

/-- The independent exact average of an odd simple-cycle profile has the production formula:
each neighboring contribution occurs `k` times and the unmatched form contributes zero. -/
theorem exactMancudeAverage_eq_oddSimpleCycle
    (molecule : MoleculeGraph Atom) (attached first second : Atom) (k : ℕ)
    (hprofile : molecule.OddSimpleCycleProfile attached first second k) :
    molecule.exactMancudeAverage attached =
      ⟨k * (molecule.atomZ first + molecule.atomZ second), 2 * k + 1,
        by omega⟩ := by
  apply ExactAtomicNumber.ext
  · have hsum := congrArg Multiset.sum hprofile
    simpa [exactMancudeAverage, OddSimpleCycleProfile, Nat.mul_add,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum
  · have hcard := congrArg Multiset.card hprofile
    simp at hcard
    change (molecule.maximumMancudeMatchings attached).card = 2 * k + 1
    omega

/-- A uniform maximum-matching partner profile has the duplicated atom's integral value. -/
theorem exactMancudeAverage_value_eq_uniformPartner
    (molecule : MoleculeGraph Atom) (attached duplicated : Atom)
    (hprofile : molecule.UniformPartnerProfile attached duplicated) :
    (molecule.exactMancudeAverage attached).value =
      (ExactAtomicNumber.ofNat (molecule.atomZ duplicated)).value := by
  have hsum := congrArg Multiset.sum hprofile
  have hcardPos : 0 < (molecule.maximumMancudeMatchings attached).card :=
    Finset.card_pos.mpr (molecule.maximumMancudeMatchings_nonempty attached)
  unfold exactMancudeAverage ExactAtomicNumber.value ExactAtomicNumber.ofNat
  simp at hsum
  rw [hsum]
  push_cast
  field_simp

end MoleculeGraph

namespace RawMolecule

/-- The production even-cycle shortcut realizes the independent maximum-matching mean whenever
the detected cycle has the corresponding independent even-cycle profile. -/
theorem simpleMancudeCycle_even_label_sound
    (mol : RawMolecule) (attached duplicated : Fin mol.atomCount)
    (cycle : List ℕ) (alternate : Fin mol.atomCount)
    (hlocalized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.1 duplicated.1 = true)
    (hcycle : mol.simpleMancudeCycle? attached.1 duplicated.1 =
      some (cycle, alternate.1))
    (heven : cycle.length % 2 = 0) :
    mol.mancudeRule1aLabel? attached.1 duplicated.1 =
      some ⟨mol.toMoleculeGraph.atomZ duplicated +
        mol.toMoleculeGraph.atomZ alternate, 2⟩ := by
  unfold mancudeRule1aLabel?
  simp [hlocalized, hcycle, simpleMancudeCycleLabel, heven,
    mol.atomZAt_eq_toMoleculeGraph_atomZ duplicated.1 duplicated.2,
    mol.atomZAt_eq_toMoleculeGraph_atomZ alternate.1 alternate.2]

/-- Consequently the production even-cycle label has exactly the independent rational value. -/
theorem simpleMancudeCycle_even_sound
    (mol : RawMolecule) (attached duplicated : Fin mol.atomCount)
    (cycle : List ℕ) (alternate : Fin mol.atomCount)
    (hlocalized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.1 duplicated.1 = true)
    (hcycle : mol.simpleMancudeCycle? attached.1 duplicated.1 =
      some (cycle, alternate.1))
    (heven : cycle.length % 2 = 0)
    (hprofile : mol.toMoleculeGraph.EvenSimpleCycleProfile
      attached duplicated alternate) :
    ∃ label, mol.mancudeRule1aLabel? attached.1 duplicated.1 = some label ∧
      label.toExactAtomicNumber.value =
        (mol.toMoleculeGraph.exactMancudeAverage attached).value := by
  let label : CIPAtomicLabel :=
    ⟨mol.toMoleculeGraph.atomZ duplicated + mol.toMoleculeGraph.atomZ alternate, 2⟩
  refine ⟨label, mol.simpleMancudeCycle_even_label_sound attached duplicated cycle alternate
    hlocalized hcycle heven, ?_⟩
  rw [mol.toMoleculeGraph.exactMancudeAverage_eq_evenSimpleCycle
    attached duplicated alternate hprofile]
  rfl

/-- The production odd-cycle shortcut has its stated `k/(2*k+1)` formula. -/
theorem simpleMancudeCycle_odd_label_sound
    (mol : RawMolecule) (attached duplicated : Fin mol.atomCount)
    (cycle : List ℕ) (alternate : Fin mol.atomCount) (k : ℕ)
    (hlocalized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.1 duplicated.1 = true)
    (hcycle : mol.simpleMancudeCycle? attached.1 duplicated.1 =
      some (cycle, alternate.1))
    (hlength : cycle.length = 2 * k + 1) :
    mol.mancudeRule1aLabel? attached.1 duplicated.1 =
      some ⟨k * (mol.toMoleculeGraph.atomZ duplicated +
        mol.toMoleculeGraph.atomZ alternate), 2 * k + 1⟩ := by
  have hdiv : (2 * k + 1) / 2 = k := by omega
  unfold mancudeRule1aLabel?
  simp [hlocalized, hcycle, simpleMancudeCycleLabel, hlength, hdiv,
    mol.atomZAt_eq_toMoleculeGraph_atomZ duplicated.1 duplicated.2,
    mol.atomZAt_eq_toMoleculeGraph_atomZ alternate.1 alternate.2]

/-- The production odd-cycle shortcut realizes the independent all-maximum-matching mean under
the independent odd-cycle profile. -/
theorem simpleMancudeCycle_odd_sound
    (mol : RawMolecule) (attached duplicated : Fin mol.atomCount)
    (cycle : List ℕ) (alternate : Fin mol.atomCount) (k : ℕ)
    (hlocalized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.1 duplicated.1 = true)
    (hcycle : mol.simpleMancudeCycle? attached.1 duplicated.1 =
      some (cycle, alternate.1))
    (hlength : cycle.length = 2 * k + 1)
    (hprofile : mol.toMoleculeGraph.OddSimpleCycleProfile
      attached duplicated alternate k) :
    ∃ label, mol.mancudeRule1aLabel? attached.1 duplicated.1 = some label ∧
      label.toExactAtomicNumber.value =
        (mol.toMoleculeGraph.exactMancudeAverage attached).value := by
  let label : CIPAtomicLabel :=
    ⟨k * (mol.toMoleculeGraph.atomZ duplicated +
      mol.toMoleculeGraph.atomZ alternate), 2 * k + 1⟩
  refine ⟨label, mol.simpleMancudeCycle_odd_label_sound attached duplicated
    cycle alternate k hlocalized hcycle hlength, ?_⟩
  rw [mol.toMoleculeGraph.exactMancudeAverage_eq_oddSimpleCycle
    attached duplicated alternate k hprofile]
  simp [label, CIPAtomicLabel.toExactAtomicNumber,
    CIPAtomicLabel.effectiveDenominator, ExactAtomicNumber.value]

/-- After simple-cycle detection fails, production delegates even the apparent single-partner case
to the exhaustive component matcher.  A length-one syntactic partner list does not imply that the
attached atom has a uniform partner across all maximum matchings. -/
theorem mancudeNoSimpleCycle_label
    (mol : RawMolecule) (attached duplicated : Fin mol.atomCount)
    (hlocalized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.1 duplicated.1 = true)
    (hcycle : mol.simpleMancudeCycle? attached.1 duplicated.1 = none)
    (label : CIPAtomicLabel)
    (hgeneral : mol.generalMancudeRule1aLabel? attached.1 duplicated.1 = some label) :
    mol.mancudeRule1aLabel? attached.1 duplicated.1 =
      some label := by
  unfold mancudeRule1aLabel?
  simp [hlocalized, hcycle, hgeneral]

/-- The repaired apparent-single-partner branch is exact whenever the general executable matcher
returns a label; no uniform-profile assumption is needed. -/
theorem mancudeNoSimpleCycle_sound
    (mol : RawMolecule) (attached duplicated : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (hlocalized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.1 duplicated.1 = true)
    (hcycle : mol.simpleMancudeCycle? attached.1 duplicated.1 = none)
    (label : CIPAtomicLabel)
    (hgeneral : mol.generalMancudeRule1aLabel? attached.1 duplicated.1 = some label) :
    ∃ label, mol.mancudeRule1aLabel? attached.1 duplicated.1 = some label ∧
      label.toExactAtomicNumber.value =
        (mol.toMoleculeGraph.exactMancudeAverage attached).value := by
  exact ⟨label, mol.mancudeNoSimpleCycle_label attached duplicated hlocalized hcycle
    label hgeneral, mol.generalMancudeRule1aLabel_exactAverage hwellFormed hunique
      attached duplicated label hgeneral⟩

end RawMolecule

end
end OneCenter
end TetraStereo
