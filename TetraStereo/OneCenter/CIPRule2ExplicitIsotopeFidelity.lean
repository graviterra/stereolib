/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TetraStereo.OneCenter.CIPRule2MassData
import TetraStereo.OneCenter.BranchSphereKey
import TetraStereo.OneCenter.AuthoritativeLocalizedCIPAnalysis
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Exact-mass fidelity to P-92.3 for explicitly labelled isotopes

IUPAC *Blue Book* P-92.3 (`P9.txt`, line 1147) orders isotopes of one element by *decreasing
integer mass number*: "Higher atomic mass number precedes lower atomic mass number."  The
production implementation, however, stores and compares exact AME-2020 isotope masses
(`CIPRule2MassData.isotopeAtomicMassPico?`, scaled by `10 ^ 12`).

This module proves the missing general bridge between those two data meanings.  The frozen
per-element tables are already kernel-checked
(`CIPRule2MassData.all_isotope_mass_lists_are_valid`) to be strictly increasing in *both* mass
number and exact mass.  Consequently, for every atomic number `z ∈ currentAtomicNumbers` and every
pair of successful explicit-nuclide lookups `(a, ma)` and `(b, mb)`, exact-mass comparison agrees
with mass-number comparison:

`compare ma mb = compare a b`

and likewise for `<` and `=` (`..._lt_iff`, `..._eq_iff`).  The proof is structural: it derives
membership from lookup success, and then reads the ordering off the checked `List.Pairwise`
validity of the frozen table.  No order-preservation hypothesis is assumed and no per-pair fixture
is enumerated.

The statement covers the whole frozen nuclide table.  Every stored row is a successful lookup of
its own stored exact mass (`lookupMassNumber?_eq_some_of_mem_of_valid`), and the table contains
`CIPRule2MassData.Generated.isotopeMassRecordCount = 3557` rows
(`CIPRule2MassData.supportedNuclides_count`); the membership form
`isotopeAtomicMassPico?_compare_eq_of_mem` states the result directly for two stored rows.

The bridge is pushed through the implementation in two further steps:

* `RawMolecule.atomMassAt` (the exact Rule-2 observation used by the node comparator) and the
  primitive Rule-2 node comparator `RawMolecule.compareCanonicalNodeRule .rule2` compare equal to
  the mass-number comparison on two real atom nodes of the same element carrying explicit isotope
  labels (`atomMassAt_compare_eq_of_explicit_isotope`,
  `compareCanonicalNodeRule_rule2_eq_of_explicit_isotope`).
* the actual certified real-root consumer, `CertifiedLocalizedCIPInput` over a semantic molecule,
  produces `cipTraceOutcome (compareOfficialNodeTrace (rootFromEdge parent left)
  (rootFromEdge parent right)) = Ordering.lt` whenever the two root atoms have the same atomic
  number, carry explicit isotope labels `some a` and `some b`, and `a < b`
  (`official_root_trace_outcome_lt_of_explicit_isotope_lt`).  Readiness supplies the successful
  Rule-2 lookups; no mass ordering is supplied by the caller.  The checked consumer lemma
  `CertifiedLocalizedCIPInput.official_root_trace_outcome_lt_of_rule2_mass_lt` exposes exactly the
  three-decision official trace characterized by
  `CertifiedLocalizedCIPInput.official_root_trace_exact` and reduces its outcome.

## Scope and non-claims

The theorem concerns explicitly labelled nuclides (`isotope? = some A`) of one and the same
element, which is exactly the situation in which Rule 1a has tied on atomic number and P-92.3 is
consulted.  It makes no new claim about:

* ordinary unlabelled composition (`rule2MassPico? z none`), whose value is the separate ordinary
  reference/abridged-weight policy;
* multiple-bond-duplicate or ring-duplicate nodes, whose implementation Rule-2 mass is the
  separate zero convention;
* mass numbers absent from the frozen AME table, which the implementation refuses; readiness
  rules them out rather than fabricating an ordering.

The certified consumer statement is a *pair of real roots* statement only.  Whole-ligand
scheduling, descriptor assignment and the remaining Rule-3--6 stages are separate obligations.

It also does not assert the proposed exact-mass extension of Rule 2 discussed in the 2018 author
preprint (`Hanson2018-preprint.txt`); it proves only that on the common explicitly-labelled
same-element domain the implemented exact masses are order-isomorphic to the source's mass
numbers.
-/

namespace TetraStereo.OneCenter.CIPRule2ExplicitIsotopeFidelity

open TetraStereo.OneCenter.CIPRule2MassData

/-! ## Structural lookup lemmas -/

/-- Successful lookup returns a record that is actually present in the table. -/
theorem lookupMassNumber?_some_mem {records : List (Nat × MassPico)} {a : Nat} {m : MassPico}
    (lookup : lookupMassNumber? records a = some m) : (a, m) ∈ records := by
  induction records with
  | nil => simp [lookupMassNumber?] at lookup
  | cons head tail inductionHypothesis =>
      obtain ⟨k, v⟩ := head
      by_cases matching : k = a
      · have hv : v = m := by simpa [lookupMassNumber?, matching] using lookup
        subst hv
        rw [matching]
        exact List.mem_cons_self ..
      · have tailLookup : lookupMassNumber? tail a = some m := by
          simpa [lookupMassNumber?, matching] using lookup
        exact List.mem_cons_of_mem _ (inductionHypothesis tailLookup)

/-- Successful lookup is functional: a fixed mass number has at most one exact mass. -/
theorem lookupMassNumber?_eq_of_eq {records : List (Nat × MassPico)} {a ma mb : Nat}
    (first : lookupMassNumber? records a = some ma)
    (second : lookupMassNumber? records a = some mb) : ma = mb := by
  rw [first] at second
  exact Option.some.inj second

/-- On a strictly sorted table, two distinct present records are comparable in table order.
This is the only place where the checked `List.Pairwise` validity of a frozen table is used. -/
theorem pairwise_rel_or_rel_of_mem_of_ne {α : Type*} {relation : α → α → Prop}
    {records : List α} {left right : α} (ordered : records.Pairwise relation)
    (leftMem : left ∈ records) (rightMem : right ∈ records) (distinct : left ≠ right) :
    relation left right ∨ relation right left := by
  induction records with
  | nil => simp at leftMem
  | cons head tail inductionHypothesis =>
      rw [List.pairwise_cons] at ordered
      obtain ⟨headRelation, tailOrdered⟩ := ordered
      rcases List.mem_cons.mp leftMem with leftEq | leftTail
      · subst leftEq
        rcases List.mem_cons.mp rightMem with rightEq | rightTail
        · exact absurd rightEq.symm distinct
        · exact Or.inl (headRelation right rightTail)
      · rcases List.mem_cons.mp rightMem with rightEq | rightTail
        · subst rightEq
          exact Or.inr (headRelation left leftTail)
        · exact inductionHypothesis tailOrdered leftTail rightTail

/-- Present records of a valid table with distinct mass numbers are ordered exactly as the table
orders them: the earlier mass number is both smaller and lighter. -/
theorem lookupMassNumber?_lt_of_lt_of_valid {records : List (Nat × MassPico)}
    (valid : ValidIsotopeMassList records) {a ma b mb : Nat}
    (leftLookup : lookupMassNumber? records a = some ma)
    (rightLookup : lookupMassNumber? records b = some mb) (massNumberLt : a < b) :
    ma < mb := by
  unfold ValidIsotopeMassList at valid
  have leftMem : (a, ma) ∈ records := lookupMassNumber?_some_mem leftLookup
  have rightMem : (b, mb) ∈ records := lookupMassNumber?_some_mem rightLookup
  have distinct : (a, ma) ≠ (b, mb) := by
    intro equality
    have sameNumber : a = b := congrArg Prod.fst equality
    omega
  rcases pairwise_rel_or_rel_of_mem_of_ne valid leftMem rightMem distinct with order | order
  · exact order.2
  · exact absurd order.1 (Nat.lt_asymm massNumberLt)

/-- Every present record of a valid table is returned by the lookup at its own mass number.  This
makes the whole frozen nuclide table reachable by successful lookups. -/
theorem lookupMassNumber?_eq_some_of_mem_of_valid {records : List (Nat × MassPico)}
    (valid : ValidIsotopeMassList records) {a : Nat} {m : MassPico}
    (member : (a, m) ∈ records) : lookupMassNumber? records a = some m := by
  induction records with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      obtain ⟨k, v⟩ := head
      unfold ValidIsotopeMassList at valid
      rw [List.pairwise_cons] at valid
      obtain ⟨headRelation, tailValid⟩ := valid
      rcases List.mem_cons.mp member with headEq | tailMember
      · cases headEq
        simp [lookupMassNumber?]
      · have different : ¬ k = a := by
          intro same
          have ordered := headRelation (a, m) tailMember
          rw [same] at ordered
          exact Nat.lt_irrefl a ordered.1
        have tailLookup : lookupMassNumber? tail a = some m :=
          inductionHypothesis tailValid tailMember
        simpa [lookupMassNumber?, different] using tailLookup

/-! ## General exact-mass / mass-number comparison on one valid table -/

/-- **General fidelity theorem.**  On any table whose mass numbers and exact masses are both
strictly increasing, two successful lookups compare in exact mass exactly as their mass numbers
compare. -/
theorem lookupMassNumber?_compare_eq_of_valid {records : List (Nat × MassPico)}
    (valid : ValidIsotopeMassList records) {a ma b mb : Nat}
    (leftLookup : lookupMassNumber? records a = some ma)
    (rightLookup : lookupMassNumber? records b = some mb) :
    compare ma mb = compare a b := by
  rcases Nat.lt_trichotomy a b with numberLt | numberEq | numberGt
  · have massLt : ma < mb :=
      lookupMassNumber?_lt_of_lt_of_valid valid leftLookup rightLookup numberLt
    rw [Nat.compare_eq_lt.mpr massLt, Nat.compare_eq_lt.mpr numberLt]
  · subst numberEq
    have massEq : ma = mb := lookupMassNumber?_eq_of_eq leftLookup rightLookup
    rw [massEq]
    rw [Nat.compare_eq_eq.mpr rfl, Nat.compare_eq_eq.mpr rfl]
  · have massLt : mb < ma :=
      lookupMassNumber?_lt_of_lt_of_valid valid rightLookup leftLookup numberGt
    rw [Nat.compare_eq_gt.mpr massLt, Nat.compare_eq_gt.mpr numberGt]

/-- Exact-mass `<` is equivalent to mass-number `<` for two successful lookups. -/
theorem lookupMassNumber?_lt_iff_of_valid {records : List (Nat × MassPico)}
    (valid : ValidIsotopeMassList records) {a ma b mb : Nat}
    (leftLookup : lookupMassNumber? records a = some ma)
    (rightLookup : lookupMassNumber? records b = some mb) :
    ma < mb ↔ a < b := by
  constructor
  · intro massLt
    have compared := lookupMassNumber?_compare_eq_of_valid valid leftLookup rightLookup
    have massCompare : compare ma mb = Ordering.lt := Nat.compare_eq_lt.mpr massLt
    rw [compared] at massCompare
    exact Nat.compare_eq_lt.mp massCompare
  · exact lookupMassNumber?_lt_of_lt_of_valid valid leftLookup rightLookup

/-- Exact-mass equality is equivalent to mass-number equality for two successful lookups. -/
theorem lookupMassNumber?_eq_iff_of_valid {records : List (Nat × MassPico)}
    (valid : ValidIsotopeMassList records) {a ma b mb : Nat}
    (leftLookup : lookupMassNumber? records a = some ma)
    (rightLookup : lookupMassNumber? records b = some mb) :
    ma = mb ↔ a = b := by
  constructor
  · intro massEq
    have compared := lookupMassNumber?_compare_eq_of_valid valid leftLookup rightLookup
    have numberCompare : compare a b = Ordering.eq := by
      rw [← compared, massEq]
      exact Nat.compare_eq_eq.mpr rfl
    exact Nat.compare_eq_eq.mp numberCompare
  · intro numberEq
    subst numberEq
    exact lookupMassNumber?_eq_of_eq leftLookup rightLookup

/-! ## Frozen explicit-nuclide tables -/

/-- **P-92.3 fidelity for the frozen nuclide table.**  For any supported atomic number and any two
successful explicit-nuclide lookups, exact-mass comparison is mass-number comparison. -/
theorem isotopeAtomicMassPico?_compare_eq (atomicNumber : Nat)
    (current : atomicNumber ∈ currentAtomicNumbers) (a ma b mb : Nat)
    (leftLookup : isotopeAtomicMassPico? atomicNumber a = some ma)
    (rightLookup : isotopeAtomicMassPico? atomicNumber b = some mb) :
    compare ma mb = compare a b :=
  lookupMassNumber?_compare_eq_of_valid
    (every_isotope_mass_list_is_valid atomicNumber current) leftLookup rightLookup

/-- Exact-mass `<` agrees with mass-number `<` on the frozen explicit-nuclide tables. -/
theorem isotopeAtomicMassPico?_lt_iff (atomicNumber : Nat)
    (current : atomicNumber ∈ currentAtomicNumbers) (a ma b mb : Nat)
    (leftLookup : isotopeAtomicMassPico? atomicNumber a = some ma)
    (rightLookup : isotopeAtomicMassPico? atomicNumber b = some mb) :
    ma < mb ↔ a < b :=
  lookupMassNumber?_lt_iff_of_valid
    (every_isotope_mass_list_is_valid atomicNumber current) leftLookup rightLookup

/-- Exact-mass equality agrees with mass-number equality on the frozen explicit-nuclide tables. -/
theorem isotopeAtomicMassPico?_eq_iff (atomicNumber : Nat)
    (current : atomicNumber ∈ currentAtomicNumbers) (a ma b mb : Nat)
    (leftLookup : isotopeAtomicMassPico? atomicNumber a = some ma)
    (rightLookup : isotopeAtomicMassPico? atomicNumber b = some mb) :
    ma = mb ↔ a = b :=
  lookupMassNumber?_eq_iff_of_valid
    (every_isotope_mass_list_is_valid atomicNumber current) leftLookup rightLookup

/-- Membership form covering every one of the 3557 frozen rows: two stored exact nuclides of the
same supported element compare in exact mass exactly as their stored mass numbers compare. -/
theorem isotopeAtomicMassPico?_compare_eq_of_mem (atomicNumber : Nat)
    (current : atomicNumber ∈ currentAtomicNumbers) (a ma b mb : Nat)
    (leftStored : (a, ma) ∈ Generated.isotopeMassesPico atomicNumber)
    (rightStored : (b, mb) ∈ Generated.isotopeMassesPico atomicNumber) :
    compare ma mb = compare a b := by
  have valid := every_isotope_mass_list_is_valid atomicNumber current
  exact lookupMassNumber?_compare_eq_of_valid valid
    (lookupMassNumber?_eq_some_of_mem_of_valid valid leftStored)
    (lookupMassNumber?_eq_some_of_mem_of_valid valid rightStored)

/-- Source direction of P-92.3: the higher mass number compares greater (precedes under Rule 2). -/
theorem isotopeAtomicMassPico?_compare_eq_gt_iff (atomicNumber : Nat)
    (current : atomicNumber ∈ currentAtomicNumbers) (a ma b mb : Nat)
    (leftLookup : isotopeAtomicMassPico? atomicNumber a = some ma)
    (rightLookup : isotopeAtomicMassPico? atomicNumber b = some mb) :
    compare ma mb = Ordering.gt ↔ b < a := by
  rw [isotopeAtomicMassPico?_compare_eq atomicNumber current a ma b mb leftLookup rightLookup]
  exact Nat.compare_eq_gt

/-- The semantic Rule-2 spelling (`rule2MassPico?` on an explicit isotope label) inherits the same
fidelity. -/
theorem rule2MassPico?_explicit_compare_eq (atomicNumber : Nat)
    (current : atomicNumber ∈ currentAtomicNumbers) (a ma b mb : Nat)
    (leftLookup : rule2MassPico? atomicNumber (some a) = some ma)
    (rightLookup : rule2MassPico? atomicNumber (some b) = some mb) :
    compare ma mb = compare a b := by
  rw [rule2MassPico?_explicit] at leftLookup rightLookup
  exact isotopeAtomicMassPico?_compare_eq atomicNumber current a ma b mb leftLookup rightLookup

/-- The semantic Rule-2 spelling inherits the `<` equivalence. -/
theorem rule2MassPico?_explicit_lt_iff (atomicNumber : Nat)
    (current : atomicNumber ∈ currentAtomicNumbers) (a ma b mb : Nat)
    (leftLookup : rule2MassPico? atomicNumber (some a) = some ma)
    (rightLookup : rule2MassPico? atomicNumber (some b) = some mb) :
    ma < mb ↔ a < b := by
  rw [rule2MassPico?_explicit] at leftLookup rightLookup
  exact isotopeAtomicMassPico?_lt_iff atomicNumber current a ma b mb leftLookup rightLookup

/-! ## Implementation bridge: atom observations and the primitive Rule-2 comparator -/

/-- A supported atomic number is never the wildcard element. -/
theorem element_ne_wildcard_of_current (element : Element)
    (current : element.atomicNumber ∈ currentAtomicNumbers) : element ≠ Element.wildcard := by
  intro wildcard
  subst wildcard
  have wildcardZero : Element.wildcard.atomicNumber = 0 := rfl
  rw [wildcardZero, currentAtomicNumbers_exact, List.mem_range'_1] at current
  omega

/-- A successful explicit-nuclide lookup fixes the executable Rule-2 mass of the atom.  The value is
the stored exact AME mass; nothing is assumed about its comparison. -/
theorem atomMassAt_eq_of_isotope_lookup (mol : RawMolecule) (idx massNumber mass : Nat)
    (spec : AtomSpec) (observed : mol.atomAt? idx = some spec)
    (notWildcard : spec.element ≠ Element.wildcard)
    (isotope : spec.isotope? = some massNumber)
    (massObserved : isotopeAtomicMassPico? spec.element.atomicNumber massNumber = some mass) :
    mol.atomMassAt idx = mass := by
  simp [RawMolecule.atomMassAt, RawMolecule.atomMassAt?, RawMolecule.rule2MassPico?,
    observed, notWildcard, isotope, massObserved]

/-- **Executable Rule-2 observation fidelity.**  Two real atom positions carrying explicit isotopes
of the same supported element order their implemented exact Rule-2 masses exactly as P-92.3 orders
their mass numbers. -/
theorem atomMassAt_compare_eq_of_explicit_isotope (mol : RawMolecule) (element : Element)
    (elementCurrent : element.atomicNumber ∈ currentAtomicNumbers)
    (leftIndex rightIndex leftMassNumber rightMassNumber leftMass rightMass : Nat)
    (leftSpec rightSpec : AtomSpec)
    (leftAtom : mol.atomAt? leftIndex = some leftSpec)
    (rightAtom : mol.atomAt? rightIndex = some rightSpec)
    (leftElement : leftSpec.element = element) (rightElement : rightSpec.element = element)
    (leftIsotope : leftSpec.isotope? = some leftMassNumber)
    (rightIsotope : rightSpec.isotope? = some rightMassNumber)
    (leftLookup : isotopeAtomicMassPico? element.atomicNumber leftMassNumber = some leftMass)
    (rightLookup : isotopeAtomicMassPico? element.atomicNumber rightMassNumber = some rightMass) :
    compare (mol.atomMassAt leftIndex) (mol.atomMassAt rightIndex) =
      compare leftMassNumber rightMassNumber := by
  have elementNotWildcard : element ≠ Element.wildcard :=
    element_ne_wildcard_of_current element elementCurrent
  have leftNotWildcard : leftSpec.element ≠ Element.wildcard := by
    rw [leftElement]
    exact elementNotWildcard
  have rightNotWildcard : rightSpec.element ≠ Element.wildcard := by
    rw [rightElement]
    exact elementNotWildcard
  have leftMassObserved :
      isotopeAtomicMassPico? leftSpec.element.atomicNumber leftMassNumber = some leftMass := by
    rw [leftElement]
    exact leftLookup
  have rightMassObserved :
      isotopeAtomicMassPico? rightSpec.element.atomicNumber rightMassNumber = some rightMass := by
    rw [rightElement]
    exact rightLookup
  have leftMassEq : mol.atomMassAt leftIndex = leftMass :=
    atomMassAt_eq_of_isotope_lookup mol leftIndex leftMassNumber leftMass leftSpec
      leftAtom leftNotWildcard leftIsotope leftMassObserved
  have rightMassEq : mol.atomMassAt rightIndex = rightMass :=
    atomMassAt_eq_of_isotope_lookup mol rightIndex rightMassNumber rightMass rightSpec
      rightAtom rightNotWildcard rightIsotope rightMassObserved
  rw [leftMassEq, rightMassEq]
  exact isotopeAtomicMassPico?_compare_eq element.atomicNumber elementCurrent
    leftMassNumber leftMass rightMassNumber rightMass leftLookup rightLookup

/-- The Rule-2 branch of the primitive node comparator, exposed without the `let`-bound mass
function. -/
@[simp] theorem compareCanonicalNodeRule_rule2 (mol : RawMolecule)
    (left right : RawMolecule.CanonicalBranchNode) :
    mol.compareCanonicalNodeRule RawMolecule.CanonicalRuleStage.rule2 left right =
      compare
        (match left.provenance with
          | RawMolecule.CanonicalNodeProvenance.realAtom => mol.atomMassAt left.atom
          | _ => 0)
        (match right.provenance with
          | RawMolecule.CanonicalNodeProvenance.realAtom => mol.atomMassAt right.atom
          | _ => 0) := rfl

/-- **Primitive comparator fidelity.**  On two real atom nodes of the same supported element with
explicit isotope labels, the actual Rule-2 node comparison is exactly the mass-number comparison of
P-92.3. -/
theorem compareCanonicalNodeRule_rule2_eq_of_explicit_isotope (mol : RawMolecule)
    (element : Element) (elementCurrent : element.atomicNumber ∈ currentAtomicNumbers)
    (left right : RawMolecule.CanonicalBranchNode)
    (leftReal : left.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (rightReal : right.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (leftSpec rightSpec : AtomSpec)
    (leftAtom : mol.atomAt? left.atom = some leftSpec)
    (rightAtom : mol.atomAt? right.atom = some rightSpec)
    (leftElement : leftSpec.element = element) (rightElement : rightSpec.element = element)
    (leftMassNumber rightMassNumber leftMass rightMass : Nat)
    (leftIsotope : leftSpec.isotope? = some leftMassNumber)
    (rightIsotope : rightSpec.isotope? = some rightMassNumber)
    (leftLookup : isotopeAtomicMassPico? element.atomicNumber leftMassNumber = some leftMass)
    (rightLookup : isotopeAtomicMassPico? element.atomicNumber rightMassNumber = some rightMass) :
    mol.compareCanonicalNodeRule RawMolecule.CanonicalRuleStage.rule2 left right =
      compare leftMassNumber rightMassNumber := by
  have massComparison := atomMassAt_compare_eq_of_explicit_isotope mol element elementCurrent
    left.atom right.atom leftMassNumber rightMassNumber leftMass rightMass leftSpec rightSpec
    leftAtom rightAtom leftElement rightElement leftIsotope rightIsotope leftLookup rightLookup
  rw [compareCanonicalNodeRule_rule2, leftReal, rightReal]
  exact massComparison

/-! ## Certified real-root consumer bridge -/

/-- Every positive atomic number at most 118 is one of the frozen table's current atomic
numbers. -/
theorem mem_currentAtomicNumbers_of_positive_bounded (atomicNumber : Nat)
    (positive : 0 < atomicNumber) (bounded : atomicNumber ≤ 118) :
    atomicNumber ∈ currentAtomicNumbers := by
  rw [currentAtomicNumbers_exact, List.mem_range'_1]
  omega

/-- **Certified real-root consumer fidelity.**  In a certified localized input, two real hierarchy
roots `rootFromEdge parent left` and `rootFromEdge parent right` whose atoms have the same atomic
number and carry explicit isotope labels `some a` and `some b` with `a < b` produce the official
trace outcome `Ordering.lt`.

Both Rule-2 lookups are derived from the readiness certificate (`AllRule2MassesKnown`); the caller
supplies no mass and no mass ordering.  The masses are then ordered by the frozen-table fidelity
theorem, and the existing checked consumer lemma turns that mass ordering into the trace outcome.
This is a pair-of-roots statement; whole-ligand scheduling and descriptor assignment remain
separate obligations. -/
theorem official_root_trace_outcome_lt_of_explicit_isotope_lt
    (input : CertifiedLocalizedCIPInput) (parent left right : input.Atom)
    (sameElement :
      (input.certified.input.molecule.atoms.get left).element.atomicNumber =
        (input.certified.input.molecule.atoms.get right).element.atomicNumber)
    (leftMassNumber rightMassNumber : Nat)
    (leftIsotope :
      (input.certified.input.molecule.atoms.get left).isotopeMassNumber? = some leftMassNumber)
    (rightIsotope :
      (input.certified.input.molecule.atoms.get right).isotopeMassNumber? = some rightMassNumber)
    (massNumberLt : leftMassNumber < rightMassNumber) :
    cipTraceOutcome
      (input.moleculeGraph.compareOfficialNodeTrace
        (OfficialCIPNode.rootFromEdge parent left)
        (OfficialCIPNode.rootFromEdge parent right)) = Ordering.lt := by
  obtain ⟨leftMass, leftMassObserved⟩ :=
    input.graphReady.2.2.1 (input.certified.input.molecule.atoms.get left)
      (List.get_mem _ _)
  obtain ⟨rightMass, rightMassObserved⟩ :=
    input.graphReady.2.2.1 (input.certified.input.molecule.atoms.get right)
      (List.get_mem _ _)
  have leftCurrent :
      (input.certified.input.molecule.atoms.get left).element.atomicNumber ∈
        currentAtomicNumbers :=
    mem_currentAtomicNumbers_of_positive_bounded _
      (input.certified.input.molecule.atoms.get left).element.positive
      (input.certified.input.molecule.atoms.get left).element.atMost118
  have leftLookup :
      CIPRule2MassData.rule2MassPico?
          (input.certified.input.molecule.atoms.get left).element.atomicNumber
          (some leftMassNumber) = some leftMass := by
    have observed := leftMassObserved
    simp only [SemanticAtom.rule2MassPico?] at observed
    rw [leftIsotope] at observed
    exact observed
  have rightLookup :
      CIPRule2MassData.rule2MassPico?
          (input.certified.input.molecule.atoms.get left).element.atomicNumber
          (some rightMassNumber) = some rightMass := by
    have observed := rightMassObserved
    simp only [SemanticAtom.rule2MassPico?] at observed
    rw [rightIsotope] at observed
    rw [sameElement]
    exact observed
  have massLower :
      (input.certified.input.molecule.atoms.get left).rule2MassPico?.getD 0 <
        (input.certified.input.molecule.atoms.get right).rule2MassPico?.getD 0 := by
    simp only [leftMassObserved, rightMassObserved, Option.getD_some]
    exact (rule2MassPico?_explicit_lt_iff
      (input.certified.input.molecule.atoms.get left).element.atomicNumber leftCurrent
      leftMassNumber leftMass rightMassNumber rightMass leftLookup rightLookup).mpr massNumberLt
  exact CertifiedLocalizedCIPInput.official_root_trace_outcome_lt_of_rule2_mass_lt
    input parent left right sameElement massLower

/-! ## Kernel-authority guards on the load-bearing general declarations -/

assert_kernel_only TetraStereo.OneCenter.CIPRule2ExplicitIsotopeFidelity.lookupMassNumber?_compare_eq_of_valid
assert_kernel_only TetraStereo.OneCenter.CIPRule2ExplicitIsotopeFidelity.lookupMassNumber?_lt_iff_of_valid
assert_kernel_only TetraStereo.OneCenter.CIPRule2ExplicitIsotopeFidelity.lookupMassNumber?_eq_iff_of_valid
assert_kernel_only TetraStereo.OneCenter.CIPRule2ExplicitIsotopeFidelity.isotopeAtomicMassPico?_compare_eq
assert_kernel_only TetraStereo.OneCenter.CIPRule2ExplicitIsotopeFidelity.isotopeAtomicMassPico?_compare_eq_of_mem
assert_kernel_only TetraStereo.OneCenter.CIPRule2ExplicitIsotopeFidelity.rule2MassPico?_explicit_compare_eq
assert_kernel_only TetraStereo.OneCenter.CIPRule2ExplicitIsotopeFidelity.atomMassAt_compare_eq_of_explicit_isotope
assert_kernel_only TetraStereo.OneCenter.CIPRule2ExplicitIsotopeFidelity.compareCanonicalNodeRule_rule2_eq_of_explicit_isotope
assert_kernel_only TetraStereo.OneCenter.CIPRule2ExplicitIsotopeFidelity.official_root_trace_outcome_lt_of_explicit_isotope_lt

end TetraStereo.OneCenter.CIPRule2ExplicitIsotopeFidelity
