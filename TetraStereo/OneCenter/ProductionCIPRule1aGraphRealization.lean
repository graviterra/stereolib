import TetraStereo.OneCenter.DeclarativeCIPRule1aExact
import TetraStereo.OneCenter.ProductionCIPExactExpansion
import TetraStereo.OneCenter.ProductionCIPReachability
import TetraStereo.OneCenter.ProductionCIPReachabilityBound

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace RawMolecule

open MoleculeGraph

private theorem edgeKey_eq_of_connects (bond : RawBond) (left right : ℕ)
    (hconnects : bond.connects left right = true) :
    RawBond.edgeKey bond = (min left right, max left right) := by
  simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at hconnects
  rcases hconnects with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · simp [RawBond.edgeKey, hsource, htarget]
  · simp [RawBond.edgeKey, hsource, htarget, min_comm, max_comm]

/-- Unordered bond-record uniqueness makes a connecting raw record unique as a value, not merely
as an edge-key occurrence. -/
theorem bond_eq_of_mem_of_connects (mol : RawMolecule) (hunique : mol.BondRecordsUnique)
    {first second : RawBond} (hfirst : first ∈ mol.bonds) (hsecond : second ∈ mol.bonds)
    {left right : ℕ} (hfirstConnects : first.connects left right = true)
    (hsecondConnects : second.connects left right = true) :
    first = second := by
  obtain ⟨firstIndex, hfirstIndex⟩ := List.get_of_mem hfirst
  obtain ⟨secondIndex, hsecondIndex⟩ := List.get_of_mem hsecond
  have hkeys : RawBond.edgeKey (mol.bonds.get firstIndex) =
      RawBond.edgeKey (mol.bonds.get secondIndex) := by
    rw [hfirstIndex, hsecondIndex,
      edgeKey_eq_of_connects first left right hfirstConnects,
      edgeKey_eq_of_connects second left right hsecondConnects]
  have hindex : firstIndex = secondIndex := by
    let firstMapped : Fin (mol.bonds.map RawBond.edgeKey).length :=
      ⟨firstIndex, by simp⟩
    let secondMapped : Fin (mol.bonds.map RawBond.edgeKey).length :=
      ⟨secondIndex, by simp⟩
    have hmapped : firstMapped = secondMapped := by
      apply hunique.injective_get
      simpa [firstMapped, secondMapped] using hkeys
    apply Fin.ext
    exact congrArg
      (fun index : Fin (mol.bonds.map RawBond.edgeKey).length => index.val) hmapped
  rw [← hfirstIndex, ← hsecondIndex, hindex]

private theorem foldDirectedBondOrder_eq_value
    (bonds : List RawBond) (left right value : ℕ)
    (hvalue : ∀ bond ∈ bonds, bond.directedConnects left right = true →
      bond.kind.order = value) :
    bonds.foldl
        (fun order bond =>
          if bond.directedConnects left right then max order bond.kind.order else order) value =
      value := by
  induction bonds with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      by_cases hdirected : head.directedConnects left right = true
      · simp only [List.foldl_cons, hdirected, ↓reduceIte,
          hvalue head (by simp) hdirected, max_self]
        apply inductionHypothesis
        intro bond hbond
        exact hvalue bond (by simp [hbond])
      · simp only [List.foldl_cons, hdirected]
        apply inductionHypothesis
        intro bond hbond
        exact hvalue bond (by simp [hbond])

private theorem foldDirectedBondOrder_eq_of_unique
    (bonds : List RawBond) (distinguished : RawBond) (left right : ℕ)
    (hmem : distinguished ∈ bonds)
    (hdirected : distinguished.directedConnects left right = true)
    (hunique : ∀ bond ∈ bonds,
      bond.directedConnects left right = true → bond = distinguished) :
    bonds.foldl
        (fun order bond =>
          if bond.directedConnects left right then max order bond.kind.order else order) 0 =
      distinguished.kind.order := by
  induction bonds with
  | nil => simp at hmem
  | cons head tail inductionHypothesis =>
      by_cases hhead : head = distinguished
      · subst head
        simp only [List.foldl_cons, hdirected, ↓reduceIte, Nat.zero_max]
        apply foldDirectedBondOrder_eq_value
        intro bond hbond hbondDirected
        rw [hunique bond (by simp [hbond]) hbondDirected]
      · have hheadDirected : head.directedConnects left right = false := by
          rw [Bool.eq_false_iff]
          intro htrue
          exact hhead (hunique head (by simp) htrue)
        simp only [List.foldl_cons, hheadDirected, Bool.false_eq_true, ↓reduceIte]
        apply inductionHypothesis
        · simpa [hhead, Ne.symm hhead] using hmem
        · intro bond hbond hbondDirected
          exact hunique bond (by simp [hbond]) hbondDirected

private theorem foldDirectedBondOrder_eq_zero
    (bonds : List RawBond) (left right : ℕ)
    (hnone : ∀ bond ∈ bonds, bond.directedConnects left right = false) :
    bonds.foldl
        (fun order bond =>
          if bond.directedConnects left right then max order bond.kind.order else order) 0 = 0 := by
  induction bonds with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.foldl_cons, hnone head (by simp), Bool.false_eq_true, ↓reduceIte]
      exact inductionHypothesis (fun bond hbond => hnone bond (by simp [hbond]))

private theorem foldDirectedBondOrder_pos_iff
    (bonds : List RawBond) (left right : ℕ) (initial : ℕ) :
    0 < bonds.foldl
        (fun order bond =>
          if bond.directedConnects left right then max order bond.kind.order else order) initial ↔
      0 < initial ∨ ∃ bond ∈ bonds, bond.directedConnects left right = true := by
  induction bonds generalizing initial with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp only [List.foldl_cons, inductionHypothesis]
      by_cases hdirected : head.directedConnects left right = true
      · have hpositive : 0 < head.kind.order := by cases head.kind <;> decide
        simp [hdirected, hpositive]
      · simp [hdirected]

theorem bondOrder_pos_iff_exists_bond (mol : RawMolecule) {left right : ℕ}
    (hne : left ≠ right) :
    0 < mol.bondOrder left right ↔
      ∃ bond ∈ mol.bonds, bond.connects left right = true := by
  unfold bondOrder directedBondOrder
  simp only [hne, ↓reduceIte, lt_max_iff,
    foldDirectedBondOrder_pos_iff, Nat.lt_irrefl, false_or]
  constructor
  · rintro (⟨bond, hbond, hdirected⟩ | ⟨bond, hbond, hdirected⟩)
    · refine ⟨bond, hbond, ?_⟩
      simp only [RawBond.connects, Bool.or_eq_true]
      left
      exact hdirected
    · refine ⟨bond, hbond, ?_⟩
      simp only [RawBond.connects, Bool.or_eq_true]
      right
      exact hdirected
  · rintro ⟨bond, hbond, hconnects⟩
    simp only [RawBond.connects, Bool.or_eq_true] at hconnects
    rcases hconnects with hforward | hreverse
    · exact Or.inl ⟨bond, hbond, hforward⟩
    · exact Or.inr ⟨bond, hbond, hreverse⟩

/-- With one unordered record per molecular edge, the matrix bond order is exactly the kind of its
unique connecting raw record. -/
theorem bondOrder_eq_kind_of_mem_connects (mol : RawMolecule)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    {bond : RawBond} (hbond : bond ∈ mol.bonds)
    {left right : ℕ} (hconnects : bond.connects left right = true) :
    mol.bondOrder left right = bond.kind.order := by
  have hne : left ≠ right := by
    intro heq
    subst right
    have hendpoints := hwellFormed bond hbond
    simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq] at hconnects
    rcases hconnects with h | h
    · exact hendpoints.2.2 (h.1.trans h.2.symm)
    · exact hendpoints.2.2 (h.1.trans h.2.symm)
  have hrecordUnique : ∀ other ∈ mol.bonds,
      other.connects left right = true → other = bond := by
    intro other hother hotherConnects
    exact mol.bond_eq_of_mem_of_connects hunique hother hbond hotherConnects hconnects
  simp only [RawBond.connects, Bool.or_eq_true] at hconnects
  rcases hconnects with hforward | hreverse
  · have hreverseNone : ∀ other ∈ mol.bonds,
        other.directedConnects right left = false := by
      intro other hother
      rw [Bool.eq_false_iff]
      intro hotherReverse
      have hotherConnects : other.connects left right = true := by
        simp [RawBond.connects, RawBond.directedConnects] at hotherReverse ⊢
        exact Or.inr hotherReverse
      have heq := hrecordUnique other hother hotherConnects
      subst other
      simp [RawBond.directedConnects] at hforward hotherReverse
      omega
    unfold bondOrder directedBondOrder
    simp only [hne, ↓reduceIte]
    rw [foldDirectedBondOrder_eq_of_unique mol.bonds bond left right hbond hforward,
      foldDirectedBondOrder_eq_zero mol.bonds right left hreverseNone]
    simp
    intro other hother hotherDirected
    apply hrecordUnique other hother
    simp [RawBond.connects, RawBond.directedConnects] at hotherDirected ⊢
    exact Or.inl hotherDirected
  · have hforwardNone : ∀ other ∈ mol.bonds,
        other.directedConnects left right = false := by
      intro other hother
      rw [Bool.eq_false_iff]
      intro hotherForward
      have hotherConnects : other.connects left right = true := by
        simp [RawBond.connects, RawBond.directedConnects] at hotherForward ⊢
        exact Or.inl hotherForward
      have heq := hrecordUnique other hother hotherConnects
      subst other
      simp [RawBond.directedConnects] at hreverse hotherForward
      omega
    unfold bondOrder directedBondOrder
    simp only [hne, ↓reduceIte]
    rw [foldDirectedBondOrder_eq_zero mol.bonds left right hforwardNone,
      foldDirectedBondOrder_eq_of_unique mol.bonds bond right left hbond hreverse]
    simp
    intro other hother hotherDirected
    apply hrecordUnique other hother
    simp [RawBond.connects, RawBond.directedConnects] at hotherDirected ⊢
    exact Or.inr hotherDirected

/-- Under the graph-realization hypotheses, a double entry in the bond matrix comes from one
unique written double-bond record. -/
theorem bondOrder_eq_two_iff_exists_double_record (mol : RawMolecule)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    {left right : ℕ} (hne : left ≠ right) :
    mol.bondOrder left right = 2 ↔
      ∃ bond ∈ mol.bonds,
        bond.connects left right = true ∧ bond.kind.order = 2 := by
  constructor
  · intro horder
    have hpositive : 0 < mol.bondOrder left right := by rw [horder]; decide
    obtain ⟨bond, hbond, hconnects⟩ :=
      (mol.bondOrder_pos_iff_exists_bond hne).1 hpositive
    refine ⟨bond, hbond, hconnects, ?_⟩
    rw [← mol.bondOrder_eq_kind_of_mem_connects hwellFormed hunique hbond hconnects]
    exact horder
  · rintro ⟨bond, hbond, hconnects, hkind⟩
    rw [mol.bondOrder_eq_kind_of_mem_connects hwellFormed hunique hbond hconnects,
      hkind]

private def RawDoubleIncidentAt (atom : ℕ) (bond : RawBond) : Prop :=
  bond.kind.order = 2 ∧ (bond.source = atom ∨ bond.target = atom)

private instance (atom : ℕ) (bond : RawBond) :
    Decidable (RawDoubleIncidentAt atom bond) := by
  unfold RawDoubleIncidentAt
  infer_instance

private def doubleIncidentOther (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (atom : Fin mol.atomCount)
    (entry : {index : Fin mol.bonds.length //
      RawDoubleIncidentAt atom (mol.bonds.get index)}) : Fin mol.atomCount := by
  let bond := mol.bonds.get entry.1
  have hbond : bond ∈ mol.bonds := List.get_mem _ _
  have hendpoints := hwellFormed bond hbond
  exact if hsource : bond.source = atom then ⟨bond.target, hendpoints.2.1⟩
    else ⟨bond.source, hendpoints.1⟩

private theorem doubleIncidentOther_connects (mol : RawMolecule)
    (hwellFormed : mol.WellFormed) (atom : Fin mol.atomCount)
    (entry : {index : Fin mol.bonds.length //
      RawDoubleIncidentAt atom (mol.bonds.get index)}) :
    (mol.bonds.get entry.1).connects atom
      (doubleIncidentOther mol hwellFormed atom entry) = true := by
  simp only [doubleIncidentOther]
  split <;> rename_i hsource
  · simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq]
    exact Or.inl ⟨hsource, trivial⟩
  · have htarget : (mol.bonds.get entry.1).target = atom := by
      exact entry.2.2.resolve_left hsource
    simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq]
    exact Or.inr ⟨trivial, htarget⟩

private theorem doubleIncidentOther_bondOrder (mol : RawMolecule)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (atom : Fin mol.atomCount)
    (entry : {index : Fin mol.bonds.length //
      RawDoubleIncidentAt atom (mol.bonds.get index)}) :
    mol.toMoleculeGraph.bond atom (doubleIncidentOther mol hwellFormed atom entry) = 2 := by
  change mol.bondOrder atom (doubleIncidentOther mol hwellFormed atom entry) = 2
  rw [mol.bondOrder_eq_kind_of_mem_connects hwellFormed hunique
    (List.get_mem mol.bonds entry.1)
    (doubleIncidentOther_connects mol hwellFormed atom entry)]
  exact entry.2.1

private def doubleIncidentNeighbor (mol : RawMolecule)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (atom : Fin mol.atomCount)
    (entry : {index : Fin mol.bonds.length //
      RawDoubleIncidentAt atom (mol.bonds.get index)}) :
    {other : Fin mol.atomCount // mol.toMoleculeGraph.bond atom other = 2} :=
  ⟨doubleIncidentOther mol hwellFormed atom entry,
    doubleIncidentOther_bondOrder mol hwellFormed hunique atom entry⟩

private theorem doubleIncidentOther_injective (mol : RawMolecule)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (atom : Fin mol.atomCount) :
    Function.Injective (doubleIncidentNeighbor mol hwellFormed hunique atom) := by
  intro first second heq
  have hfirstConnects := doubleIncidentOther_connects mol hwellFormed atom first
  have hsecondConnects := doubleIncidentOther_connects mol hwellFormed atom second
  have hother : doubleIncidentOther mol hwellFormed atom first =
      doubleIncidentOther mol hwellFormed atom second := congrArg Subtype.val heq
  rw [hother] at hfirstConnects
  have hbond : mol.bonds.get first.1 = mol.bonds.get second.1 :=
    mol.bond_eq_of_mem_of_connects hunique
      (List.get_mem mol.bonds first.1) (List.get_mem mol.bonds second.1)
      hfirstConnects hsecondConnects
  have hindex : first.1 = second.1 := by
    let firstMapped : Fin (mol.bonds.map RawBond.edgeKey).length :=
      ⟨first.1, by simp⟩
    let secondMapped : Fin (mol.bonds.map RawBond.edgeKey).length :=
      ⟨second.1, by simp⟩
    have hmapped : firstMapped = secondMapped := by
      apply hunique.injective_get
      simpa [firstMapped, secondMapped] using congrArg RawBond.edgeKey hbond
    apply Fin.ext
    exact congrArg
      (fun index : Fin (mol.bonds.map RawBond.edgeKey).length => index.val) hmapped
  exact Subtype.ext hindex

private theorem doubleIncidentOther_surjective (mol : RawMolecule)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (atom : Fin mol.atomCount) :
    Function.Surjective
      (doubleIncidentNeighbor mol hwellFormed hunique atom) := by
  intro other
  have hne : atom.val ≠ other.1.val := by
    intro heq
    have hself := mol.toMoleculeGraph.bond_self atom
    have hother := other.2
    have hfin : atom = other.1 := Fin.ext heq
    have hzero : mol.toMoleculeGraph.bond atom other.1 = 0 := by
      simpa [← hfin] using hself
    have : (0 : ℕ) = 2 := hzero.symm.trans hother
    omega
  obtain ⟨bond, hbond, hconnects, hkind⟩ :=
    (mol.bondOrder_eq_two_iff_exists_double_record hwellFormed hunique hne).1 other.2
  obtain ⟨index, hindex⟩ := List.get_of_mem hbond
  subst bond
  have hincident : RawDoubleIncidentAt atom (mol.bonds.get index) := by
    refine ⟨hkind, ?_⟩
    simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq] at hconnects
    rcases hconnects with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2
  let entry : {index : Fin mol.bonds.length //
      RawDoubleIncidentAt atom (mol.bonds.get index)} := ⟨index, hincident⟩
  refine ⟨entry, ?_⟩
  apply Subtype.ext
  simp only [doubleIncidentNeighbor]
  apply Fin.ext
  simp only [doubleIncidentOther]
  dsimp only [entry]
  split <;> rename_i hsource
  · have hsourceBond : (mol.bonds.get index).source = atom := hsource
    simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq] at hconnects
    rcases hconnects with h | h
    · exact h.2
    · exact (hne (hsourceBond.symm.trans h.1)).elim
  · have hsourceBond : (mol.bonds.get index).source ≠ atom := hsource
    simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq] at hconnects
    rcases hconnects with h | h
    · exact (hsourceBond h.1).elim
    · exact h.1

private noncomputable def doubleIncidentEquiv (mol : RawMolecule)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (atom : Fin mol.atomCount) :
    {index : Fin mol.bonds.length // RawDoubleIncidentAt atom (mol.bonds.get index)} ≃
      {other : Fin mol.atomCount // mol.toMoleculeGraph.bond atom other = 2} :=
  Equiv.ofBijective (doubleIncidentNeighbor mol hwellFormed hunique atom)
    ⟨doubleIncidentOther_injective mol hwellFormed hunique atom,
      doubleIncidentOther_surjective mol hwellFormed hunique atom⟩

/-- Raw record counting and finite-neighbour counting give the same written-double incidence at
every parsed atom.  This is the cardinality bridge on which localized vertex eligibility rests. -/
theorem incidentDoubleBondCount_eq_toMoleculeGraph (mol : RawMolecule)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (atom : Fin mol.atomCount) :
    mol.incidentDoubleBondCount atom =
      mol.toMoleculeGraph.incidentDoubleBondCount atom := by
  calc
    mol.incidentDoubleBondCount atom =
        mol.bonds.countP (fun bond => decide (RawDoubleIncidentAt atom bond)) := by
      unfold RawMolecule.incidentDoubleBondCount
      rw [List.countP_eq_length_filter]
      congr 2
      funext bond
      apply Bool.eq_iff_iff.mpr
      simp [RawDoubleIncidentAt]
    _ = Nat.card {index : Fin mol.bonds.length //
          RawDoubleIncidentAt atom (mol.bonds.get index)} :=
      (card_fin_subtype_eq_countP mol.bonds (RawDoubleIncidentAt atom)).symm
    _ = Nat.card {other : Fin mol.atomCount //
          mol.toMoleculeGraph.bond atom other = 2} :=
      Nat.card_congr (doubleIncidentEquiv mol hwellFormed hunique atom)
    _ = mol.toMoleculeGraph.incidentDoubleBondCount atom := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rfl

private theorem listGet?_eq_some_get {alpha : Type*} (values : List alpha)
    (index : Fin values.length) :
    listGet? values index = some (values.get index) := by
  induction values with
  | nil => exact Fin.elim0 index
  | cons value values inductionHypothesis =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · rfl
      · simpa [listGet?] using inductionHypothesis tail

/-- The production Boolean vertex test is exactly the independent localized-mancude vertex
predicate on the raw (non-oxido-demoted) molecule graph. -/
theorem localizedMancudeVertex_eq_true_iff (mol : RawMolecule)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (atom : Fin mol.atomCount) :
    mol.localizedMancudeVertex atom = true ↔
      mol.toMoleculeGraph.LocalizedMancudeVertex atom := by
  have hcount := mol.incidentDoubleBondCount_eq_toMoleculeGraph
    hwellFormed hunique atom
  have hatom : mol.atomAt? atom = some (mol.atoms.get atom) := by
    exact listGet?_eq_some_get mol.atoms atom
  unfold RawMolecule.localizedMancudeVertex MoleculeGraph.LocalizedMancudeVertex
  rw [hatom]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    RawMolecule.toMoleculeGraph]
  rw [hcount]
  simp
  change (mol.toMoleculeGraph.incidentDoubleBondCount atom = 1 ∨
      (mol.toMoleculeGraph.incidentDoubleBondCount atom = 0 ∧
        mol.toMoleculeGraph.formalCharge atom < 0)) ↔ _
  rfl

/-- Occurrence-sensitive candidate-edge realization.  The production list retains the written
orientation of its unique raw bond record; the independent predicate is undirected. -/
theorem pair_mem_localizedMancudeCandidateEdges_iff (mol : RawMolecule)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (left right : Fin mol.atomCount) :
    (left.val, right.val) ∈ mol.localizedMancudeCandidateEdges ↔
      ∃ bond ∈ mol.bonds,
        bond.source = left.val ∧ bond.target = right.val ∧
          mol.toMoleculeGraph.MancudeCandidateEdge left right := by
  unfold RawMolecule.localizedMancudeCandidateEdges
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨bond, hbond, hmap⟩
    let condition := (bond.kind.order == 1 || bond.kind.order == 2) &&
      mol.localizedMancudeVertex bond.source && mol.localizedMancudeVertex bond.target
    by_cases hcondition : condition = true
    · have hpair : (bond.source, bond.target) = (left.val, right.val) := by
        have hmap' : some (bond.source, bond.target) = some (left.val, right.val) := by
          simpa [condition, hcondition] using hmap
        exact Option.some.inj hmap'
      have hsource : bond.source = left.val := congrArg Prod.fst hpair
      have htarget : bond.target = right.val := congrArg Prod.snd hpair
      have hparts :
          (bond.kind.order = 1 ∨ bond.kind.order = 2) ∧
            mol.localizedMancudeVertex bond.source = true ∧
            mol.localizedMancudeVertex bond.target = true := by
        simpa [condition, and_assoc] using hcondition
      refine ⟨bond, hbond, hsource, htarget, ?_⟩
      unfold MoleculeGraph.MancudeCandidateEdge
      have hconnects : bond.connects left right = true := by
        simp [RawBond.connects, hsource, htarget]
      have horder := mol.bondOrder_eq_kind_of_mem_connects
        hwellFormed hunique hbond hconnects
      change (mol.bondOrder left right = 1 ∨ mol.bondOrder left right = 2) ∧ _
      have hmatrixOrder : mol.bondOrder left right = 1 ∨
          mol.bondOrder left right = 2 := by
        rw [horder]
        exact hparts.1
      refine ⟨hmatrixOrder, ?_, ?_⟩
      · exact (mol.localizedMancudeVertex_eq_true_iff
          hwellFormed hunique left).1 (by simpa [hsource] using hparts.2.1)
      · exact (mol.localizedMancudeVertex_eq_true_iff
          hwellFormed hunique right).1 (by simpa [htarget] using hparts.2.2)
    · simp [condition, hcondition] at hmap
  · rintro ⟨bond, hbond, hsource, htarget, hcandidate⟩
    refine ⟨bond, hbond, ?_⟩
    unfold MoleculeGraph.MancudeCandidateEdge at hcandidate
    have hconnects : bond.connects left right = true := by
      simp [RawBond.connects, hsource, htarget]
    have horder := mol.bondOrder_eq_kind_of_mem_connects
      hwellFormed hunique hbond hconnects
    have hkind : bond.kind.order = 1 ∨ bond.kind.order = 2 := by
      have hmatrixOrder : mol.bondOrder left right = 1 ∨
          mol.bondOrder left right = 2 := hcandidate.1
      rw [horder] at hmatrixOrder
      exact hmatrixOrder
    have hleft := (mol.localizedMancudeVertex_eq_true_iff
      hwellFormed hunique left).2 hcandidate.2.1
    have hright := (mol.localizedMancudeVertex_eq_true_iff
      hwellFormed hunique right).2 hcandidate.2.2
    simp [hkind, hleft, hright, hsource, htarget]

private theorem containsUndirectedEdge_eq_true_iff_mem (edges : List (ℕ × ℕ))
    (left right : ℕ) :
    containsUndirectedEdge edges left right = true ↔
      (left, right) ∈ edges ∨ (right, left) ∈ edges := by
  simp only [containsUndirectedEdge, List.any_eq_true, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨edge, hedge, hforward | hreverse⟩
    · left
      have hedgeEq : edge = (left, right) := Prod.ext hforward.1 hforward.2
      simpa [hedgeEq] using hedge
    · right
      have hedgeEq : edge = (right, left) := Prod.ext hreverse.1 hreverse.2
      simpa [hedgeEq] using hedge
  · rintro (hforward | hreverse)
    · exact ⟨(left, right), hforward, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨(right, left), hreverse, Or.inr ⟨rfl, rfl⟩⟩

/-- Orientation-free candidate-edge realization, matching the production membership test used by
the mancude labeler. -/
theorem containsUndirectedEdge_localizedMancudeCandidateEdges_iff
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (left right : Fin mol.atomCount) :
    containsUndirectedEdge mol.localizedMancudeCandidateEdges left right = true ↔
      mol.toMoleculeGraph.MancudeCandidateEdge left right := by
  rw [containsUndirectedEdge_eq_true_iff_mem]
  constructor
  · rintro (hforward | hreverse)
    · obtain ⟨_, _, _, _, hcandidate⟩ :=
        (mol.pair_mem_localizedMancudeCandidateEdges_iff
          hwellFormed hunique left right).1 hforward
      exact hcandidate
    · obtain ⟨_, _, _, _, hcandidate⟩ :=
        (mol.pair_mem_localizedMancudeCandidateEdges_iff
          hwellFormed hunique right left).1 hreverse
      exact (mol.toMoleculeGraph.mancudeCandidateEdge_symm).2 hcandidate
  · intro hcandidate
    have hne : left.val ≠ right.val := by
      intro heq
      have hfin : left = right := Fin.ext heq
      have hzero : mol.toMoleculeGraph.bond left right = 0 := by
        simpa [hfin] using mol.toMoleculeGraph.bond_self left
      rcases hcandidate.1 with h | h
      · rw [hzero] at h
        contradiction
      · rw [hzero] at h
        contradiction
    have hpositive : 0 < mol.bondOrder left right := by
      rcases hcandidate.1 with h | h
      · change mol.bondOrder left right = 1 at h
        rw [h]
        decide
      · change mol.bondOrder left right = 2 at h
        rw [h]
        decide
    obtain ⟨bond, hbond, hconnects⟩ :=
      (mol.bondOrder_pos_iff_exists_bond hne).1 hpositive
    simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq] at hconnects
    rcases hconnects with hforward | hreverse
    · left
      exact (mol.pair_mem_localizedMancudeCandidateEdges_iff
        hwellFormed hunique left right).2
          ⟨bond, hbond, hforward.1, hforward.2, hcandidate⟩
    · right
      exact (mol.pair_mem_localizedMancudeCandidateEdges_iff
        hwellFormed hunique right left).2
          ⟨bond, hbond, hreverse.1, hreverse.2,
            (mol.toMoleculeGraph.mancudeCandidateEdge_symm).1 hcandidate⟩

private def candidateRecord? (mol : RawMolecule) (bond : RawBond) : Option (ℕ × ℕ) :=
  if (bond.kind.order == 1 || bond.kind.order == 2) &&
      mol.localizedMancudeVertex bond.source && mol.localizedMancudeVertex bond.target then
    some (bond.source, bond.target)
  else none

private theorem localizedMancudeCandidateEdges_eq_filterMap (mol : RawMolecule) :
    mol.localizedMancudeCandidateEdges = mol.bonds.filterMap mol.candidateRecord? :=
  rfl

private theorem filterMap_attach_val {alpha beta : Type*} (values : List alpha)
    (f : alpha → Option beta) :
    values.attach.filterMap (fun value => f value.1) = values.filterMap f := by
  calc
    values.attach.filterMap (fun value => f value.1) =
        (values.attach.map Subtype.val).filterMap f := by
      rw [List.filterMap_map]
      rfl
    _ = values.filterMap f := by
      have hmap : values.attach.map Subtype.val = values := by
        simp
      rw [hmap]

/-- Candidate edges retain one occurrence per unordered raw bond record. -/
theorem localizedMancudeCandidateEdges_nodup (mol : RawMolecule)
    (hunique : mol.BondRecordsUnique) :
    mol.localizedMancudeCandidateEdges.Nodup := by
  have hbonds : mol.bonds.Nodup := hunique.of_map RawBond.edgeKey
  let attachedCandidate : {bond // bond ∈ mol.bonds} → Option (ℕ × ℕ) :=
    fun bond => mol.candidateRecord? bond.1
  have hattached : mol.bonds.attach.Nodup := hbonds.attach
  have hfiltered : (mol.bonds.attach.filterMap attachedCandidate).Nodup := by
    apply hattached.filterMap
    intro first second edge hfirst hsecond
    have hfirstMap : mol.candidateRecord? first.1 = some edge := by simpa using hfirst
    have hsecondMap : mol.candidateRecord? second.1 = some edge := by simpa using hsecond
    have hfirstPair : (first.1.source, first.1.target) = edge := by
      unfold candidateRecord? at hfirstMap
      split at hfirstMap <;> simp_all
    have hsecondPair : (second.1.source, second.1.target) = edge := by
      unfold candidateRecord? at hsecondMap
      split at hsecondMap <;> simp_all
    have hsource : second.1.source = first.1.source := by
      exact congrArg Prod.fst (hsecondPair.trans hfirstPair.symm)
    have htarget : second.1.target = first.1.target := by
      exact congrArg Prod.snd (hsecondPair.trans hfirstPair.symm)
    apply Subtype.ext
    apply mol.bond_eq_of_mem_of_connects hunique first.2 second.2
      (left := first.1.source) (right := first.1.target)
    · simp [RawBond.connects]
    · simp [RawBond.connects, hsource, htarget]
  rw [localizedMancudeCandidateEdges_eq_filterMap,
    ← filterMap_attach_val mol.bonds mol.candidateRecord?]
  exact hfiltered

/-- Bridge removal is a list filter, so the production localized-edge list is duplicate-free. -/
theorem localizedMancudeEdges_nodup (mol : RawMolecule)
    (hunique : mol.BondRecordsUnique) :
    mol.localizedMancudeEdges.Nodup := by
  unfold localizedMancudeEdges
  exact (mol.localizedMancudeCandidateEdges_nodup hunique).filter _

private theorem endpoints_lt_of_mem_localizedMancudeCandidateEdges
    (mol : RawMolecule) (hwellFormed : mol.WellFormed) {edge : ℕ × ℕ}
    (hedge : edge ∈ mol.localizedMancudeCandidateEdges) :
    edge.1 < mol.atomCount ∧ edge.2 < mol.atomCount := by
  unfold localizedMancudeCandidateEdges at hedge
  rw [List.mem_filterMap] at hedge
  obtain ⟨bond, hbond, houtput⟩ := hedge
  by_cases hcondition :
      ((bond.kind.order == 1 || bond.kind.order == 2) &&
        mol.localizedMancudeVertex bond.source &&
        mol.localizedMancudeVertex bond.target) = true
  · have hedgeEq : (bond.source, bond.target) = edge := by
      have : some (bond.source, bond.target) = some edge := by
        simpa [hcondition] using houtput
      exact Option.some.inj this
    have hendpoints := hwellFormed bond hbond
    have hbounds : bond.source < mol.atomCount ∧ bond.target < mol.atomCount :=
      ⟨hendpoints.1, hendpoints.2.1⟩
    simpa [← hedgeEq] using hbounds
  · simp [hcondition] at houtput

/-- Production localized edges inherit the molecule graph's looplessness. -/
theorem localizedMancudeEdges_noSelf (mol : RawMolecule)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique) :
    ∀ edge ∈ mol.localizedMancudeEdges, edge.1 ≠ edge.2 := by
  intro edge hedge heq
  have hcandidateMem : edge ∈ mol.localizedMancudeCandidateEdges := by
    unfold localizedMancudeEdges at hedge
    exact (List.mem_filter.mp hedge).1
  have hbounds := mol.endpoints_lt_of_mem_localizedMancudeCandidateEdges
    hwellFormed hcandidateMem
  let left : Fin mol.atomCount := ⟨edge.1, hbounds.1⟩
  let right : Fin mol.atomCount := ⟨edge.2, hbounds.2⟩
  obtain ⟨_, _, _, _, hcandidate⟩ :=
    (mol.pair_mem_localizedMancudeCandidateEdges_iff
      hwellFormed hunique left right).1 hcandidateMem
  have hfin : left = right := Fin.ext heq
  have hzero : mol.toMoleculeGraph.bond left right = 0 := by
    simpa [hfin] using mol.toMoleculeGraph.bond_self left
  rcases hcandidate.1 with hbond | hbond
  · rw [hzero] at hbond
    contradiction
  · rw [hzero] at hbond
    contradiction

/-- Bond-record uniqueness rules out storing both orientations of one localized edge. -/
theorem localizedMancudeEdges_undirectedUnique (mol : RawMolecule)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique) :
    ∀ first ∈ mol.localizedMancudeEdges, ∀ second ∈ mol.localizedMancudeEdges,
      (first = second ∨ first = (second.2, second.1)) → first = second := by
  intro first hfirst second hsecond hsame
  rcases hsame with hsame | hreverse
  · exact hsame
  · have hfirstCandidate : first ∈ mol.localizedMancudeCandidateEdges := by
      unfold localizedMancudeEdges at hfirst
      exact (List.mem_filter.mp hfirst).1
    have hsecondCandidate : second ∈ mol.localizedMancudeCandidateEdges := by
      unfold localizedMancudeEdges at hsecond
      exact (List.mem_filter.mp hsecond).1
    have hfirstBounds := mol.endpoints_lt_of_mem_localizedMancudeCandidateEdges
      hwellFormed hfirstCandidate
    have hsecondBounds := mol.endpoints_lt_of_mem_localizedMancudeCandidateEdges
      hwellFormed hsecondCandidate
    let firstLeft : Fin mol.atomCount := ⟨first.1, hfirstBounds.1⟩
    let firstRight : Fin mol.atomCount := ⟨first.2, hfirstBounds.2⟩
    let secondLeft : Fin mol.atomCount := ⟨second.1, hsecondBounds.1⟩
    let secondRight : Fin mol.atomCount := ⟨second.2, hsecondBounds.2⟩
    obtain ⟨firstBond, hfirstBond, hfirstSource, hfirstTarget, _⟩ :=
      (mol.pair_mem_localizedMancudeCandidateEdges_iff
        hwellFormed hunique firstLeft firstRight).1 hfirstCandidate
    obtain ⟨secondBond, hsecondBond, hsecondSource, hsecondTarget, _⟩ :=
      (mol.pair_mem_localizedMancudeCandidateEdges_iff
        hwellFormed hunique secondLeft secondRight).1 hsecondCandidate
    have hsecondSource' : secondBond.source = second.1 := by
      simpa [secondLeft] using hsecondSource
    have hsecondTarget' : secondBond.target = second.2 := by
      simpa [secondRight] using hsecondTarget
    have hfirstConnects : firstBond.connects second.1 second.2 = true := by
      simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      right
      constructor
      · exact hfirstSource.trans (congrArg Prod.fst hreverse)
      · exact hfirstTarget.trans (congrArg Prod.snd hreverse)
    have hsecondConnects : secondBond.connects second.1 second.2 = true := by
      simp [RawBond.connects, hsecondSource', hsecondTarget']
    have hbondEq := mol.bond_eq_of_mem_of_connects hunique hfirstBond hsecondBond
      hfirstConnects hsecondConnects
    have hcross : second.2 = second.1 := by
      calc
        second.2 = firstBond.source :=
          (hfirstSource.trans (congrArg Prod.fst hreverse)).symm
        _ = secondBond.source := congrArg RawBond.source hbondEq
        _ = second.1 := hsecondSource'
    calc
      first = (second.2, second.1) := hreverse
      _ = second := by apply Prod.ext <;> simp [hcross]

private theorem unblockedListEdge_of_mancudeStepWithout
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) {blockedLeft blockedRight left right : Fin mol.atomCount}
    (hstep : mol.toMoleculeGraph.MancudeStepWithout blockedLeft blockedRight left right) :
    UnblockedListEdge (blockedLeft.val, blockedRight.val)
      mol.localizedMancudeCandidateEdges left.val right.val := by
  have hcontains : containsUndirectedEdge mol.localizedMancudeCandidateEdges
      left.val right.val = true :=
    (mol.containsUndirectedEdge_localizedMancudeCandidateEdges_iff
      hwellFormed hunique left right).2 hstep.1
  rw [containsUndirectedEdge_eq_true_iff_mem] at hcontains
  have hunblockedVals : ¬
      ((left.val = blockedLeft.val ∧ right.val = blockedRight.val) ∨
       (left.val = blockedRight.val ∧ right.val = blockedLeft.val)) := by
    intro hblocked
    apply hstep.2
    rcases hblocked with hblocked | hblocked
    · exact Or.inl ⟨Fin.ext hblocked.1, Fin.ext hblocked.2⟩
    · exact Or.inr ⟨Fin.ext hblocked.1, Fin.ext hblocked.2⟩
  rw [unblockedListEdge_iff]
  rcases hcontains with hforward | hreverse
  · exact ⟨(left.val, right.val), hforward, hunblockedVals,
      Or.inl ⟨rfl, rfl⟩⟩
  · refine ⟨(right.val, left.val), hreverse, ?_, Or.inr ⟨rfl, rfl⟩⟩
    intro hblocked
    apply hunblockedVals
    rcases hblocked with hblocked | hblocked
    · exact Or.inr ⟨hblocked.2, hblocked.1⟩
    · exact Or.inl ⟨hblocked.2, hblocked.1⟩

private theorem mancudeStepWithout_swapBlocked {Atom : Type*} [Fintype Atom]
    [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    {blockedLeft blockedRight left right : Atom}
    (hstep : molecule.MancudeStepWithout blockedLeft blockedRight left right) :
    molecule.MancudeStepWithout blockedRight blockedLeft left right := by
  constructor
  · exact hstep.1
  · intro hblocked
    apply hstep.2
    rcases hblocked with hblocked | hblocked
    · exact Or.inr hblocked
    · exact Or.inl hblocked

private theorem mancudeStepWithout_symm {Atom : Type*} [Fintype Atom]
    [DecidableEq Atom] (molecule : MoleculeGraph Atom)
    {blockedLeft blockedRight left right : Atom}
    (hstep : molecule.MancudeStepWithout blockedLeft blockedRight left right) :
    molecule.MancudeStepWithout blockedLeft blockedRight right left := by
  constructor
  · exact (molecule.mancudeCandidateEdge_symm).2 hstep.1
  · intro hblocked
    apply hstep.2
    rcases hblocked with hblocked | hblocked
    · exact Or.inr ⟨hblocked.2, hblocked.1⟩
    · exact Or.inl ⟨hblocked.2, hblocked.1⟩

private theorem reflTransGen_reverse {alpha : Type*} {relation : alpha → alpha → Prop}
    (hsymm : Symmetric relation) {left right : alpha}
    (hpath : Relation.ReflTransGen relation left right) :
    Relation.ReflTransGen relation right left := by
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprefix hstep inductionHypothesis =>
      exact (Relation.ReflTransGen.single (hsymm hstep)).trans inductionHypothesis

private theorem localizedMancudeEdge_reverse {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    {left right : Atom} (hedge : molecule.LocalizedMancudeEdge left right) :
    molecule.LocalizedMancudeEdge right left := by
  refine ⟨(molecule.mancudeCandidateEdge_symm).2 hedge.1, ?_⟩
  have hswap : Relation.ReflTransGen
      (molecule.MancudeStepWithout right left) left right :=
    hedge.2.mono fun _ _ hstep => mancudeStepWithout_swapBlocked molecule hstep
  exact reflTransGen_reverse (fun _ _ hstep =>
    mancudeStepWithout_symm molecule hstep) hswap

private theorem pair_mem_localizedMancudeEdges_of_candidate_of_localized
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (left right : Fin mol.atomCount)
    (hcandidate : (left.val, right.val) ∈ mol.localizedMancudeCandidateEdges)
    (hlocalized : mol.toMoleculeGraph.LocalizedMancudeEdge left right) :
    (left.val, right.val) ∈ mol.localizedMancudeEdges := by
  unfold localizedMancudeEdges
  simp only [List.mem_filter]
  refine ⟨hcandidate, ?_⟩
  have hrawPath : Relation.ReflTransGen
      (UnblockedListEdge (left.val, right.val) mol.localizedMancudeCandidateEdges)
      left.val right.val :=
    hlocalized.2.lift Fin.val fun _ _ hstep =>
      mol.unblockedListEdge_of_mancudeStepWithout hwellFormed hunique hstep
  have hmem := reachableWithoutEdge_complete_of_reflTransGen
    (left.val, right.val) mol.localizedMancudeCandidateEdges hrawPath
  simpa using hmem

/-- Every edge accepted by production's bounded bridge-removal search satisfies the independent
non-bridge reachability definition. -/
theorem localizedMancudeEdge_of_pair_mem_localizedMancudeEdges
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (left right : Fin mol.atomCount)
    (hmem : (left.val, right.val) ∈ mol.localizedMancudeEdges) :
    mol.toMoleculeGraph.LocalizedMancudeEdge left right := by
  unfold localizedMancudeEdges at hmem
  simp only [List.mem_filter] at hmem
  have hcandidate :=
    (mol.pair_mem_localizedMancudeCandidateEdges_iff
      hwellFormed hunique left right).1 hmem.1
  obtain ⟨bond, hbond, hsource, htarget, hcandidateGraph⟩ := hcandidate
  refine ⟨hcandidateGraph, ?_⟩
  have hcontains : right.val ∈
      reachableWithoutEdge (left.val, right.val)
        (mol.localizedMancudeCandidateEdges.length + 1)
        mol.localizedMancudeCandidateEdges [left.val] [left.val] := by
    simpa using hmem.2
  have hraw := reachableWithoutEdge_from_singleton_sound
    (left.val, right.val) (mol.localizedMancudeCandidateEdges.length + 1)
    mol.localizedMancudeCandidateEdges hcontains
  have hconvert : ∀ atom,
      Relation.ReflTransGen
          (UnblockedListEdge (left.val, right.val) mol.localizedMancudeCandidateEdges)
          left.val atom →
        ∃ hbound : atom < mol.atomCount,
          Relation.ReflTransGen
            (mol.toMoleculeGraph.MancudeStepWithout left right)
            left ⟨atom, hbound⟩ := by
    intro atom hpath
    induction hpath with
    | refl => exact ⟨left.isLt, Relation.ReflTransGen.refl⟩
    | @tail parent atom hprefix hstep inductionHypothesis =>
        obtain ⟨hparentBound, hprefixIndependent⟩ := inductionHypothesis
        rw [unblockedListEdge_iff] at hstep
        obtain ⟨edge, hedge, hunblockedEdge, horientation⟩ := hstep
        have hfacts :
            ((parent, atom) ∈ mol.localizedMancudeCandidateEdges ∨
              (atom, parent) ∈ mol.localizedMancudeCandidateEdges) ∧
              ¬ ((parent = left.val ∧ atom = right.val) ∨
                (parent = right.val ∧ atom = left.val)) := by
          constructor
          · rcases horientation with ⟨hsource, htarget⟩ | ⟨htarget, hsource⟩
            · have hedgeEq : edge = (parent, atom) := Prod.ext hsource htarget
              exact Or.inl (by simpa [hedgeEq] using hedge)
            · have hedgeEq : edge = (atom, parent) := Prod.ext hsource htarget
              exact Or.inr (by simpa [hedgeEq] using hedge)
          · rcases horientation with ⟨hsource, htarget⟩ | ⟨htarget, hsource⟩
            · have hedgeEq : edge = (parent, atom) := Prod.ext hsource htarget
              simpa [hedgeEq] using hunblockedEdge
            · have hedgeEq : edge = (atom, parent) := Prod.ext hsource htarget
              intro hblocked
              apply hunblockedEdge
              simp only [hedgeEq]
              rcases hblocked with hblocked | hblocked
              · exact Or.inr ⟨hblocked.2, hblocked.1⟩
              · exact Or.inl ⟨hblocked.2, hblocked.1⟩
        have hatomBound : atom < mol.atomCount := by
          rcases hfacts.1 with hforward | hreverse
          · exact (mol.endpoints_lt_of_mem_localizedMancudeCandidateEdges
              hwellFormed hforward).2
          · exact (mol.endpoints_lt_of_mem_localizedMancudeCandidateEdges
              hwellFormed hreverse).1
        let parentFin : Fin mol.atomCount := ⟨parent, hparentBound⟩
        let atomFin : Fin mol.atomCount := ⟨atom, hatomBound⟩
        have hcandidateStep :
            mol.toMoleculeGraph.MancudeCandidateEdge parentFin atomFin := by
          apply (mol.containsUndirectedEdge_localizedMancudeCandidateEdges_iff
            hwellFormed hunique parentFin atomFin).1
          rw [containsUndirectedEdge_eq_true_iff_mem]
          exact hfacts.1
        have hunblocked : ¬
            ((parentFin = left ∧ atomFin = right) ∨
             (parentFin = right ∧ atomFin = left)) := by
          intro hblocked
          apply hfacts.2
          rcases hblocked with hblocked | hblocked
          · exact Or.inl ⟨congrArg Fin.val hblocked.1, congrArg Fin.val hblocked.2⟩
          · exact Or.inr ⟨congrArg Fin.val hblocked.1, congrArg Fin.val hblocked.2⟩
        refine ⟨hatomBound, ?_⟩
        exact hprefixIndependent.tail ⟨hcandidateStep, hunblocked⟩
  obtain ⟨hrightBound, hindependent⟩ := hconvert right.val hraw
  have hright : (⟨right.val, hrightBound⟩ : Fin mol.atomCount) = right := by
    apply Fin.ext
    rfl
  simpa [hright] using hindependent

/-- Exact orientation-free realization of the production localized mancude edge list.  This
closes both the raw/finite-graph representation boundary and the bounded-search fuel boundary. -/
theorem containsUndirectedEdge_localizedMancudeEdges_iff
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (left right : Fin mol.atomCount) :
    containsUndirectedEdge mol.localizedMancudeEdges left.val right.val = true ↔
      mol.toMoleculeGraph.LocalizedMancudeEdge left right := by
  rw [containsUndirectedEdge_eq_true_iff_mem]
  constructor
  · rintro (hforward | hreverse)
    · exact mol.localizedMancudeEdge_of_pair_mem_localizedMancudeEdges
        hwellFormed hunique left right hforward
    · exact localizedMancudeEdge_reverse mol.toMoleculeGraph
        (mol.localizedMancudeEdge_of_pair_mem_localizedMancudeEdges
          hwellFormed hunique right left hreverse)
  · intro hlocalized
    have hcandidate :
        (left.val, right.val) ∈ mol.localizedMancudeCandidateEdges ∨
          (right.val, left.val) ∈ mol.localizedMancudeCandidateEdges := by
      rw [← containsUndirectedEdge_eq_true_iff_mem]
      exact (mol.containsUndirectedEdge_localizedMancudeCandidateEdges_iff
        hwellFormed hunique left right).2 hlocalized.1
    rcases hcandidate with hforward | hreverse
    · exact Or.inl (mol.pair_mem_localizedMancudeEdges_of_candidate_of_localized
        hwellFormed hunique left right hforward hlocalized)
    · exact Or.inr (mol.pair_mem_localizedMancudeEdges_of_candidate_of_localized
        hwellFormed hunique right left hreverse
          (localizedMancudeEdge_reverse mol.toMoleculeGraph hlocalized))

private theorem edgeComponent_eq_reachableWithoutEdge_sentinel
    (edges : List (ℕ × ℕ)) (bound : ℕ)
    (hbounded : ∀ edge ∈ edges, edge.1 < bound ∧ edge.2 < bound) :
    ∀ fuel frontier seen,
      edgeComponent edges fuel frontier seen =
        reachableWithoutEdge (bound, bound) fuel edges frontier seen := by
  intro fuel
  induction fuel with
  | zero => intro frontier seen; rfl
  | succ fuel inductionHypothesis =>
      intro frontier seen
      cases frontier with
      | nil => rfl
      | cons first rest =>
          have hfilterMap : ∀ atom,
              edges.filterMap (fun edge =>
                let isBlocked :=
                  (edge.1 == bound && edge.2 == bound) ||
                    (edge.1 == bound && edge.2 == bound)
                if isBlocked then none
                else if edge.1 == atom then some edge.2
                else if edge.2 == atom then some edge.1
                else none) =
                edges.filterMap (fun edge =>
                  if edge.1 == atom then some edge.2
                  else if edge.2 == atom then some edge.1
                  else none) := by
            intro atom
            apply List.filterMap_congr
            intro edge hedge
            have hne : edge.1 ≠ bound := Nat.ne_of_lt (hbounded edge hedge).1
            simp [hne]
          have hnext :
              (List.flatMap
                (fun atom => edges.filterMap fun edge =>
                  let isBlocked :=
                    (edge.1 == bound && edge.2 == bound) ||
                      (edge.1 == bound && edge.2 == bound)
                  if isBlocked then none
                  else if edge.1 == atom then some edge.2
                  else if edge.2 == atom then some edge.1
                  else none) (first :: rest)).filter
                    (fun atom => !seen.contains atom) =
              (List.flatMap
                (fun atom => edges.filterMap fun edge =>
                  if edge.1 == atom then some edge.2
                  else if edge.2 == atom then some edge.1
                  else none) (first :: rest)).filter
                    (fun atom => !seen.contains atom) := by
            congr 1
            apply List.flatMap_congr
            intro atom _
            exact hfilterMap atom
          simp only [edgeComponent, reachableWithoutEdge]
          rw [hnext]
          exact inductionHypothesis _ _

theorem endpoints_lt_of_mem_localizedMancudeEdges
    (mol : RawMolecule) (hwellFormed : mol.WellFormed) {edge : ℕ × ℕ}
    (hedge : edge ∈ mol.localizedMancudeEdges) :
    edge.1 < mol.atomCount ∧ edge.2 < mol.atomCount := by
  unfold localizedMancudeEdges at hedge
  exact mol.endpoints_lt_of_mem_localizedMancudeCandidateEdges
    hwellFormed (List.mem_filter.mp hedge).1

private theorem unblockedSentinelEdge_of_localizedMancudeEdge
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) {left right : Fin mol.atomCount}
    (hstep : mol.toMoleculeGraph.LocalizedMancudeEdge left right) :
    UnblockedListEdge (mol.atomCount, mol.atomCount)
      mol.localizedMancudeEdges left.val right.val := by
  have hcontains : containsUndirectedEdge mol.localizedMancudeEdges
      left.val right.val = true :=
    (mol.containsUndirectedEdge_localizedMancudeEdges_iff
      hwellFormed hunique left right).2 hstep
  rw [containsUndirectedEdge_eq_true_iff_mem] at hcontains
  rw [unblockedListEdge_iff]
  rcases hcontains with hforward | hreverse
  · refine ⟨(left.val, right.val), hforward, ?_, Or.inl ⟨rfl, rfl⟩⟩
    have hleft : left.val ≠ mol.atomCount := Nat.ne_of_lt left.isLt
    simp [hleft]
  · refine ⟨(right.val, left.val), hreverse, ?_, Or.inr ⟨rfl, rfl⟩⟩
    have hright : right.val ≠ mol.atomCount := Nat.ne_of_lt right.isLt
    simp [hright]

/-- Exact realization of the production component traversal as declarative connectivity in the
localized mancude graph.  The traversal fuel is justified by the finite-edge simple-path bound. -/
theorem mem_edgeComponent_localizedMancudeEdges_iff
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached atom : Fin mol.atomCount) :
    atom.val ∈ edgeComponent mol.localizedMancudeEdges
        (mol.localizedMancudeEdges.length + 1) [attached.val] [attached.val] ↔
      mol.toMoleculeGraph.InMancudeComponent attached atom := by
  have hbounded : ∀ edge ∈ mol.localizedMancudeEdges,
      edge.1 < mol.atomCount ∧ edge.2 < mol.atomCount :=
    fun edge hedge => mol.endpoints_lt_of_mem_localizedMancudeEdges hwellFormed hedge
  rw [edgeComponent_eq_reachableWithoutEdge_sentinel
    mol.localizedMancudeEdges mol.atomCount hbounded]
  constructor
  · intro hmem
    have hraw : Relation.ReflTransGen
        (UnblockedListEdge (mol.atomCount, mol.atomCount) mol.localizedMancudeEdges)
        attached.val atom.val := by
      apply reachableWithoutEdge_sound (mol.atomCount, mol.atomCount)
        mol.localizedMancudeEdges attached.val
        (mol.localizedMancudeEdges.length + 1) [attached.val] [attached.val]
      · intro current hcurrent
        simp only [List.mem_singleton] at hcurrent
        subst current
        exact Relation.ReflTransGen.refl
      · intro current hcurrent
        simp only [List.mem_singleton] at hcurrent
        subst current
        exact Relation.ReflTransGen.refl
      · exact hmem
    have hconvert : ∀ current,
        Relation.ReflTransGen
            (UnblockedListEdge (mol.atomCount, mol.atomCount) mol.localizedMancudeEdges)
            attached.val current →
          ∃ hcurrent : current < mol.atomCount,
            Relation.ReflTransGen mol.toMoleculeGraph.LocalizedMancudeEdge
              attached ⟨current, hcurrent⟩ := by
      intro current hpath
      induction hpath with
      | refl => exact ⟨attached.isLt, Relation.ReflTransGen.refl⟩
      | @tail parent current hprefix hstep inductionHypothesis =>
          obtain ⟨hparentBound, hprefixIndependent⟩ := inductionHypothesis
          rw [unblockedListEdge_iff] at hstep
          obtain ⟨edge, hedge, _, horientation⟩ := hstep
          have hedgeMembership :
              (parent, current) ∈ mol.localizedMancudeEdges ∨
                (current, parent) ∈ mol.localizedMancudeEdges := by
            rcases horientation with ⟨hsource, htarget⟩ | ⟨htarget, hsource⟩
            · have hedgeEq : edge = (parent, current) := Prod.ext hsource htarget
              exact Or.inl (by simpa [hedgeEq] using hedge)
            · have hedgeEq : edge = (current, parent) := Prod.ext hsource htarget
              exact Or.inr (by simpa [hedgeEq] using hedge)
          have hcurrentBound : current < mol.atomCount := by
            rcases hedgeMembership with hforward | hreverse
            · exact (mol.endpoints_lt_of_mem_localizedMancudeEdges
                hwellFormed hforward).2
            · exact (mol.endpoints_lt_of_mem_localizedMancudeEdges
                hwellFormed hreverse).1
          let parentFin : Fin mol.atomCount := ⟨parent, hparentBound⟩
          let currentFin : Fin mol.atomCount := ⟨current, hcurrentBound⟩
          have hlocalized :
              mol.toMoleculeGraph.LocalizedMancudeEdge parentFin currentFin := by
            apply (mol.containsUndirectedEdge_localizedMancudeEdges_iff
              hwellFormed hunique parentFin currentFin).1
            rw [containsUndirectedEdge_eq_true_iff_mem]
            exact hedgeMembership
          exact ⟨hcurrentBound, hprefixIndependent.tail hlocalized⟩
    obtain ⟨hatomBound, hindependent⟩ := hconvert atom.val hraw
    have hatom : (⟨atom.val, hatomBound⟩ : Fin mol.atomCount) = atom := Fin.ext rfl
    simpa [MoleculeGraph.InMancudeComponent, hatom] using hindependent
  · intro hcomponent
    have hraw : Relation.ReflTransGen
        (UnblockedListEdge (mol.atomCount, mol.atomCount) mol.localizedMancudeEdges)
        attached.val atom.val := by
      exact hcomponent.lift Fin.val fun _ _ hstep =>
        mol.unblockedSentinelEdge_of_localizedMancudeEdge hwellFormed hunique hstep
    exact reachableWithoutEdge_complete_from_start_of_reflTransGen
      (mol.atomCount, mol.atomCount) mol.localizedMancudeEdges attached.val hraw

end RawMolecule

end
end OneCenter
end TetraStereo
