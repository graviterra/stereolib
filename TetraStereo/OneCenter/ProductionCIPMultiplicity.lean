import TetraStereo.OneCenter.ProductionCIPHistoryBridge

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace RawMolecule

private def copiesFromBond (mol : RawMolecule) (node : CanonicalBranchNode)
    (bond : RawBond) : List (ℕ × ℕ) :=
    let next? :=
      if bond.source == node.atom then some bond.target
      else if bond.target == node.atom then some bond.source
      else none
    match next? with
    | none => []
    | some next =>
        (List.range (mol.canonicalBondOrder node next)).map fun copyIndex =>
          (next, copyIndex)

private def childCopySeeds (mol : RawMolecule) (node : CanonicalBranchNode) :
    List (ℕ × ℕ) :=
  mol.bonds.flatMap (copiesFromBond mol node)

private def nodeFromCopy (node : CanonicalBranchNode) (copy : ℕ × ℕ) :
    CanonicalBranchNode :=
  let provenance :=
    if copy.2 != 0 then
      CanonicalNodeProvenance.multipleBondDuplicate node.depth
    else if node.history.contains copy.1 then
      CanonicalNodeProvenance.ringDuplicate (canonicalHistoryDistance node copy.1)
    else CanonicalNodeProvenance.realAtom
  { atom := copy.1, parent := node.atom, history := copy.1 :: node.history,
    provenance := provenance }

private theorem canonicalChildCopies_eq (mol : RawMolecule)
    (node : CanonicalBranchNode) :
    mol.canonicalChildCopies node =
      eraseCanonicalParentCopy node.parent (childCopySeeds mol node) :=
  rfl

private theorem edgeKey_eq_of_connects (bond : RawBond) (left right : ℕ)
    (hconnects : bond.connects left right = true) :
    RawBond.edgeKey bond = (min left right, max left right) := by
  simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at hconnects
  rcases hconnects with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · simp [RawBond.edgeKey, hsource, htarget]
  · simp [RawBond.edgeKey, hsource, htarget, min_comm, max_comm]

private theorem incident_record_count_le_one (mol : RawMolecule)
    (hunique : mol.BondRecordsUnique) (left right : ℕ) :
    mol.bonds.countP (fun bond => bond.connects left right) ≤ 1 := by
  let key := (min left right, max left right)
  have hcount : mol.bonds.countP (fun bond => bond.connects left right) ≤
      (mol.bonds.map RawBond.edgeKey).count key := by
    induction mol.bonds with
    | nil => simp
    | cons bond bonds inductionHypothesis =>
        simp only [List.countP_cons, List.map_cons, List.count_cons]
        by_cases hconnects : bond.connects left right = true
        · have hkey : RawBond.edgeKey bond = key :=
            edgeKey_eq_of_connects bond left right hconnects
          simp [hconnects, hkey]
          omega
        · by_cases hkey : RawBond.edgeKey bond = key
          · simp [hconnects, hkey]
            omega
          · simp [hconnects, hkey]
            omega
  exact hcount.trans ((List.nodup_iff_count_le_one.mp hunique) key)

private theorem parsedBondKind_order_pos (kind : ParsedBondKind) :
    0 < kind.order := by
  cases kind <;> decide

private theorem directedBondOrder_pos_iff (mol : RawMolecule) (left right : ℕ) :
    0 < mol.directedBondOrder left right ↔
      ∃ bond ∈ mol.bonds, bond.directedConnects left right = true := by
  unfold directedBondOrder
  have foldLemma : ∀ (bonds : List RawBond) (accumulator : ℕ),
      0 < bonds.foldl
          (fun order bond =>
            if bond.directedConnects left right then max order bond.kind.order else order)
          accumulator ↔
        0 < accumulator ∨
          ∃ bond ∈ bonds, bond.directedConnects left right = true := by
    intro bonds
    induction bonds with
    | nil => intro accumulator; simp
    | cons bond bonds inductionHypothesis =>
        intro accumulator
        simp only [List.foldl_cons]
        rw [inductionHypothesis]
        by_cases hconnects : bond.directedConnects left right = true
        · simp [hconnects, parsedBondKind_order_pos bond.kind]
        · simp [hconnects]
  rw [foldLemma]
  simp

private theorem bondOrder_pos_iff (mol : RawMolecule) (left right : ℕ)
    (hne : left ≠ right) :
    0 < mol.bondOrder left right ↔
      ∃ bond ∈ mol.bonds, bond.connects left right = true := by
  unfold bondOrder
  simp only [hne, ↓reduceIte]
  have hmax : ∀ first second : ℕ,
      0 < max first second ↔ 0 < first ∨ 0 < second := by omega
  rw [hmax]
  rw [mol.directedBondOrder_pos_iff left right,
    mol.directedBondOrder_pos_iff right left]
  simp only [RawBond.connects, RawBond.directedConnects, Bool.or_eq_true]
  aesop

private theorem bond_connects_self_false_early (mol : RawMolecule)
    (hwellFormed : mol.WellFormed) (bond : RawBond) (hbond : bond ∈ mol.bonds)
    (atom : ℕ) : bond.connects atom atom = false := by
  rw [Bool.eq_false_iff]
  intro hconnects
  simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at hconnects
  rcases hconnects with h | h
  · exact (hwellFormed bond hbond).2.2 (h.1.trans h.2.symm)
  · exact (hwellFormed bond hbond).2.2 (h.1.trans h.2.symm)

private theorem countP_range_comp_atom (count next atom : ℕ) :
    (List.range count).countP
        ((fun copy : ℕ × ℕ => copy.1 == atom) ∘ fun index => (next, index)) =
      if next = atom then count else 0 := by
  simpa only [List.countP_map] using countP_rangeMap_atom count next atom

private theorem countP_range_comp_atom_nonzero (count next atom : ℕ) :
    (List.range count).countP
        (((fun copy : ℕ × ℕ => copy.1 == atom && copy.2 != 0)) ∘
          fun index => (next, index)) =
      if next = atom then count - 1 else 0 := by
  simpa only [List.countP_map] using countP_rangeMap_atom_nonzero count next atom

private theorem countP_range_eq_zero (count : ℕ) :
    (List.range count).countP (fun index => index == 0) =
      if 0 < count then 1 else 0 := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      cases count with
      | zero => decide
      | succ count =>
          rw [List.range_succ, List.countP_append, inductionHypothesis]
          simp

private theorem countP_rangeMap_atom_zero (count next atom : ℕ) :
    ((List.range count).map fun index => (next, index)).countP
        (fun copy => copy.1 == atom && copy.2 == 0) =
      if next = atom ∧ 0 < count then 1 else 0 := by
  rw [List.countP_map]
  by_cases heq : next = atom
  · subst next
    simpa [Function.comp_def] using countP_range_eq_zero count
  · simp [Function.comp_def, heq]

private theorem countP_range_comp_atom_zero (count next atom : ℕ) :
    (List.range count).countP
        (((fun copy : ℕ × ℕ => copy.1 == atom && copy.2 == 0)) ∘
          fun index => (next, index)) =
      if next = atom ∧ 0 < count then 1 else 0 := by
  simpa only [List.countP_map] using countP_rangeMap_atom_zero count next atom

private theorem copiesFromBond_atom_count (mol : RawMolecule)
    (node : CanonicalBranchNode) (bond : RawBond) (atom : ℕ) :
    (copiesFromBond mol node bond).countP (fun copy => copy.1 == atom) =
      if bond.connects node.atom atom then mol.canonicalBondOrder node atom else 0 := by
  unfold copiesFromBond
  by_cases hsource : bond.source = node.atom
  · by_cases htarget : bond.target = atom
    · simp only [hsource, htarget, beq_self_eq_true, ↓reduceIte, List.countP_map]
      rw [countP_range_comp_atom]
      have htrue : bond.connects node.atom atom = true := by
        simp [RawBond.connects, hsource, htarget]
      simp [htrue]
    · simp only [hsource, beq_self_eq_true, ↓reduceIte,
        List.countP_map]
      rw [countP_range_comp_atom]
      have hfalse : bond.connects node.atom atom = false := by
        rw [Bool.eq_false_iff]
        intro htrue
        simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
          beq_iff_eq] at htrue
        aesop
      simp [htarget, hfalse]
  · by_cases htarget : bond.target = node.atom
    · by_cases hsourceAtom : bond.source = atom
      · have hne : atom ≠ node.atom := by
          intro heq
          exact hsource (hsourceAtom.trans heq)
        simp only [htarget, hsourceAtom, beq_self_eq_true, beq_eq_false_iff_ne.mpr hne,
          Bool.false_eq_true, ↓reduceIte, List.countP_map]
        rw [countP_range_comp_atom]
        simp [RawBond.connects, htarget, hsourceAtom]
      · simp only [beq_iff_eq, hsource, htarget, beq_self_eq_true,
          ↓reduceIte, List.countP_map]
        rw [countP_range_comp_atom]
        have hfalse : bond.connects node.atom atom = false := by
          simp [RawBond.connects, hsource, htarget, hsourceAtom]
        simp [hsourceAtom, hfalse]
    · simp [hsource, htarget, RawBond.connects]

private theorem childCopySeeds_atom_count (mol : RawMolecule)
    (node : CanonicalBranchNode) (atom : ℕ) :
    (childCopySeeds mol node).countP (fun copy => copy.1 == atom) =
      mol.bonds.countP (fun bond => bond.connects node.atom atom) *
        mol.canonicalBondOrder node atom := by
  unfold childCopySeeds
  induction mol.bonds with
  | nil => simp
  | cons bond bonds inductionHypothesis =>
      rw [List.flatMap_cons, List.countP_append,
        copiesFromBond_atom_count, inductionHypothesis, List.countP_cons]
      by_cases hconnects : bond.connects node.atom atom = true
      · simp [hconnects, Nat.add_comm, Nat.add_mul]
      · simp [hconnects]

private theorem copiesFromBond_atom_nonzero_count (mol : RawMolecule)
    (node : CanonicalBranchNode) (bond : RawBond) (atom : ℕ) :
    (copiesFromBond mol node bond).countP
        (fun copy => copy.1 == atom && copy.2 != 0) =
      if bond.connects node.atom atom then
        mol.canonicalBondOrder node atom - 1 else 0 := by
  unfold copiesFromBond
  by_cases hsource : bond.source = node.atom
  · by_cases htarget : bond.target = atom
    · simp only [hsource, htarget, beq_self_eq_true, ↓reduceIte, List.countP_map]
      rw [countP_range_comp_atom_nonzero]
      have htrue : bond.connects node.atom atom = true := by
        simp [RawBond.connects, hsource, htarget]
      simp [htrue]
    · have hfalse : bond.connects node.atom atom = false := by
        rw [Bool.eq_false_iff]
        intro htrue
        simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
          beq_iff_eq] at htrue
        aesop
      simp only [beq_iff_eq, hsource, ↓reduceIte, List.countP_map]
      convert countP_rangeMap_atom_nonzero (mol.canonicalBondOrder node bond.target)
          bond.target atom using 1 <;>
        simp [Function.comp_def, htarget, hfalse]
  · by_cases htarget : bond.target = node.atom
    · by_cases hsourceAtom : bond.source = atom
      · have hne : atom ≠ node.atom := by aesop
        simp only [beq_iff_eq, htarget, hsourceAtom,
          beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte, List.countP_map]
        simpa [Function.comp_def, RawBond.connects, htarget, hsourceAtom] using
          countP_rangeMap_atom_nonzero (mol.canonicalBondOrder node atom) atom atom
      · have hfalse : bond.connects node.atom atom = false := by
          rw [Bool.eq_false_iff]
          intro htrue
          simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
            beq_iff_eq] at htrue
          aesop
        simp only [beq_iff_eq, hsource, htarget, ↓reduceIte, List.countP_map]
        convert countP_rangeMap_atom_nonzero (mol.canonicalBondOrder node bond.source)
            bond.source atom using 1 <;>
          simp [Function.comp_def, hsourceAtom, hfalse]
    · simp [hsource, htarget, RawBond.connects]

private theorem childCopySeeds_atom_nonzero_count (mol : RawMolecule)
    (node : CanonicalBranchNode) (atom : ℕ) :
    (childCopySeeds mol node).countP
        (fun copy => copy.1 == atom && copy.2 != 0) =
      mol.bonds.countP (fun bond => bond.connects node.atom atom) *
        (mol.canonicalBondOrder node atom - 1) := by
  unfold childCopySeeds
  induction mol.bonds with
  | nil => simp
  | cons bond bonds inductionHypothesis =>
      rw [List.flatMap_cons, List.countP_append,
        copiesFromBond_atom_nonzero_count, inductionHypothesis, List.countP_cons]
      by_cases hconnects : bond.connects node.atom atom = true
      · simp [hconnects, Nat.add_comm, Nat.add_mul]
      · simp [hconnects]

private theorem copiesFromBond_atom_zero_count (mol : RawMolecule)
    (node : CanonicalBranchNode) (bond : RawBond) (atom : ℕ) :
    (copiesFromBond mol node bond).countP
        (fun copy => copy.1 == atom && copy.2 == 0) =
      if bond.connects node.atom atom && 0 < mol.canonicalBondOrder node atom then 1 else 0 := by
  unfold copiesFromBond
  by_cases hsource : bond.source = node.atom
  · by_cases htarget : bond.target = atom
    · have htrue : bond.connects node.atom atom = true := by
        simp [RawBond.connects, hsource, htarget]
      simp only [hsource, htarget, beq_self_eq_true, ↓reduceIte]
      rw [countP_rangeMap_atom_zero]
      simp [htrue]
    · have hfalse : bond.connects node.atom atom = false := by
        rw [Bool.eq_false_iff]
        intro htrue
        simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
          beq_iff_eq] at htrue
        aesop
      simp [hsource, htarget, hfalse]
  · by_cases htarget : bond.target = node.atom
    · by_cases hsourceAtom : bond.source = atom
      · have hne : atom ≠ node.atom := by aesop
        have hsourceBool : (bond.source == node.atom) = false :=
          beq_eq_false_iff_ne.mpr hsource
        have htrue : bond.connects node.atom atom = true := by
          simp [RawBond.connects, htarget, hsourceAtom]
        simp only [hsourceBool, Bool.false_eq_true, htarget, beq_self_eq_true,
          ↓reduceIte, List.countP_map]
        rw [countP_range_comp_atom_zero]
        simp [htrue, hsourceAtom]
      · have hfalse : bond.connects node.atom atom = false := by
          rw [Bool.eq_false_iff]
          intro htrue
          simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
            beq_iff_eq] at htrue
          aesop
        simp [hsource, htarget, hsourceAtom, hfalse]
    · simp [hsource, htarget, RawBond.connects]

private theorem childCopySeeds_atom_zero_count (mol : RawMolecule)
    (node : CanonicalBranchNode) (atom : ℕ) :
    (childCopySeeds mol node).countP
        (fun copy => copy.1 == atom && copy.2 == 0) =
      mol.bonds.countP (fun bond => bond.connects node.atom atom) *
        (if 0 < mol.canonicalBondOrder node atom then 1 else 0) := by
  unfold childCopySeeds
  induction mol.bonds with
  | nil => simp
  | cons bond bonds inductionHypothesis =>
      rw [List.flatMap_cons, List.countP_append,
        copiesFromBond_atom_zero_count, inductionHypothesis, List.countP_cons]
      by_cases hconnects : bond.connects node.atom atom = true <;>
        by_cases horder : 0 < mol.canonicalBondOrder node atom <;>
        simp [hconnects, horder, Nat.add_comm]

private theorem childCopySeeds_atom_zero_count_eq (mol : RawMolecule)
    (node : CanonicalBranchNode) (atom : ℕ)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (hhead : node.history.head? = some node.atom) :
    (childCopySeeds mol node).countP
        (fun copy => copy.1 == atom && copy.2 == 0) =
      if node.atom = atom then 0
      else if 0 < mol.canonicalBondOrder node atom then 1 else 0 := by
  rw [childCopySeeds_atom_zero_count]
  by_cases hself : node.atom = atom
  · subst atom
    have hcount : mol.bonds.countP (fun bond => bond.connects node.atom node.atom) = 0 := by
      apply List.countP_eq_zero.mpr
      intro bond hbond htrue
      have hfalse := bond_connects_self_false_early mol hwellFormed bond hbond node.atom
      rw [hfalse] at htrue
      contradiction
    simp [hcount]
  · by_cases horder : 0 < mol.canonicalBondOrder node atom
    · have hrawPositive := mol.canonicalBondOrder_pos_imp_bondOrder_pos
        node atom hhead horder
      obtain ⟨bond, hbond, hconnects⟩ :=
        (mol.bondOrder_pos_iff node.atom atom hself).1 hrawPositive
      have hcountPositive : 0 < mol.bonds.countP
          (fun bond => bond.connects node.atom atom) :=
        List.countP_pos_iff.2 ⟨bond, hbond, hconnects⟩
      have hcountLe := incident_record_count_le_one mol hunique node.atom atom
      have hcount : mol.bonds.countP (fun bond => bond.connects node.atom atom) = 1 := by
        omega
      simp [hself, horder, hcount]
    · simp [hself, horder]

private theorem childCopySeeds_atom_count_eq_order (mol : RawMolecule)
    (node : CanonicalBranchNode) (atom : ℕ)
    (hunique : mol.BondRecordsUnique)
    (hhead : node.history.head? = some node.atom)
    (hne : node.atom ≠ atom) :
    (childCopySeeds mol node).countP (fun copy => copy.1 == atom) =
      mol.canonicalBondOrder node atom := by
  rw [childCopySeeds_atom_count]
  by_cases horder : mol.canonicalBondOrder node atom = 0
  · simp [horder]
  · have hpositive : 0 < mol.canonicalBondOrder node atom := Nat.pos_of_ne_zero horder
    have hrawPositive := mol.canonicalBondOrder_pos_imp_bondOrder_pos
      node atom hhead hpositive
    obtain ⟨bond, hbond, hconnects⟩ :=
      (mol.bondOrder_pos_iff node.atom atom hne).1 hrawPositive
    have hcountPositive : 0 < mol.bonds.countP
        (fun bond => bond.connects node.atom atom) :=
      List.countP_pos_iff.2 ⟨bond, hbond, hconnects⟩
    have hcountLe := incident_record_count_le_one mol hunique node.atom atom
    have hcount : mol.bonds.countP (fun bond => bond.connects node.atom atom) = 1 := by
      omega
    simp [hcount]

private theorem childCopySeeds_atom_nonzero_count_eq_order_sub_one
    (mol : RawMolecule) (node : CanonicalBranchNode) (atom : ℕ)
    (hunique : mol.BondRecordsUnique)
    (hhead : node.history.head? = some node.atom)
    (hne : node.atom ≠ atom) :
    (childCopySeeds mol node).countP
        (fun copy => copy.1 == atom && copy.2 != 0) =
      mol.canonicalBondOrder node atom - 1 := by
  rw [childCopySeeds_atom_nonzero_count]
  by_cases hmeasure : mol.canonicalBondOrder node atom - 1 = 0
  · simp [hmeasure]
  · have horderPositive : 0 < mol.canonicalBondOrder node atom := by omega
    have hrawPositive := mol.canonicalBondOrder_pos_imp_bondOrder_pos
      node atom hhead horderPositive
    obtain ⟨bond, hbond, hconnects⟩ :=
      (mol.bondOrder_pos_iff node.atom atom hne).1 hrawPositive
    have hcountPositive : 0 < mol.bonds.countP
        (fun bond => bond.connects node.atom atom) :=
      List.countP_pos_iff.2 ⟨bond, hbond, hconnects⟩
    have hcountLe := incident_record_count_le_one mol hunique node.atom atom
    have hcount : mol.bonds.countP (fun bond => bond.connects node.atom atom) = 1 := by
      omega
    simp [hcount]

private theorem zero_mem_childCopySeeds (mol : RawMolecule)
    (node : CanonicalBranchNode) (atom : ℕ)
    (hhead : node.history.head? = some node.atom)
    (hne : node.atom ≠ atom)
    (hpositive : 0 < mol.canonicalBondOrder node atom) :
    (atom, 0) ∈ childCopySeeds mol node := by
  have hrawPositive := mol.canonicalBondOrder_pos_imp_bondOrder_pos
    node atom hhead hpositive
  obtain ⟨bond, hbond, hconnects⟩ :=
    (mol.bondOrder_pos_iff node.atom atom hne).1 hrawPositive
  unfold childCopySeeds
  rw [List.mem_flatMap]
  refine ⟨bond, hbond, ?_⟩
  simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at hconnects
  rcases hconnects with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · unfold copiesFromBond
    simp [hsource, htarget, hpositive]
  · unfold copiesFromBond
    have hsourceNe : bond.source ≠ node.atom := by aesop
    have hreverseNe : atom ≠ node.atom := hne.symm
    simp [hsource, htarget, hreverseNe, hpositive]

private theorem bond_connects_self_false (mol : RawMolecule)
    (hwellFormed : mol.WellFormed) (bond : RawBond) (hbond : bond ∈ mol.bonds)
    (atom : ℕ) : bond.connects atom atom = false := by
  rw [Bool.eq_false_iff]
  intro hconnects
  simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at hconnects
  rcases hconnects with h | h
  · exact (hwellFormed bond hbond).2.2 (h.1.trans h.2.symm)
  · exact (hwellFormed bond hbond).2.2 (h.1.trans h.2.symm)

private theorem canonicalBondOrder_self (mol : RawMolecule)
    (node : CanonicalBranchNode)
    (hhead : node.history.head? = some node.atom) :
    mol.canonicalBondOrder node node.atom = 0 := by
  unfold canonicalBondOrder
  cases hhistory : node.history with
  | nil => simp [hhistory] at hhead
  | cons current rest =>
      have hcurrent : current = node.atom := by simpa [hhistory] using hhead
      subst current
      cases rest with
      | nil => simp [mol.bondOrder_self]
      | cons center tail =>
          cases tail with
          | nil =>
              by_cases hspecial : node.atom == center &&
                  mol.isTrigonalPyramidalOxidoRootEdge center node.atom
              · simp only [Bool.and_eq_true] at hspecial
                have heq : node.atom = center := beq_iff_eq.mp hspecial.1
                subst center
                unfold isTrigonalPyramidalOxidoRootEdge at hspecial
                split at hspecial <;> simp_all [mol.bondOrder_self]
              · simp [hspecial, mol.bondOrder_self]
          | cons another tail => simp [mol.bondOrder_self]

private theorem childCopySeeds_self_atom_count_eq_zero (mol : RawMolecule)
    (node : CanonicalBranchNode) (hwellFormed : mol.WellFormed) :
    (childCopySeeds mol node).countP (fun copy => copy.1 == node.atom) = 0 := by
  rw [childCopySeeds_atom_count]
  have hcount : mol.bonds.countP (fun bond => bond.connects node.atom node.atom) = 0 := by
    apply List.countP_eq_zero.mpr
    intro bond hbond htrue
    have hfalse := bond_connects_self_false mol hwellFormed bond hbond node.atom
    rw [hfalse] at htrue
    contradiction
  simp [hcount]

private theorem canonicalChildCopies_atom_count (mol : RawMolecule)
    (node : CanonicalBranchNode) (atom : ℕ)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (hhead : node.history.head? = some node.atom) :
    (mol.canonicalChildCopies node).countP (fun copy => copy.1 == atom) =
      mol.canonicalBondOrder node atom - (if atom = node.parent then 1 else 0) := by
  rw [canonicalChildCopies_eq, countP_eraseCanonicalParentCopy]
  by_cases hself : node.atom = atom
  · subst atom
    rw [childCopySeeds_self_atom_count_eq_zero mol node hwellFormed]
    rw [canonicalBondOrder_self mol node hhead]
    simp
  · rw [childCopySeeds_atom_count_eq_order mol node atom hunique hhead hself]
    by_cases hparent : atom = node.parent
    · subst atom
      by_cases horder : mol.canonicalBondOrder node node.parent = 0
      · have hnotMem : (node.parent, 0) ∉ childCopySeeds mol node := by
          intro hmem
          have hcountPositive : 0 < (childCopySeeds mol node).countP
              (fun copy => copy.1 == node.parent) :=
            List.countP_pos_iff.2 ⟨(node.parent, 0), hmem, by simp⟩
          rw [childCopySeeds_atom_count_eq_order mol node node.parent hunique hhead hself,
            horder] at hcountPositive
          omega
        simp [horder, hnotMem]
      · have hpositive : 0 < mol.canonicalBondOrder node node.parent :=
          Nat.pos_of_ne_zero horder
        have hmem := zero_mem_childCopySeeds mol node node.parent hhead hself hpositive
        simp [hmem]
    · simp [hparent, Ne.symm hparent]

private theorem canonicalChildCopies_atom_nonzero_count (mol : RawMolecule)
    (node : CanonicalBranchNode) (atom : ℕ)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (hhead : node.history.head? = some node.atom) :
    (mol.canonicalChildCopies node).countP
        (fun copy => copy.1 == atom && copy.2 != 0) =
      if node.atom = atom then 0 else mol.canonicalBondOrder node atom - 1 := by
  rw [canonicalChildCopies_eq, countP_eraseCanonicalParentCopy]
  by_cases hself : node.atom = atom
  · subst atom
    rw [childCopySeeds_atom_nonzero_count]
    have hcount : mol.bonds.countP (fun bond => bond.connects node.atom node.atom) = 0 := by
      apply List.countP_eq_zero.mpr
      intro bond hbond htrue
      have hfalse := bond_connects_self_false mol hwellFormed bond hbond node.atom
      rw [hfalse] at htrue
      contradiction
    simp [hcount]
  · rw [childCopySeeds_atom_nonzero_count_eq_order_sub_one
      mol node atom hunique hhead hself]
    simp [hself]

private theorem canonicalChildCopies_atom_zero_count (mol : RawMolecule)
    (node : CanonicalBranchNode) (atom : ℕ)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (hhead : node.history.head? = some node.atom) :
    (mol.canonicalChildCopies node).countP
        (fun copy => copy.1 == atom && copy.2 == 0) =
      if node.atom = atom then 0
      else if 0 < mol.canonicalBondOrder node atom ∧ atom ≠ node.parent then 1 else 0 := by
  rw [canonicalChildCopies_eq, countP_eraseCanonicalParentCopy,
    childCopySeeds_atom_zero_count_eq mol node atom hwellFormed hunique hhead]
  by_cases hself : node.atom = atom
  · simp [hself]
  · by_cases horder : 0 < mol.canonicalBondOrder node atom
    · by_cases hparent : atom = node.parent
      · subst atom
        have hmem := zero_mem_childCopySeeds mol node node.parent hhead hself horder
        simp [hself, horder, hmem]
      · simp [hself, horder, hparent, Ne.symm hparent]
    · simp [hself, horder]

private theorem canonicalChildren_atom_count (mol : RawMolecule)
    (node : CanonicalBranchNode) (atom : ℕ)
    (hreal : node.provenance = CanonicalNodeProvenance.realAtom)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (hhead : node.history.head? = some node.atom) :
    (mol.canonicalChildren node).countP (fun child => child.atom == atom) =
      mol.canonicalBondOrder node atom - (if atom = node.parent then 1 else 0) := by
  unfold canonicalChildren
  simp only [CanonicalBranchNode.forcedLeaf, hreal, Bool.false_eq_true, ↓reduceIte,
    List.countP_map, Function.comp_def]
  exact canonicalChildCopies_atom_count mol node atom hwellFormed hunique hhead

private theorem canonicalChildren_atom_multiple_count (mol : RawMolecule)
    (node : CanonicalBranchNode) (atom : ℕ)
    (hreal : node.provenance = CanonicalNodeProvenance.realAtom)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (hhead : node.history.head? = some node.atom) :
    (mol.canonicalChildren node).countP (fun child =>
      child.atom == atom &&
        match child.provenance with
        | CanonicalNodeProvenance.multipleBondDuplicate _ => true
        | _ => false) =
      if node.atom = atom then 0 else mol.canonicalBondOrder node atom - 1 := by
  unfold canonicalChildren
  simp only [CanonicalBranchNode.forcedLeaf, hreal, Bool.false_eq_true, ↓reduceIte,
    List.countP_map]
  change (mol.canonicalChildCopies node).countP
      ((fun child => child.atom == atom &&
        match child.provenance with
        | CanonicalNodeProvenance.multipleBondDuplicate _ => true
        | _ => false) ∘ nodeFromCopy node) = _
  rw [← canonicalChildCopies_atom_nonzero_count mol node atom hwellFormed hunique hhead]
  apply congrArg (fun predicate =>
    (mol.canonicalChildCopies node).countP predicate)
  funext copy
  simp only [Function.comp_apply]
  by_cases hnonzero : copy.2 != 0
  · simp [nodeFromCopy, hnonzero]
  · have hzero : copy.2 = 0 := by simpa using hnonzero
    by_cases hhistory : copy.1 ∈ node.history
    · simp [nodeFromCopy, hzero, hhistory]
    · simp [nodeFromCopy, hzero, hhistory]

private theorem canonicalChildren_atom_ring_count (mol : RawMolecule)
    (node : CanonicalBranchNode) (atom : ℕ)
    (hreal : node.provenance = CanonicalNodeProvenance.realAtom)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (hhead : node.history.head? = some node.atom) :
    (mol.canonicalChildren node).countP (fun child =>
      child.atom == atom &&
        match child.provenance with
        | CanonicalNodeProvenance.ringDuplicate _ => true
        | _ => false) =
      if node.atom = atom then 0
      else if 0 < mol.canonicalBondOrder node atom ∧ atom ≠ node.parent ∧
          atom ∈ node.history then 1 else 0 := by
  unfold canonicalChildren
  simp only [CanonicalBranchNode.forcedLeaf, hreal, Bool.false_eq_true, ↓reduceIte,
    List.countP_map]
  change (mol.canonicalChildCopies node).countP
      ((fun child => child.atom == atom &&
        match child.provenance with
        | CanonicalNodeProvenance.ringDuplicate _ => true
        | _ => false) ∘ nodeFromCopy node) = _
  have hclassify :
      (mol.canonicalChildCopies node).countP
          ((fun child => child.atom == atom &&
            match child.provenance with
            | CanonicalNodeProvenance.ringDuplicate _ => true
            | _ => false) ∘ nodeFromCopy node) =
        (mol.canonicalChildCopies node).countP
          (fun copy => copy.1 == atom && copy.2 == 0 &&
            node.history.contains copy.1) := by
    apply congrArg (fun predicate => (mol.canonicalChildCopies node).countP predicate)
    funext copy
    by_cases hzero : copy.2 = 0
    · by_cases hhistory : copy.1 ∈ node.history
      · simp [nodeFromCopy, hzero, hhistory]
      · simp [nodeFromCopy, hzero, hhistory]
    · have hnonzero : copy.2 != 0 := by simpa using hzero
      simp [nodeFromCopy, hnonzero, hzero]
  rw [hclassify]
  by_cases hhistory : atom ∈ node.history
  · have heq :
        (mol.canonicalChildCopies node).countP
            (fun copy => copy.1 == atom && copy.2 == 0 &&
              node.history.contains copy.1) =
          (mol.canonicalChildCopies node).countP
            (fun copy => copy.1 == atom && copy.2 == 0) := by
      apply congrArg (fun predicate => (mol.canonicalChildCopies node).countP predicate)
      funext copy
      by_cases hatom : copy.1 = atom <;> simp [hatom, hhistory]
    rw [heq, canonicalChildCopies_atom_zero_count
      mol node atom hwellFormed hunique hhead]
    simp [hhistory]
  · have heq :
        (mol.canonicalChildCopies node).countP
            (fun copy => copy.1 == atom && copy.2 == 0 &&
              node.history.contains copy.1) = 0 := by
      apply List.countP_eq_zero.mpr
      intro copy hcopy htrue
      simp only [Bool.and_eq_true, beq_iff_eq] at htrue
      exact hhistory (htrue.1.1 ▸ (List.contains_iff_mem.mp htrue.2))
    rw [heq]
    simp [hhistory]

private theorem canonicalChildren_atom_real_count (mol : RawMolecule)
    (node : CanonicalBranchNode) (atom : ℕ)
    (hreal : node.provenance = CanonicalNodeProvenance.realAtom)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (hhead : node.history.head? = some node.atom) :
    (mol.canonicalChildren node).countP (fun child =>
      child.atom == atom &&
        match child.provenance with
        | CanonicalNodeProvenance.realAtom => true
        | _ => false) =
      if node.atom = atom then 0
      else if 0 < mol.canonicalBondOrder node atom ∧ atom ≠ node.parent ∧
          atom ∉ node.history then 1 else 0 := by
  unfold canonicalChildren
  simp only [CanonicalBranchNode.forcedLeaf, hreal, Bool.false_eq_true, ↓reduceIte,
    List.countP_map]
  change (mol.canonicalChildCopies node).countP
      ((fun child => child.atom == atom &&
        match child.provenance with
        | CanonicalNodeProvenance.realAtom => true
        | _ => false) ∘ nodeFromCopy node) = _
  have hclassify :
      (mol.canonicalChildCopies node).countP
          ((fun child => child.atom == atom &&
            match child.provenance with
            | CanonicalNodeProvenance.realAtom => true
            | _ => false) ∘ nodeFromCopy node) =
        (mol.canonicalChildCopies node).countP
          (fun copy => copy.1 == atom && copy.2 == 0 &&
            !(node.history.contains copy.1)) := by
    apply congrArg (fun predicate => (mol.canonicalChildCopies node).countP predicate)
    funext copy
    by_cases hzero : copy.2 = 0
    · by_cases hhistory : copy.1 ∈ node.history
      · simp [nodeFromCopy, hzero, hhistory]
      · simp [nodeFromCopy, hzero, hhistory]
    · have hnonzero : copy.2 != 0 := by simpa using hzero
      simp [nodeFromCopy, hnonzero, hzero]
  rw [hclassify]
  by_cases hhistory : atom ∈ node.history
  · have heq :
        (mol.canonicalChildCopies node).countP
            (fun copy => copy.1 == atom && copy.2 == 0 &&
              !(node.history.contains copy.1)) = 0 := by
      apply List.countP_eq_zero.mpr
      intro copy hcopy htrue
      simp only [Bool.and_eq_true, beq_iff_eq] at htrue
      have hcontains : node.history.contains copy.1 = true :=
        List.contains_iff_mem.mpr (htrue.1.1 ▸ hhistory)
      have hnot := htrue.2
      rw [hcontains] at hnot
      simp at hnot
    rw [heq]
    simp [hhistory]
  · have heq :
        (mol.canonicalChildCopies node).countP
            (fun copy => copy.1 == atom && copy.2 == 0 &&
              !(node.history.contains copy.1)) =
          (mol.canonicalChildCopies node).countP
            (fun copy => copy.1 == atom && copy.2 == 0) := by
      apply congrArg (fun predicate => (mol.canonicalChildCopies node).countP predicate)
      funext copy
      by_cases hatom : copy.1 = atom <;> simp [hatom, hhistory]
    rw [heq, canonicalChildCopies_atom_zero_count
      mol node atom hwellFormed hunique hhead]
    simp [hhistory]

/-- A generated real child records its actual parent and is precisely the zero-index copy of an
atom not already present in the parent history. -/
theorem canonicalChildren_real_data (mol : RawMolecule)
    (parent child : CanonicalBranchNode)
    (hchild : child ∈ mol.canonicalChildren parent)
    (hreal : child.provenance = CanonicalNodeProvenance.realAtom) :
    child.parent = parent.atom ∧ child.atom ∉ parent.history := by
  unfold canonicalChildren at hchild
  by_cases hleaf : parent.forcedLeaf
  · simp [hleaf] at hchild
  · simp only [hleaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hchild
    obtain ⟨copy, hcopy, rfl⟩ := hchild
    by_cases hmultiple : copy.2 != 0
    · simp [hmultiple] at hreal
    · have hzero : copy.2 = 0 := by simpa using hmultiple
      by_cases hhistory : copy.1 ∈ parent.history
      · simp [hzero, hhistory] at hreal
      · exact ⟨rfl, by simpa using hhistory⟩

theorem canonicalBondOrder_eq_bondOrder_of_history_length_ne_two
    (mol : RawMolecule) (node : CanonicalBranchNode) (atom : ℕ)
    (hlength : node.history.length ≠ 2) :
    mol.canonicalBondOrder node atom = mol.bondOrder node.atom atom := by
  unfold canonicalBondOrder
  cases hhistory : node.history with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => exact (hlength (by simp [hhistory])).elim
          | cons third rest => rfl

end RawMolecule

namespace RawMolecule.CanonicalBranchKey

theorem ligand_mem_source_history_of_rootedAt_childrenExact
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hroot : key.RootedAt center ligand) (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source) :
    ligand.1 ∈ source.history := by
  have hcomplete := key.sourceComplete_of_root_and_childrenExact mol
    (RawMolecule.canonicalRoot center ligand) hroot hexact
  have hreachable := (key.toDeclarativeDigraph mol).reachable node
  change Relation.ReflTransGen key.HierarchyChild
    ⟨[], key.nil_mem_hierarchyAddresses⟩ node at hreachable
  revert source
  induction hreachable with
  | refl =>
      intro source hsource
      have hsourceEq : source = RawMolecule.canonicalRoot center ligand :=
        Option.some.inj (hsource.symm.trans hroot)
      subst source
      simp [RawMolecule.canonicalRoot]
  | tail hparent hchild ih =>
      intro source hsource
      rcases hcomplete _ with ⟨parentSource, hparentSource⟩
      rcases hexact _ parentSource hparentSource with ⟨equivalence, hlookup⟩
      let generated := (mol.canonicalChildren parentSource).get
        (equivalence ⟨_, hchild⟩)
      have hgenerated : generated ∈ mol.canonicalChildren parentSource := List.get_mem _ _
      have hsourceEq : source = generated :=
        Option.some.inj (hsource.symm.trans (hlookup ⟨_, hchild⟩))
      subst source
      rw [mol.canonicalChildren_history parentSource generated hgenerated]
      exact List.mem_cons_of_mem _ (ih parentSource hparentSource)

theorem canonicalBondOrder_eq_canonicalHierarchyBond_of_real_source
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hroot : key.RootedAt center ligand) (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source)
    (hreal : source.provenance = CanonicalNodeProvenance.realAtom)
    (atom : ℕ) :
    mol.canonicalBondOrder source atom =
      mol.canonicalHierarchyBond center ligand source.atom atom := by
  have hcomplete := key.sourceComplete_of_root_and_childrenExact mol
    (RawMolecule.canonicalRoot center ligand) hroot hexact
  have hreachable := (key.toDeclarativeDigraph mol).reachable node
  change Relation.ReflTransGen key.HierarchyChild
    ⟨[], key.nil_mem_hierarchyAddresses⟩ node at hreachable
  induction hreachable generalizing source with
  | refl =>
      have hsourceEq : source = RawMolecule.canonicalRoot center ligand :=
        Option.some.inj (hsource.symm.trans hroot)
      subst source
      unfold RawMolecule.canonicalRoot canonicalBondOrder canonicalHierarchyBond IsRootPair
      have hoxidoSelf : ∀ current,
          mol.isTrigonalPyramidalOxidoRootEdge current current = false := by
        intro current
        unfold RawMolecule.isTrigonalPyramidalOxidoRootEdge
        split <;> simp_all [mol.bondOrder_self]
      by_cases hdiag : ligand.1 = atom
      · subst atom
        by_cases hcl : center.1 = ligand.1
        · simp [hcl, hoxidoSelf, mol.bondOrder_self]
        · have hlc : ligand.1 ≠ center.1 := Ne.symm hcl
          simp [hlc, mol.bondOrder_self]
      · simp [hdiag, Ne.symm hdiag]
  | @tail parent node hpath hedge ih =>
      rcases hcomplete parent with ⟨parentSource, hparentSource⟩
      have hchildren := key.childrenSound_of_childrenExact mol hexact
      have hgenerated := hchildren parent node parentSource source hedge
        hparentSource hsource
      obtain ⟨_, hnew⟩ := mol.canonicalChildren_real_data parentSource source hgenerated hreal
      have hcenterMem := key.externalParent_mem_source_history mol center ligand
        hroot hexact parent parentSource hparentSource
      have hligandMem := key.ligand_mem_source_history_of_rootedAt_childrenExact mol
        center ligand hroot hexact parent parentSource hparentSource
      have hsourceCenter : source.atom ≠ center.1 := fun heq => hnew (heq ▸ hcenterMem)
      have hsourceLigand : source.atom ≠ ligand.1 := fun heq => hnew (heq ▸ hligandMem)
      have hdepth := key.source_depth_eq_address_length_succ mol center ligand
        hroot hexact node source hsource
      have hhead := key.source_history_head_of_rootedAt_childrenExact mol center ligand
        hroot hexact node source hsource
      have hpositive : 0 < source.history.length := by
        cases hhistory : source.history with
        | nil => simp [hhistory] at hhead
        | cons first rest => simp
      have hlength : source.history.length ≠ 2 := by
        unfold CanonicalBranchNode.depth at hdepth
        rcases hedge with ⟨slot, haddress⟩
        rw [haddress] at hdepth
        simp only [List.length_append, List.length_singleton] at hdepth
        omega
      rw [mol.canonicalBondOrder_eq_bondOrder_of_history_length_ne_two source atom hlength]
      unfold RawMolecule.canonicalHierarchyBond RawMolecule.IsRootPair
      by_cases heq : source.atom = atom
      · subst atom
        simp [mol.bondOrder_self]
      · simp [heq, hsourceCenter, hsourceLigand]

private theorem childAtomCount_eq_canonicalChildren_countP
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount) (hwellFormed : mol.WellFormed)
    (hexact : key.ChildrenExact mol)
    (parent : key.HierarchyNode) (parentSource : CanonicalBranchNode)
    (hparent : key.sourceNodeAtAddress? parent.1 = some parentSource)
    (hparentHead : parentSource.history.head? = some parentSource.atom)
    (atom : Fin mol.atomCount) :
    RootedDigraph.ChildAtomCount (key.toDeclarativeDigraph mol) parent atom =
      (mol.canonicalChildren parentSource).countP
        (fun child => child.atom == atom.1) := by
  classical
  have hchildren := key.childrenSound_of_childrenExact mol hexact
  unfold RootedDigraph.ChildAtomCount
  refine (key.childCountWhere_eq_canonicalChildren_countP mol hexact parent parentSource
    hparent
    (fun node => ((key.toDeclarativeDigraph mol).label node).atom? = some atom)
    (fun source => source.atom = atom.1) ?_).trans ?_
  · intro child childSource hchildSource
    have hgenerated := hchildren parent child.1 parentSource childSource child.2
      hparent hchildSource
    have hvalid := mol.canonicalChildren_atom_valid_and_adjacent center ligand hwellFormed
      parentSource childSource hparentHead hgenerated
    change (key.declarativeLabel mol child.1).atom? = some atom ↔ _
    rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol child.1 childSource hchildSource]
    have hatomIff :
        (⟨childSource.atom, hvalid.1⟩ : Fin mol.atomCount) = atom ↔
          childSource.atom = atom.1 := by
      exact Fin.ext_iff
    cases hp : childSource.provenance with
    | realAtom => simp [atomFin?, hvalid.1, hatomIff]
    | multipleBondDuplicate distance => simp [atomFin?, hvalid.1, hatomIff]
    | ringDuplicate distance => simp [atomFin?, hvalid.1, hatomIff]
    | phantom distance =>
        exact (mol.canonicalChildren_provenance_ne_phantom parentSource childSource
          hgenerated distance hp).elim
  · apply congrArg (fun predicate => (mol.canonicalChildren parentSource).countP predicate)
    funext child
    rfl

private theorem childAtomProvenanceCount_eq_canonicalChildren_countP
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount) (hwellFormed : mol.WellFormed)
    (hexact : key.ChildrenExact mol)
    (parent : key.HierarchyNode) (parentSource : CanonicalBranchNode)
    (hparent : key.sourceNodeAtAddress? parent.1 = some parentSource)
    (hparentHead : parentSource.history.head? = some parentSource.atom)
    (atom : Fin mol.atomCount)
    (nodeKind : NodeProvenance → Prop) (sourceKind : CanonicalNodeProvenance → Prop)
    [DecidablePred nodeKind] [DecidablePred sourceKind]
    (hkind : ∀ provenance,
      nodeKind (declarativeProvenance provenance) ↔ sourceKind provenance) :
    RootedDigraph.ChildAtomProvenanceCount (key.toDeclarativeDigraph mol)
        parent atom nodeKind =
      (mol.canonicalChildren parentSource).countP
        (fun child => decide (child.atom = atom.1 ∧ sourceKind child.provenance)) := by
  classical
  have hchildren := key.childrenSound_of_childrenExact mol hexact
  unfold RootedDigraph.ChildAtomProvenanceCount
  apply key.childCountWhere_eq_canonicalChildren_countP mol hexact parent parentSource
    hparent
    (fun node => ((key.toDeclarativeDigraph mol).label node).atom? = some atom ∧
      nodeKind ((key.toDeclarativeDigraph mol).label node).provenance)
    (fun source => source.atom = atom.1 ∧ sourceKind source.provenance)
  intro child childSource hchildSource
  have hgenerated := hchildren parent child.1 parentSource childSource child.2
    hparent hchildSource
  have hvalid := mol.canonicalChildren_atom_valid_and_adjacent center ligand hwellFormed
    parentSource childSource hparentHead hgenerated
  change ((key.declarativeLabel mol child.1).atom? = some atom ∧
      nodeKind (key.declarativeLabel mol child.1).provenance) ↔ _
  rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol child.1 childSource hchildSource]
  have hatomIff :
      (⟨childSource.atom, hvalid.1⟩ : Fin mol.atomCount) = atom ↔
        childSource.atom = atom.1 := by
    exact Fin.ext_iff
  cases hp : childSource.provenance with
  | realAtom => simp [atomFin?, hvalid.1, hkind, hatomIff]
  | multipleBondDuplicate distance => simp [atomFin?, hvalid.1, hkind, hatomIff]
  | ringDuplicate distance => simp [atomFin?, hvalid.1, hkind, hatomIff]
  | phantom distance =>
      exact (mol.canonicalChildren_provenance_ne_phantom parentSource childSource
        hgenerated distance hp).elim

/-- Exact occurrence accounting for every atom at every expandable production carrier. -/
theorem atomChildMultiplicities_of_rootedAt_childrenExact
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (hroot : key.RootedAt center ligand) (hexact : key.ChildrenExact mol) :
    RootedDigraph.AtomChildMultiplicities
      (mol.canonicalHierarchyMoleculeGraph center ligand) center
      (key.toDeclarativeDigraph mol) := by
  classical
  have hcomplete := key.sourceComplete_of_root_and_childrenExact mol
    (RawMolecule.canonicalRoot center ligand) hroot hexact
  have hcoherent := key.sourceCoherent_of_root_and_childrenExact mol center ligand
    hwellFormed hroot hexact
  intro parent parentAtom hparentAtom hparentReal atom
  rcases hcomplete parent with ⟨parentSource, hparentSource⟩
  have hhead := key.source_history_head_of_rootedAt_childrenExact mol center ligand
    hroot hexact parent parentSource hparentSource
  change (key.declarativeLabel mol parent).atom? = some parentAtom at hparentAtom
  change RootedDigraph.ProvenanceRealAtom
    (key.declarativeLabel mol parent).provenance at hparentReal
  have hsourceReal :
      parentSource.provenance = CanonicalNodeProvenance.realAtom := by
    rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol parent parentSource
      hparentSource] at hparentReal
    cases hp : parentSource.provenance <;>
      simp [hp, declarativeProvenance, RootedDigraph.ProvenanceRealAtom] at hparentReal
    rfl
  have hparentBound : parentSource.atom < mol.atomCount := by
    simpa [hsourceReal] using (hcoherent parent parentSource hparentSource).2
  have hparentFin := key.atomFin_eq_of_declarativeLabel_atom_eq mol parent parentSource
    hparentSource parentAtom hparentAtom
  have hparentEq : parentSource.atom = parentAtom.1 := by
    have hsome : some (⟨parentSource.atom, hparentBound⟩ : Fin mol.atomCount) =
        some parentAtom := by
      simpa [atomFin?, hparentBound] using hparentFin
    exact congrArg Fin.val (Option.some.inj hsome)
  have hbond :
      (mol.canonicalHierarchyMoleculeGraph center ligand).bond parentAtom atom =
        mol.canonicalBondOrder parentSource atom.1 := by
    change mol.canonicalHierarchyBond center ligand parentAtom.1 atom.1 = _
    rw [← hparentEq]
    exact (key.canonicalBondOrder_eq_canonicalHierarchyBond_of_real_source mol
      center ligand hroot hexact parent parentSource hparentSource hsourceReal atom.1).symm
  have htotal := key.childAtomCount_eq_canonicalChildren_countP mol center ligand
    hwellFormed hexact parent parentSource hparentSource hhead atom
  have hmultiple := key.childAtomProvenanceCount_eq_canonicalChildren_countP mol
    center ligand hwellFormed hexact parent parentSource hparentSource hhead atom
    RootedDigraph.ProvenanceMultipleBondDuplicate
    (fun provenance => match provenance with
      | CanonicalNodeProvenance.multipleBondDuplicate _ => True
      | _ => False) (by
        intro provenance
        cases provenance <;>
          simp [declarativeProvenance, RootedDigraph.ProvenanceMultipleBondDuplicate])
  have hring := key.childAtomProvenanceCount_eq_canonicalChildren_countP mol
    center ligand hwellFormed hexact parent parentSource hparentSource hhead atom
    RootedDigraph.ProvenanceRingDuplicate
    (fun provenance => match provenance with
      | CanonicalNodeProvenance.ringDuplicate _ => True
      | _ => False) (by
        intro provenance
        cases provenance <;>
          simp [declarativeProvenance, RootedDigraph.ProvenanceRingDuplicate])
  have hrealCount := key.childAtomProvenanceCount_eq_canonicalChildren_countP mol
    center ligand hwellFormed hexact parent parentSource hparentSource hhead atom
    RootedDigraph.ProvenanceRealAtom
    (fun provenance => provenance = CanonicalNodeProvenance.realAtom) (by
        intro provenance
        cases provenance <;>
          simp [declarativeProvenance, RootedDigraph.ProvenanceRealAtom])
  have hmultiple' :
      RootedDigraph.ChildAtomProvenanceCount (key.toDeclarativeDigraph mol)
          parent atom RootedDigraph.ProvenanceMultipleBondDuplicate =
        (mol.canonicalChildren parentSource).countP (fun child =>
          child.atom == atom.1 &&
            match child.provenance with
            | CanonicalNodeProvenance.multipleBondDuplicate _ => true
            | _ => false) := by
    rw [hmultiple]
    apply congrArg (fun predicate => (mol.canonicalChildren parentSource).countP predicate)
    funext child
    by_cases heq : child.atom = atom.1 <;>
      cases child.provenance <;> simp [heq]
  have hring' :
      RootedDigraph.ChildAtomProvenanceCount (key.toDeclarativeDigraph mol)
          parent atom RootedDigraph.ProvenanceRingDuplicate =
        (mol.canonicalChildren parentSource).countP (fun child =>
          child.atom == atom.1 &&
            match child.provenance with
            | CanonicalNodeProvenance.ringDuplicate _ => true
            | _ => false) := by
    rw [hring]
    apply congrArg (fun predicate => (mol.canonicalChildren parentSource).countP predicate)
    funext child
    by_cases heq : child.atom = atom.1 <;>
      cases child.provenance <;> simp [heq]
  have hrealCount' :
      RootedDigraph.ChildAtomProvenanceCount (key.toDeclarativeDigraph mol)
          parent atom RootedDigraph.ProvenanceRealAtom =
        (mol.canonicalChildren parentSource).countP (fun child =>
          child.atom == atom.1 &&
            match child.provenance with
            | CanonicalNodeProvenance.realAtom => true
            | _ => false) := by
    rw [hrealCount]
    apply congrArg (fun predicate => (mol.canonicalChildren parentSource).countP predicate)
    funext child
    by_cases heq : child.atom = atom.1 <;>
      cases child.provenance <;> simp [heq]
  rw [htotal, hmultiple', hring', hrealCount',
    RawMolecule.canonicalChildren_atom_count mol parentSource atom.1 hsourceReal
      hwellFormed hunique hhead,
    RawMolecule.canonicalChildren_atom_multiple_count mol parentSource atom.1 hsourceReal
      hwellFormed hunique hhead,
    RawMolecule.canonicalChildren_atom_ring_count mol parentSource atom.1 hsourceReal
      hwellFormed hunique hhead,
    RawMolecule.canonicalChildren_atom_real_count mol parentSource atom.1 hsourceReal
      hwellFormed hunique hhead,
    hbond]
  have hsuppressed := key.source_parent_eq_iff_suppressedParentAtom mol center ligand
    hwellFormed hroot hexact parent parentSource hparentSource atom
  have hadjacent :
      (mol.canonicalHierarchyMoleculeGraph center ligand).Adj parentAtom atom ↔
        0 < mol.canonicalBondOrder parentSource atom.1 := by
    change 0 < (mol.canonicalHierarchyMoleculeGraph center ligand).bond parentAtom atom ↔ _
    rw [hbond]
  constructor
  · rw [← hsuppressed]
    by_cases hsupp : atom.1 = parentSource.parent <;> simp [hsupp]
  · constructor
    · by_cases hself : parentSource.atom = atom.1
      · rw [if_pos hself]
        rw [← hself, RawMolecule.canonicalBondOrder_self mol parentSource hhead]
      · simp [hself]
    · constructor
      · by_cases hadj :
          (mol.canonicalHierarchyMoleculeGraph center ligand).Adj parentAtom atom
        · have horder : 0 < mol.canonicalBondOrder parentSource atom.1 :=
            hadjacent.mp hadj
          have hself : parentSource.atom ≠ atom.1 := by
            intro heq
            rw [← heq, RawMolecule.canonicalBondOrder_self mol parentSource hhead]
              at horder
            omega
          have hhistory :=
            key.source_history_mem_iff_branchAncestorAtom_of_adjacent mol center ligand
              hwellFormed hroot hexact parent parentSource hparentSource parentAtom atom
              hparentAtom hadj
          rw [← hhistory, ← hsuppressed]
          simp [hadj, horder, hself, and_comm]
        · have horder : ¬0 < mol.canonicalBondOrder parentSource atom.1 := by
            exact fun h => hadj (hadjacent.mpr h)
          simp [hadj, horder]
      · by_cases hadj :
          (mol.canonicalHierarchyMoleculeGraph center ligand).Adj parentAtom atom
        · have horder : 0 < mol.canonicalBondOrder parentSource atom.1 :=
            hadjacent.mp hadj
          have hself : parentSource.atom ≠ atom.1 := by
            intro heq
            rw [← heq, RawMolecule.canonicalBondOrder_self mol parentSource hhead]
              at horder
            omega
          have hhistory :=
            key.source_history_mem_iff_branchAncestorAtom_of_adjacent mol center ligand
              hwellFormed hroot hexact parent parentSource hparentSource parentAtom atom
              hparentAtom hadj
          rw [← hhistory]
          have hsuppressedBranch :
              RootedDigraph.SuppressedParentAtom (key.toDeclarativeDigraph mol)
                  center atom parent →
                RootedDigraph.BranchAncestorAtom (key.toDeclarativeDigraph mol)
                  center atom parent := by
            intro hsupp
            rcases hsupp with ⟨hrootNode, hatomCenter⟩ | ⟨ancestor, hedge, hlabel⟩
            · exact Or.inl hatomCenter
            · exact Or.inr ⟨ancestor, Relation.TransGen.single hedge, hlabel⟩
          by_cases hmem : atom.1 ∈ parentSource.history
          · simp [hadj, horder, hself, hmem]
          · have hneParent : atom.1 ≠ parentSource.parent := by
              intro heq
              have hsupp : RootedDigraph.SuppressedParentAtom
                  (key.toDeclarativeDigraph mol) center atom parent :=
                hsuppressed.mp heq
              exact hmem (hhistory.mpr (hsuppressedBranch hsupp))
            simp [hadj, horder, hself, hmem, hneParent]
        · have horder : ¬0 < mol.canonicalBondOrder parentSource atom.1 := by
            exact fun h => hadj (hadjacent.mpr h)
          simp [hadj, horder]

end RawMolecule.CanonicalBranchKey

end
end OneCenter
end TetraStereo
