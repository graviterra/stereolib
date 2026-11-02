import TetraStereo.OneCenter.ProductionCIPBranchingComparatorCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.ProductionCIPRerootComparatorLaws

/-!
Literal finite certification of the existing branching support predicate. This checks actual
production labels, terminality and children; it neither assumes comparator success nor changes
the production child-width or frontier-capacity limits. Support alone is not a frontier-capacity
certificate, a chemical admission certificate, or an external source approval.
-/

/-- A computable existence test for the actual optional production Rule-1a label. -/
def branchingCursorLabelAvailable? (mol : RawMolecule) (cursor : CanonicalRerootCursor) : Bool :=
  (mol.canonicalRule1aLabel? cursor.node).isSome

theorem branchingCursorLabelAvailable?_eq_true_iff (mol : RawMolecule)
    (cursor : CanonicalRerootCursor) :
    branchingCursorLabelAvailable? mol cursor = true ↔
      ∃ value, mol.canonicalRule1aLabel? cursor.node = some value := by
  cases labelEq : mol.canonicalRule1aLabel? cursor.node <;>
    simp [branchingCursorLabelAvailable?, labelEq]

/-- Terminal support may stop at any fuel. Nonterminal support consumes one fuel and checks every
actual child, with the existing production bound of three children. -/
def branchingCursorSupport? (mol : RawMolecule) : Nat → CanonicalRerootCursor → Bool
  | 0, cursor => branchingCursorLabelAvailable? mol cursor && cursorTerminal mol cursor
  | fuel + 1, cursor =>
      branchingCursorLabelAvailable? mol cursor &&
        (cursorTerminal mol cursor ||
          (decide ((cursor.children mol).length ≤ 3) &&
            (cursor.children mol).all (branchingCursorSupport? mol fuel)))

theorem branchingCursorSupport_zero_iff (mol : RawMolecule) (cursor : CanonicalRerootCursor) :
    BranchingCursorSupport mol 0 cursor ↔
      (∃ value, mol.canonicalRule1aLabel? cursor.node = some value) ∧
        cursorTerminal mol cursor = true := by
  constructor
  · intro support
    exact ⟨support.label, support.zero_terminal⟩
  · rintro ⟨label, terminal⟩
    exact .terminal 0 cursor label terminal

theorem branchingCursorSupport_succ_iff (mol : RawMolecule) (fuel : Nat)
    (cursor : CanonicalRerootCursor) :
    BranchingCursorSupport mol (fuel + 1) cursor ↔
      (∃ value, mol.canonicalRule1aLabel? cursor.node = some value) ∧
        (cursorTerminal mol cursor = true ∨
          (cursor.children mol).length ≤ 3 ∧
            ∀ child, child ∈ cursor.children mol → BranchingCursorSupport mol fuel child) := by
  constructor
  · intro support
    cases support with
    | terminal _ _ label terminal => exact ⟨label, Or.inl terminal⟩
    | branch _ _ children label childrenEq width childrenSupport =>
        refine ⟨label, Or.inr ⟨?_, ?_⟩⟩
        · simpa only [childrenEq] using width
        · simpa only [childrenEq] using childrenSupport
  · rintro ⟨label, terminal | ⟨width, childrenSupport⟩⟩
    · exact .terminal (fuel + 1) cursor label terminal
    · exact .branch fuel cursor (cursor.children mol) label rfl width childrenSupport



theorem branchingCursorSupport?_eq_true_iff (mol : RawMolecule) (fuel : Nat)
    (cursor : CanonicalRerootCursor) :
    branchingCursorSupport? mol fuel cursor = true ↔ BranchingCursorSupport mol fuel cursor := by
  induction fuel generalizing cursor with
  | zero =>
      rw [branchingCursorSupport_zero_iff]
      simp only [branchingCursorSupport?, Bool.and_eq_true,
        branchingCursorLabelAvailable?_eq_true_iff]
  | succ fuel ih =>
      rw [branchingCursorSupport_succ_iff]
      simp only [branchingCursorSupport?, Bool.and_eq_true, Bool.or_eq_true,
        branchingCursorLabelAvailable?_eq_true_iff, decide_eq_true_eq, List.all_eq_true, ih]

theorem BranchingCursorSupport.of_check {mol : RawMolecule} {fuel : Nat}
    {cursor : CanonicalRerootCursor} (accepted : branchingCursorSupport? mol fuel cursor = true) :
    BranchingCursorSupport mol fuel cursor :=
  (branchingCursorSupport?_eq_true_iff mol fuel cursor).mp accepted

theorem BranchingCursorSupport.check {mol : RawMolecule} {fuel : Nat}
    {cursor : CanonicalRerootCursor} (support : BranchingCursorSupport mol fuel cursor) :
    branchingCursorSupport? mol fuel cursor = true :=
  (branchingCursorSupport?_eq_true_iff mol fuel cursor).mpr support

namespace BranchingSupportExamples

/-- A small graph fixture, not a source-reviewed chemical input. -/
def twoCarbon : RawMolecule where
  atoms := List.replicate 2 (AtomSpec.aliphatic Element.C)
  bonds := [{ source := 0, target := 1, kind := .single }]

def twoCarbonRoot : CanonicalRerootCursor where
  node := { atom := 0, parent := 0, history := [0], provenance := .realAtom }

theorem twoCarbon_zero_refused : branchingCursorSupport? twoCarbon 0 twoCarbonRoot = false := by
  decide

theorem twoCarbon_one_accepted : branchingCursorSupport? twoCarbon 1 twoCarbonRoot = true := by
  decide

theorem twoCarbon_one_supported : BranchingCursorSupport twoCarbon 1 twoCarbonRoot :=
  BranchingCursorSupport.of_check twoCarbon_one_accepted

/-- A genuinely branching finite graph fixture with three actual children. -/
def threeChildStar : RawMolecule where
  atoms := List.replicate 4 (AtomSpec.aliphatic Element.C)
  bonds := [{ source := 0, target := 1, kind := .single },
    { source := 0, target := 2, kind := .single },
    { source := 0, target := 3, kind := .single }]

theorem threeChildStar_actual_width : (twoCarbonRoot.children threeChildStar).length = 3 := by
  decide

theorem threeChildStar_ten_accepted :
    branchingCursorSupport? threeChildStar 10 twoCarbonRoot = true := by
  decide

theorem threeChildStar_ten_supported : BranchingCursorSupport threeChildStar 10 twoCarbonRoot :=
  BranchingCursorSupport.of_check threeChildStar_ten_accepted

/-- Four actual children expose the existing width boundary independently of finite fuel. -/
def fourChildStar : RawMolecule where
  atoms := List.replicate 5 (AtomSpec.aliphatic Element.C)
  bonds := [{ source := 0, target := 1, kind := .single },
    { source := 0, target := 2, kind := .single },
    { source := 0, target := 3, kind := .single },
    { source := 0, target := 4, kind := .single }]

theorem fourChildStar_one_refused :
    branchingCursorSupport? fourChildStar 1 twoCarbonRoot = false := by
  decide

theorem fourChildStar_one_unsupported :
    ¬ BranchingCursorSupport fourChildStar 1 twoCarbonRoot := by
  intro support
  have accepted := support.check
  rw [fourChildStar_one_refused] at accepted
  contradiction

end BranchingSupportExamples

end TetraStereo.OneCenter.ProductionCIPRerootComparatorLaws
