import TetraStereo.Engine.RingIsotopePriority
import TetraStereo.Engine.RingEnantiomorphicArms

set_option autoImplicit false

namespace TetraStereo.Examples.RingIsotopeAssignment
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open Engine.RingChemicalPriority

/-- Fluorocyclopropane, with an explicit nuclide on each CH₂ carbon.
Atom 0 is CHF, atoms 1 and 2 are CH₂, and atoms 3 and 4 are F and H. -/
def molecule (leftMass rightMass : Nat) : RawMolecule where
  atoms := [.aliphatic .C, {element := .C, isotope? := some leftMass},
    {element := .C, isotope? := some rightMass}, .aliphatic .F, .aliphatic .H,
    .aliphatic .H, .aliphatic .H, .aliphatic .H, .aliphatic .H]
  bonds := ([(0,1),(1,2),(2,0),(0,3),(0,4),(1,5),(1,6),(2,7),(2,8)] :
    List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

/-- The carbons span the xy-plane. Reflection in x interchanges the two
ring arms, including their hydrogens, and fixes the F, CHF carbon and CHF
hydrogen. Each carbon is the centroid of its four neighboring atoms. -/
def geometry : Geometry := fun i =>
  ([⟨0,0,0⟩,⟨1,2,0⟩,⟨-1,2,0⟩,⟨0,-2,-2⟩,⟨0,-2,2⟩,
    ⟨2,3,-1⟩,⟨3,3,1⟩,⟨-2,3,-1⟩,⟨-3,3,1⟩] : List CartesianPoint3)[i]?

def exchangeArms : Nat → Nat
  | 1 => 2 | 2 => 1 | 5 => 7 | 7 => 5 | 6 => 8 | 8 => 6 | i => i

/-- With equal isotopes the two ligands are related by a spatial reflection
of the entire molecule preserving every atom and bond specification. -/
theorem equal_mass_reflection : Reflects (molecule 12 12) geometry exchangeArms := by
  constructor <;> decide +kernel

/-- Every molecularly equivariant, reflection-invariant observation gives
the same priority value on the two arms of the equal-isotope control. -/
theorem equal_mass_arm_values {α : Type} (read : Geometry → Nat → Nat → α)
    (equivariant : ∀ f, Reflects (molecule 12 12) geometry f → ∀ root arm,
      read geometry (f root) (f arm) = read (mirror geometry) root arm)
    (invariant : ∀ root arm, read (mirror geometry) root arm = read geometry root arm) :
    read geometry 0 1 = read geometry 0 2 :=
  earlier_rules_tie equal_mass_reflection read equivariant invariant rfl rfl

theorem equal_mass_no_strict_order {α : Type} [Preorder α]
    (read : Geometry → Nat → Nat → α)
    (equivariant : ∀ f, Reflects (molecule 12 12) geometry f → ∀ root arm,
      read geometry (f root) (f arm) = read (mirror geometry) root arm)
    (invariant : ∀ root arm, read (mirror geometry) root arm = read geometry root arm) :
    ¬ read geometry 0 1 < read geometry 0 2 ∧ ¬ read geometry 0 2 < read geometry 0 1 := by
  rw [equal_mass_arm_values read equivariant invariant]
  exact ⟨lt_irrefl _, lt_irrefl _⟩

def descriptor? (m : RawMolecule) (g : Geometry) (p : List Nat) :
    Option LocalizedTetrahedralRSPseudoDescriptor := do
  let order ← IsotopePriority.order? m p
  caseFromMirror? (readback? g order) (readback? (mirror g) order)

/-- Constitutionally identical CH₂ ring arms acquire strict priority in
descending isotope mass. Moving the label to the opposite arm exchanges
their ranks, and equal masses restore the tie. -/
theorem root_order :
    saturatedWithHalogens (molecule 13 12) = true ∧
    IsotopePriority.order? (molecule 13 12) [0] = some [3,1,2,4] ∧
    IsotopePriority.order? (molecule 12 13) [0] = some [3,2,1,4] ∧
    IsotopePriority.order? (molecule 12 12) [0] = none := by
  refine ⟨?_,?_,?_,?_⟩ <;> decide +kernel

/-- Replace one hydrogen attached to the lighter ring carbon by fluorine. -/
def difluorinated : RawMolecule :=
  let m := molecule 13 12
  {m with atoms := m.atoms.set 7 (.aliphatic .F)}

/-- The fluorinated carbon outranks the heavier carbon. Their immediate
atomic numbers tie, then F on the lighter arm decides by Rule 1a before
the isotope masses can participate. -/
theorem constitution_precedes_isotope :
    saturatedWithHalogens difluorinated = true ∧
    atomicOrder? difluorinated [0] 1 = some [3,2,1,4] ∧
    IsotopePriority.order? difluorinated [0] = some [3,2,1,4] := by
  refine ⟨?_,?_,?_⟩ <;> decide +kernel

/-- The isotope creates an uppercase R center on the input coordinates. Each
of exchanging the two nuclides and reflecting the geometry changes it to S. -/
theorem root_letters :
    descriptor? (molecule 13 12) geometry [0] = some (.chiral .R) ∧
    descriptor? (molecule 13 12) (mirror geometry) [0] = some (.chiral .S) ∧
    descriptor? (molecule 12 13) geometry [0] = some (.chiral .S) := by
  refine ⟨?_,?_,?_⟩ <;> decide +kernel

/-- At the occurrence reached from fluorine, the highest-priority ligand
points back toward the original root. Both ring routes remain available for
the isotope comparison and the auxiliary reading is uppercase R. -/
theorem nonroot_assignment :
    IsotopePriority.order? (molecule 13 12) [3,0] = some [3,1,2,4] ∧
    descriptor? (molecule 13 12) geometry [3,0] = some (.chiral .R) := by
  constructor <;> decide +kernel

private theorem descriptor_of_order {m p order} (g : Geometry)
    (ranked : IsotopePriority.order? m p = some order) :
    descriptor? m g p = (readback? g order).map (.chiral ·) := by
  unfold descriptor?
  rw [ranked]
  change caseFromMirror? (readback? g order) (readback? (mirror g) order) = _
  rw [readback_mirror]
  cases raw : readback? g order with
  | none => rfl
  | some hand => exact caseFromMirror?_eq_swap hand

/-- For every choice of coordinates, both isotope assignments succeed exactly
when the same four ligand positions give a nonzero volume. Exchanging the
isotopes reverses that volume's letter. The incoming fluorine edge gives
the same result at the auxiliary occurrence as at the root. -/
theorem assignment_all_geometries (g : Geometry) :
    descriptor? (molecule 13 12) g [0] =
      (readback? g [3,1,2,4]).map (.chiral ·) ∧
    descriptor? (molecule 12 13) g [0] =
      (readback? g [3,1,2,4]).map (fun h => .chiral h.swap) ∧
    descriptor? (molecule 13 12) g [3,0] = descriptor? (molecule 13 12) g [0] := by
  rw [descriptor_of_order g root_order.2.1,descriptor_of_order g root_order.2.2.1,
    descriptor_of_order g nonroot_assignment.1,LocalizedMarkedTerminalGaugeSwap.readback_swap23 g 3 1 2 4]
  simp [Option.map_map,Function.comp_def]

end TetraStereo.Examples.RingIsotopeAssignment

assert_kernel_only TetraStereo.Examples.RingIsotopeAssignment.equal_mass_reflection
assert_kernel_only TetraStereo.Examples.RingIsotopeAssignment.equal_mass_arm_values
assert_kernel_only TetraStereo.Examples.RingIsotopeAssignment.equal_mass_no_strict_order
assert_kernel_only TetraStereo.Examples.RingIsotopeAssignment.root_order
assert_kernel_only TetraStereo.Examples.RingIsotopeAssignment.constitution_precedes_isotope
assert_kernel_only TetraStereo.Examples.RingIsotopeAssignment.root_letters
assert_kernel_only TetraStereo.Examples.RingIsotopeAssignment.nonroot_assignment
assert_kernel_only TetraStereo.Examples.RingIsotopeAssignment.assignment_all_geometries
