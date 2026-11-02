import TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture
import TetraStereo.OneCenter.MultiCenterDetection
import TetraStereo.KernelOnly
import TetraStereo.Examples.TwoReferenceSupport.FixtureInventory
import TetraStereo.Examples.TwoReferenceSupport.FixtureGeometry

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace FixtureMirror

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture

abbrev Input := FixtureInventory.Input
abbrev Atom := FixtureInventory.Atom
abbrev Graph := Input.moleculeGraph

/-- The source-index involution exchanging the two 15-atom arms. -/
def mirrorIndex (i : Fin 33) : Fin 33 :=
  if h : i.val < 3 then i
  else if h : i.val < 18 then ⟨i.val + 15, by omega⟩
  else ⟨i.val - 15, by omega⟩

theorem mirrorIndex_involutive (i : Fin 33) : mirrorIndex (mirrorIndex i) = i := by
  fin_cases i <;> decide +kernel

theorem mirrorIndex_injective : Function.Injective mirrorIndex := by
  intro i j h
  have h' := congrArg mirrorIndex h
  rw [mirrorIndex_involutive, mirrorIndex_involutive] at h'
  exact h'

theorem mirrorIndex_surjective : Function.Surjective mirrorIndex := by
  intro i
  exact ⟨mirrorIndex i, mirrorIndex_involutive i⟩

def mirrorIndexPerm : Equiv.Perm (Fin 33) :=
  { toFun := mirrorIndex
    invFun := mirrorIndex
    left_inv := mirrorIndex_involutive
    right_inv := mirrorIndex_involutive }

@[simp] theorem mirrorIndexPerm_apply (i : Fin 33) : mirrorIndexPerm i = mirrorIndex i := rfl

def atomIndex (a : Atom) : Fin 33 :=
  ⟨a.val, a.isLt⟩

@[simp] theorem atomIndex_fixtureAtom (i : Fin 33) : atomIndex (FixtureInventory.fixtureAtom i) = i := by
  apply Fin.ext
  rfl

def mirrorAtom (a : Atom) : Atom :=
  FixtureInventory.fixtureAtom (mirrorIndex (atomIndex a))

theorem mirrorAtom_involutive (a : Atom) : mirrorAtom (mirrorAtom a) = a := by
  apply Fin.ext
  simp [mirrorAtom, atomIndex]
  exact congrArg Fin.val (mirrorIndex_involutive (atomIndex a))

theorem mirrorAtom_injective : Function.Injective mirrorAtom := by
  intro a b h
  have h' := congrArg mirrorAtom h
  rw [mirrorAtom_involutive, mirrorAtom_involutive] at h'
  exact h'

theorem mirrorAtom_surjective : Function.Surjective mirrorAtom := by
  intro a
  exact ⟨mirrorAtom a, mirrorAtom_involutive a⟩

def mirrorPerm : Equiv.Perm Atom :=
  { toFun := mirrorAtom
    invFun := mirrorAtom
    left_inv := mirrorAtom_involutive
    right_inv := mirrorAtom_involutive }

@[simp] theorem mirrorPerm_apply (a : Atom) : mirrorPerm a = mirrorAtom a := rfl

theorem mirrorPerm_involutive (a : Atom) : mirrorPerm (mirrorPerm a) = a :=
  mirrorAtom_involutive a

/-- The arm exchange preserves all actual source labels and every actual bond order.  The graph is
the certified localized graph built from the fixture's own atom labels and interaction records. -/
theorem mirrorPerm_isAutomorphism : Graph.IsAutomorphism mirrorPerm := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    fin_cases a <;> decide +kernel
  · intro a
    fin_cases a <;> decide +kernel
  · intro a
    fin_cases a <;> decide +kernel
  · intro a b
    fin_cases a <;> fin_cases b <;> decide +kernel

def mirrorGraphAut : Graph.Aut := ⟨mirrorPerm, mirrorPerm_isAutomorphism⟩

/-- Detected centers are preserved by the generic theorem for every graph automorphism. -/
def mirrorDetectedAut : Input.detectedMultiCenterMolecule.Aut :=
  Graph.detectedMultiCenterAutOfGraphAut mirrorGraphAut

theorem mirrorDetectedAut_coe :
    (mirrorDetectedAut : Equiv.Perm Atom) = mirrorPerm := rfl

/-- The point reflection in the fixture's `x = 0` plane. -/
def reflectPoint (p : CartesianPoint3) : CartesianPoint3 :=
  { x := -p.x, y := p.y, z := p.z }

/-- Actual coordinate readback commutes with the source arm exchange and reflection. -/
theorem pointAt_mirror (i : Fin 33) :
    FixtureGeometry.pointAt (mirrorIndex i) =
      (FixtureGeometry.pointAt i).map reflectPoint := by
  simp only [FixtureGeometry.pointAt_eq_source_index]
  fin_cases i <;> decide +kernel

theorem spatialPointAt_mirror (i : Fin 33) :
    input.certified.spatialPointAt? (FixtureInventory.fixtureAtom (mirrorIndex i)) =
      (input.certified.spatialPointAt? (FixtureInventory.fixtureAtom i)).map reflectPoint := by
  change FixtureGeometry.pointAt (mirrorIndex i) =
    (FixtureGeometry.pointAt i).map reflectPoint
  exact pointAt_mirror i

end FixtureMirror

assert_kernel_only FixtureMirror.mirrorIndex_involutive
assert_kernel_only FixtureMirror.mirrorIndex_injective
assert_kernel_only FixtureMirror.mirrorIndex_surjective
assert_kernel_only FixtureMirror.mirrorAtom_involutive
assert_kernel_only FixtureMirror.mirrorAtom_injective
assert_kernel_only FixtureMirror.mirrorAtom_surjective
assert_kernel_only FixtureMirror.mirrorPerm_isAutomorphism
assert_kernel_only FixtureMirror.pointAt_mirror
assert_kernel_only FixtureMirror.spatialPointAt_mirror
