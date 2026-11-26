import TetraStereo.Engine.RingFullPathPairs
import TetraStereo.Engine.RingPairAlternatives

/-! Figure 8 source hierarchy test, not a raw-molecule public replay.

The local authors' compounds_3d.sdf VS262 record has 94 atoms / 93 bonds.
Source SDF SHA-256: 28a000b36506dabe5a45f6d7672451c61c6e34f3e0f027f2599000d850273325.
Its central C27 reaches arm A via C87,C24,N10 and B via C89,C29,N31
(one-based source atom numbers). Figure 8 fixes each arm's main order by
Rule 4a: pseudoasymmetric C1 / C44 precede nonstereogenic C14 / C35.
Only the two chiral children of C1 / C44 can exchange order with the
reference. The source drawing, not production ranking, supplies that
through-4a hierarchy and its auxiliary hands. This test uses the production
legal-order sorter on this reduced hierarchy and checks atom order first.
It does not prove the hierarchy or hands from the molecular geometry.
-/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open TetraStereo.Engine
namespace HansonFigureEight

structure Hit where
  atom : Nat
  -- 2 = the branch containing source pseudoasymmetric center; 1 = ns.
  prior : Nat
  -- True means S in the source auxiliary drawing.
  isS : Bool
  deriving DecidableEq, Repr

def aNear : List Hit := [⟨7,2,true⟩,⟨11,1,false⟩]
def aFar : List Hit := [⟨20,2,true⟩,⟨3,2,false⟩,⟨16,1,false⟩,⟨58,1,false⟩]
def bNear : List Hit := [⟨41,2,false⟩,⟨32,1,true⟩]
def bFar : List Hit := [⟨46,2,true⟩,⟨54,2,false⟩,⟨37,1,false⟩,⟨50,1,false⟩]

-- The strict earlier-rule path rank precedes the current reference bit.
-- Suppressed equal path entries cannot affect this reduced comparison.
def key (seedS : Bool) (x : Hit) : Nat :=
  2 * x.prior + (x.isS == seedS).toNat
def ranked (seedS : Bool) (near far : List Hit) : List Hit :=
  RingStereoSiblingPass.order (key seedS) near ++
  RingStereoSiblingPass.order (key seedS) far

def atoms (seedS : Bool) (near far : List Hit) := (ranked seedS near far).map Hit.atom
def bits (seedS : Bool) (near far : List Hit) :=
  (ranked seedS near far).map fun x => (x.isS == seedS).toNat
def score (xs : List Nat) := xs.foldl (fun n b => 2*n+b) 0

-- These assertions catch reordering of the main branches and swapping the
-- wrong deeper pair; asserting just the four integer scores would not.
theorem source_atom_orders :
    atoms true aNear aFar = [7,11,20,3,16,58] ∧
    atoms false aNear aFar = [7,11,3,20,16,58] ∧
    atoms true bNear bFar = [41,32,46,54,37,50] ∧
    atoms false bNear bFar = [41,32,54,46,37,50] := by
  simp [atoms, ranked, RingStereoSiblingPass.order, key, aNear, aFar, bNear, bFar, List.mergeSort, List.merge]

theorem source_words :
    bits true aNear aFar = [1,0,1,0,0,0] ∧
    bits false aNear aFar = [0,1,1,0,1,1] ∧
    bits true bNear bFar = [0,1,1,0,0,0] ∧
    bits false bNear bFar = [1,0,1,0,1,1] := by
  simp [bits, ranked, RingStereoSiblingPass.order, key, aNear, aFar, bNear, bFar, List.mergeSort, List.merge]

theorem scores_and_winner :
    score (bits true aNear aFar) = 40 ∧ score (bits false aNear aFar) = 27 ∧
    score (bits true bNear bFar) = 24 ∧ score (bits false bNear bFar) = 43 ∧
    max (score (bits true aNear aFar)) (score (bits false aNear aFar)) <
      max (score (bits true bNear bFar)) (score (bits false bNear bFar)) := by
  simp [bits, ranked, RingStereoSiblingPass.order, key, aNear, aFar, bNear, bFar, score, List.mergeSort, List.merge]

end HansonFigureEight
assert_kernel_only HansonFigureEight.source_atom_orders
assert_kernel_only HansonFigureEight.source_words
assert_kernel_only HansonFigureEight.scores_and_winner

def main : IO Unit := IO.println "Figure 8: checked source hierarchy atom orders; A=(40,27), B=(24,43), B wins. Raw geometry-to-hierarchy derivation remains open."
