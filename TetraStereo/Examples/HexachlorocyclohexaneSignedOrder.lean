import TetraStereo.Examples.HexachlorocyclohexaneClassification
import TetraStereo.Engine.RingBinaryPairScore
import TetraStereo.Engine.RingFullPathPublication

/-! Complete signed-word algebra for the five successive chiral donors on
each ring arm of 1,2,3,4,5,6-hexachlorocyclohexane. -/
set_option autoImplicit false
namespace TetraStereo.Examples.HexachlorocyclohexaneSignedOrder
open OneCenter Engine LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)
open RingFullPathEligibility (Key)
open RingFullPathTrialReadings (trialKey bitWord)
open HexachlorocyclohexaneFamily (directionHand palindrome clockwiseWins mirrorWins reading)
attribute [local instance] lexOrd

def signedWord (p : Fin 32) (cw rev : Bool) (seed : RS) : List Bool :=
  (List.finRange 5).map fun k => (if rev then (directionHand p cw k).swap else directionHand p cw k) == seed

def best (p : Fin 32) (cw rev : Bool) :=
  max (signedWord p cw rev .R) (signedWord p cw rev .S)

/-- The first emitting hand selects the better reference for any nonempty
sequence: the word beginning in true precedes either possible suffix. -/
theorem best_seed (h : RS) (tail : List RS) :
    max ((h::tail).map (· == RS.R)) ((h::tail).map (· == RS.S)) =
      (h::tail).map (· == h) := by
  cases h
  · apply max_eq_left
    apply le_of_lt
    exact List.Lex.rel (by decide : false < true)
  · apply max_eq_right
    apply le_of_lt
    exact List.Lex.rel (by decide : false < true)

def winner (p : Fin 32) (rev : Bool) := if rev then mirrorWins p else clockwiseWins p

def direction (p : Fin 32) (rev : Bool) : Ordering := if winner p rev then .gt else .lt

inductive Rule where | fourB | five deriving Repr, DecidableEq

def rule (p : Fin 32) : Rule := if palindrome p then .five else .fourB

/-- Zero-based donor index along the two arms. -/
def position (p : Fin 32) : Fin 5 :=
  if palindrome p then 0 else if (best p true false)[1]? = (best p false false)[1]? then 2 else 1

def decidingWord (p : Fin 32) (cw rev : Bool) :=
  if palindrome p then signedWord p cw rev .R else best p cw rev

/-- The Rule 4b word is the first-donor-relative recursive pair word even
on the mirrored geometry. Rule 4b ties precisely on palindromic profiles. -/
theorem best_profile (p : Fin 32) (cw rev : Bool) :
    (best p cw rev).map Bool.toNat = HexachlorocyclohexaneFamily.pairWord p cw := by
  fin_cases p <;> cases cw <;> cases rev <;> decide +kernel

theorem directions (p : Fin 32) (rev : Bool) :
    compare (best p true rev) (best p false rev) =
      (if palindrome p then .eq else direction p rev) ∧
    (palindrome p = true →
      compare (signedWord p true rev .R) (signedWord p false rev .R) = direction p rev ∧
      RingOccurrenceStereo.fixedScore
        (compare (signedWord p true rev .R) (signedWord p false rev .R))
        (compare (signedWord p true rev .S) (signedWord p false rev .S)) =
          (if winner p rev then (2 : Int) else -2)) := by
  fin_cases p <;> cases rev <;> decide +kernel

theorem first_difference (p : Fin 32) (rev : Bool) :
    (∀ k : Fin 5, k < position p → (decidingWord p true rev)[k.val]? = (decidingWord p false rev)[k.val]?) ∧
    (decidingWord p true rev)[(position p).val]? = some (winner p rev) ∧
    (decidingWord p false rev)[(position p).val]? = some (!(winner p rev)) := by
  fin_cases p <;> cases rev <;> decide +kernel

theorem distribution :
    ((List.finRange 32).filter (fun p => rule p == .five)).length = 8 ∧
    ((List.finRange 32).filter (fun p => position p == 0)).length = 8 ∧
    ((List.finRange 32).filter (fun p => position p == 1)).length = 16 ∧
    ((List.finRange 32).filter (fun p => position p == 2)).length = 8 := by
  decide +kernel

/-- At the promoted or ordinary stage, projecting the two legal reference
words and the fixed R word determines both native fields. -/
theorem fields {i : Input} {r : Reader i} {q : Arm i} {k : Key} (p : Fin 32) (cw rev : Bool)
    (got : RingFullPathEligibility.key? i r rev q = some k)
    (fourB : ∀ seed, RingFullPathPairs.stageWords i r rev [] seed q = some (signedWord p cw rev seed))
    (five : RingFullPathPairs.stageWords i r rev [.lowercase] .R q = some (signedWord p cw rev .R)) :
    k.bestFourB = best p cw rev ∧ k.fixedR = signedWord p cw rev .R := by
  unfold RingFullPathEligibility.key? at got
  simp only [RingFullPathPairs.pairs?,RingFullPathRule5.word?,fourB,five] at got
  cases u : RingRetainedStereoRefinement.priority i r rev [] q <;>
    cases l : RingRetainedStereoRefinement.priority i r rev [.lowercase] q <;> simp [u,l] at got
  subst k
  exact ⟨rfl,rfl⟩

/-- After the equal constitutional, Rule 4a and Rule 4c fields, the order
is strict on every profile, even with arbitrary nominated-atom words. -/
theorem trial_order (p : Fin 32) (rev : Bool) (x y : Key)
    (prior : x.throughFourA = y.throughFourA) (lower : x.fourC = y.fourC)
    (cw : x.bestFourB = best p true rev ∧ x.fixedR = signedWord p true rev .R)
    (ccw : y.bestFourB = best p false rev ∧ y.fixedR = signedWord p false rev .R)
    (m n : RingRetainedChemicalTrace.Word) :
    compare (trialKey x m) (trialKey y n) = direction p rev := by
  obtain ⟨a,b⟩ := directions p rev
  simp only [trialKey,prior,lower,cw.1,cw.2,ccw.1,ccw.2,List.compare_cons_cons,
    RingBinaryPairScore.compare_bits,Std.ReflOrd.compare_self,a]
  cases hp : palindrome p <;> cases hw : winner p rev <;> simp_all [direction]

/-- Complete order from the molecular projections, with no premise on either
signed field of the accepted keys. -/
theorem trial_from_words {i : Input} {r : Reader i} (p : Fin 32) (rev : Bool)
    (q : Bool → Arm i) (k : Bool → Key)
    (got : ∀ cw, RingFullPathEligibility.key? i r rev (q cw) = some (k cw))
    (prior : (k true).throughFourA = (k false).throughFourA)
    (lower : (k true).fourC = (k false).fourC)
    (fourB : ∀ cw seed, RingFullPathPairs.stageWords i r rev [] seed (q cw) = some (signedWord p cw rev seed))
    (five : ∀ cw, RingFullPathPairs.stageWords i r rev [.lowercase] .R (q cw) = some (signedWord p cw rev .R))
    (m n : RingRetainedChemicalTrace.Word) :
    compare (trialKey (k true) m) (trialKey (k false) n) = direction p rev :=
  trial_order p rev _ _ prior lower (fields p true rev (got _) (fourB _) (five _))
    (fields p false rev (got _) (fourB _) (five _)) m n

/-- Compute the winning direction directly from the two native signed fields. -/
def nativeWins (p : Fin 32) (rev : Bool) : Bool :=
  ((compare (best p true rev) (best p false rev)).then
    (compare (signedWord p true rev .R) (signedWord p false rev .R))) == .gt

theorem nativeWins_eq (p : Fin 32) (rev : Bool) : nativeWins p rev = winner p rev := by
  obtain ⟨a,b⟩ := directions p rev
  cases hp : palindrome p <;> cases hw : winner p rev <;> simp_all [nativeWins,direction]

/-- The recursive molecular calculation at every one of the six roots gives
exactly the winner pair read independently from the native signed fields. -/
theorem recursive_agreement (i : Fin 6) (p : Fin 32) :
    (RingChemicalPriority.Recursive.priorityStep? BlueBookHexachlorocyclohexane.molecule [i.val] 0
      (HexachlorocyclohexaneFamily.rootFrame i p) (HexachlorocyclohexaneFamily.armFacts i p true)
      (HexachlorocyclohexaneFamily.armFacts i p false)).map Subtype.val =
      some (nativeWins p false,nativeWins p true) := by
  rw [nativeWins_eq,nativeWins_eq]
  exact HexachlorocyclohexaneFamily.all_priorities i p

/-- The actual and mirror singleton ballots reproduce the recursive label:
eight palindromes are pseudoasymmetric and the other 24 profiles chiral. -/
def ballot (p : Fin 32) (near : RS) (rev : Bool) : RS :=
  let localHand := if rev then near.swap else near
  if winner p rev then localHand.swap else localHand

theorem ballots (p : Fin 32) (near : RS) :
    ballot p near false = (reading p near).actual ∧
    ballot p near true = (reading p near).reflected ∧
    RingFullPathPublication.crossed [some (ballot p near false)] [some (ballot p near true)] =
      some (RingNestedActivePair.label (reading p near).actual (reading p near).reflected,
        RingNestedActivePair.label (reading p near).reflected (reading p near).actual) ∧
    (reading p near).label = some (if palindrome p then
      .pseudoasymmetric (pseudoRSOfRS (ballot p near false)) else .chiral (ballot p near false)) := by
  cases pal : palindrome p <;> cases wins : clockwiseWins p <;> cases near <;>
    simp [ballot,winner,mirrorWins,reading,pal,wins,RingChemicalPriority.Recursive.Reading.label,
      caseFromMirror?,pseudoRSOfRS,RS.swap] <;> decide +kernel

end TetraStereo.Examples.HexachlorocyclohexaneSignedOrder
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexaneSignedOrder.first_difference
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexaneSignedOrder.trial_order
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexaneSignedOrder.ballots
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexaneSignedOrder.recursive_agreement
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexaneSignedOrder.trial_from_words
