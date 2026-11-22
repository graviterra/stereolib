import TetraStereo.Examples.BlueBookHexachlorocyclohexane

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
namespace TetraStereo.Examples.HexachlorocyclohexaneFamily
open OneCenter LocalizedGenericMarkedRecalculation CertifiedLocalizedCIPInput
open Engine.RingChemicalPriority Recursive BlueBookHexachlorocyclohexane

/-- Read the four physical ligand points in the same cyclic convention at
every carbon. Ring direction is fixed even before a CIP priority is assigned. -/
def fixedFrame (c : Nat) := [c+6,(c+5)%6,(c+1)%6,c+12]
private def exchanged (c : Nat) := [c+6,(c+1)%6,(c+5)%6,c+12]
def forwardSite (i : Fin 6) (k : Fin 5) := site i true (k.val+1)

private def back (k : Fin 5) : Fin 5 := ⟨4-k.val,by omega⟩
private theorem frames (i : Fin 6) (k : Fin 5) :
    order i true k = fixedFrame (forwardSite i k) ∧
    order i false k = exchanged (forwardSite i (back k)) := by
  fin_cases i <;> fin_cases k <;> decide +kernel

/-- A local profile records the five other physical hands encountered
clockwise from the focus. The hand of the focus is read separately. -/
def hand (p : Fin 32) (k : Fin 5) : RS := if p.val.testBit k.val then .R else .S

def directionHand (p : Fin 32) (cw : Bool) (k : Fin 5) :=
  if cw then hand p k else (hand p (back k)).swap

def pairWord (p : Fin 32) (cw : Bool) : List Nat :=
  (List.finRange 5).map fun k => (directionHand p cw k == directionHand p cw 0).toNat

def palindrome (p : Fin 32) := hand p 0 == hand p 4 && hand p 1 == hand p 3

theorem pair_words_tie_iff (p : Fin 32) :
    pairWord p true = pairWord p false ↔ palindrome p = true := by
  fin_cases p <;> decide +kernel

def clockwiseWins (p : Fin 32) : Bool :=
  if palindrome p then hand p 0 == .R else decide (pairWord p false < pairWord p true)

def mirrorWins (p : Fin 32) := if palindrome p then !(clockwiseWins p) else clockwiseWins p

def reading (p : Fin 32) (h : RS) : Reading :=
  let actual := if clockwiseWins p then h.swap else h
  ⟨actual,if palindrome p then actual else actual.swap⟩

theorem exact_case (p : Fin 32) (h : RS) :
    (reading p h).label = some (if palindrome p then
      .pseudoasymmetric (pseudoRSOfRS (reading p h).actual) else .chiral (reading p h).actual) := by
  cases hp : palindrome p <;> cases hw : clockwiseWins p <;> cases h <;> simp [reading,hp,hw,Reading.label,caseFromMirror?,pseudoRSOfRS,RS.swap]

def rootFrame (i : Fin 6) (p : Fin 32) : Recursive.Frame :=
  ⟨if palindrome p then .five else .fourB,i.val+6,(i.val+1)%6,(i.val+5)%6,i.val+12,exchange i.val,false⟩

def armFacts (i : Fin 6) (p : Fin 32) (cw : Bool) : Facts :=
  (List.finRange 5).map fun k =>
    let h := directionHand p cw k
    (path i cw k,⟨h,h.swap⟩)

def priorityCheck (i : Fin 6) (p : Fin 32) : Prop :=
  (priorityStep? molecule [i.val] 0 (rootFrame i p) (armFacts i p true)
    (armFacts i p false)).map Subtype.val = some (clockwiseWins p,mirrorWins p)

instance (i : Fin 6) (p : Fin 32) : Decidable (priorityCheck i p) :=
  inferInstanceAs (Decidable (_ = _))

private theorem exchanged_read (g : Geometry) (c : Nat) :
    readback? g (exchanged c) = (readback? g (fixedFrame c)).map RS.swap :=
  LocalizedMarkedTerminalGaugeSwap.readback_swap23 g _ _ _ _

private theorem local_aux {g : Geometry} {i : Fin 6} {p : Fin 32}
    (hh : ∀ k, readback? g (fixedFrame (forwardSite i k)) = some (hand p k))
    (cw : Bool) (k : Fin 5) :
    Supported molecule g (path i cw k) ⟨directionHand p cw k,(directionHand p cw k).swap⟩ := by
  apply auxiliary_of_geometry
  cases cw with
  | false => simp [geometric,(frames i k).2,readback_mirror,exchanged_read,hh,directionHand]
  | true => simp [geometric,(frames i k).1,readback_mirror,hh,directionHand]

private theorem local_facts {g : Geometry} {i : Fin 6} {p : Fin 32}
    (hh : ∀ k, readback? g (fixedFrame (forwardSite i k)) = some (hand p k))
    (cw : Bool) : ∀ x ∈ armFacts i p cw, Supported molecule g x.1 x.2 := by
  intro x hx
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx
  exact local_aux hh cw k

private theorem root_read {g : Geometry} {i : Fin 6} {p : Fin 32} {h : RS}
    (hr : readback? g (fixedFrame i.val) = some h) :
    geometric g ((rootFrame i p).order (clockwiseWins p)) ((rootFrame i p).order (mirrorWins p)) =
      some (reading p h) := by
  have ex := exchanged_read g i.val
  rw [hr] at ex
  unfold fixedFrame at hr
  unfold exchanged at ex
  cases hp : palindrome p <;> cases hw : clockwiseWins p <;> cases h <;>
    simp [geometric,rootFrame,Recursive.Frame.order,mirrorWins,reading,readback_mirror,hp,hw,hr,ex,RS.swap]

theorem supported_at {g : Geometry} {i : Fin 6} {p : Fin 32} {h : RS}
    (valid : priorityCheck i p) (hr : readback? g (fixedFrame i.val) = some h)
    (hh : ∀ k, readback? g (fixedFrame (forwardSite i k)) = some (hand p k)) :
    Supported molecule g [i.val] (reading p h) :=
  supported_of_priorities valid (local_facts hh true) (local_facts hh false) (root_read hr)

end TetraStereo.Examples.HexachlorocyclohexaneFamily
