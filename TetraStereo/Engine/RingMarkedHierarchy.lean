import TetraStereo.Engine.RingChemicalPriority

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.MarkedHierarchy
open OneCenter CertifiedLocalizedCIPInput

/-- Observations through Rule 4a in the neutral single-bonded fragment.
The selected occurrence is distinguished from every other visit to its atom. -/
structure Observation where
  nuclearCharge : Nat
  isotope : Option Nat
  provenance : Nat
  originalDistance : Nat
  unitClass : Nat
  selected : Bool
  deriving DecidableEq, Repr

inductive Code where
  | atom (value : Observation)
  | nil
  | cons (head tail : Code)
  deriving DecidableEq, Repr

private def pack (xs : List Code) := xs.foldr Code.cons .nil

private theorem pack_injective : Function.Injective pack := by
  intro a
  induction a with
  | nil => intro b h; cases b <;> simp_all [pack]
  | cons x xs ih =>
    intro b h
    cases b with
    | nil => contradiction
    | cons y ys =>
      obtain ⟨rfl,t⟩ := Code.cons.inj h
      exact congrArg (List.cons x) (ih t)

/-- A structural numeric word used solely to sort siblings. The equality
certificate below always compares the full trees and all observation fields. -/
private def tokens : Code → List Nat
  | .nil => [0]
  | .atom o => [1,o.nuclearCharge,(o.isotope.map Nat.succ).getD 0,o.provenance,
      o.originalDistance,o.unitClass,o.selected.toNat]
  | .cons a b => 2 :: (tokens a ++ tokens b)

def node (o : Observation) (children : List Code) :=
  Code.cons (.atom o) (pack (children.insertionSort (fun a b => tokens a ≤ tokens b)))

/-- Equality of marked codes preserves the actual observation and a bijective
matching of child codes, with multiplicities, at every visited node. -/
theorem same_node {o p a b} (same : node o a = node p b) : o = p ∧ a.Perm b := by
  obtain ⟨oh,ch⟩ := Code.cons.inj same
  have eq := pack_injective ch
  exact ⟨Code.atom.inj oh,(List.perm_insertionSort _ a).symm.trans (eq ▸ List.perm_insertionSort _ b)⟩

private def origin : RawMolecule.CanonicalNodeProvenance → Nat × Nat
  | .realAtom => (0,0)
  | .multipleBondDuplicate d => (1,d)
  | .ringDuplicate d => (2,d)
  | .phantom d => (3,d)

/-- Construct the complete pointed arm without cutting off a populated sphere.
Every ring duplicate retains the distance of its corresponding real atom. -/
def encode (m : RawMolecule) (classAt : List Nat → Nat) (selected : List Nat) :
    Nat → RawMolecule.CanonicalBranchNode → Option Code
  | 0,_ => none
  | fuel+1,n => do
    let atom ← m.atoms[n.atom]?
    let children ← (m.canonicalChildren n).mapM (encode m classAt selected fuel)
    let p := n.history.reverse
    let (kind,distance) := origin n.provenance
    return node ⟨atom.element.atomicNumber,atom.isotope?,kind,distance,classAt p,p == selected⟩ children

/-- The marked molecular observation at an actual digraph occurrence. -/
def observe? (m : RawMolecule) (unit : List Nat → Nat) (selected : List Nat)
    (n : RawMolecule.CanonicalBranchNode) : Option Observation := do
  let atom ← m.atoms[n.atom]?
  let (kind,d) := origin n.provenance
  let path := n.history.reverse
  return ⟨atom.element.atomicNumber,atom.isotope?,kind,d,unit path,path == selected⟩

/-- Structural isomorphism of two molecular arms with their selected
occurrences. At each matched node there is a bijection of its actual child
list, with multiplicities, followed by the same comparison recursively. -/
def Isomorphic (m n : RawMolecule) (u v : List Nat → Nat) (p q : List Nat) :
    Nat → RawMolecule.CanonicalBranchNode → RawMolecule.CanonicalBranchNode → Prop
  | 0,_,_ => False
  | d+1,a,b => ∃ observation, observe? m u p a = some observation ∧
      observe? n v q b = some observation ∧ ∃ right, right.Perm (n.canonicalChildren b) ∧
      List.Forall₂ (Isomorphic m n u v p q d) (m.canonicalChildren a) right

private theorem mapped_sites {α β : Type} (f : α → Option β) {xs ys}
    (ok : xs.mapM f = some ys) : List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => simp at ok; subst ys; exact .nil
  | cons x xs ih =>
    cases h : f x with
    | none => simp [List.mapM_cons,h] at ok
    | some y =>
      cases tl : xs.mapM f with
      | none => simp [List.mapM_cons,h,tl] at ok
      | some rest =>
        simp [List.mapM_cons,h,tl] at ok
        subst ys
        exact .cons h (ih tl)

private theorem join_sites {α β γ : Type} {L : α → β → Prop} {R : β → γ → Prop} {S : α → γ → Prop}
    (join : ∀ a b c, L a b → R b c → S a c) {x y z}
    (left : List.Forall₂ L x y) (right : List.Forall₂ R y z) : List.Forall₂ S x z := by
  induction left generalizing z with
  | nil => cases right; exact .nil
  | cons a _ ih => cases right with | cons b tail => exact .cons (join _ _ _ a b) (ih tail)

private theorem open_node {m u p d a c} (found : encode m u p (d+1) a = some c) :
    ∃ o cs, observe? m u p a = some o ∧
      List.Forall₂ (fun x y => encode m u p d x = some y) (m.canonicalChildren a) cs ∧
      node o cs = c := by
  cases atom : m.atoms[a.atom]? with
  | none => simp [encode,atom] at found
  | some spec =>
    cases children : (m.canonicalChildren a).mapM (encode m u p d) with
    | none => simp [encode,atom,children] at found
    | some cs =>
      let o : Observation := ⟨spec.element.atomicNumber,spec.isotope?,(origin a.provenance).1,
        (origin a.provenance).2,u a.history.reverse,a.history.reverse == p⟩
      refine ⟨o,cs,by simp [observe?,atom,o],mapped_sites _ children,?_⟩
      simpa [encode,atom,children] using found

/-- Equality of computed codes yields an isomorphism between the original
occurrence trees. No traversal order or proposed atom renaming is required. -/
theorem isomorphic_of_code {m n u v p q d a b c}
    (left : encode m u p d a = some c) (right : encode n v q d b = some c) :
    Isomorphic m n u v p q d a b := by
  induction d generalizing a b c with
  | zero => contradiction
  | succ d ih =>
    obtain ⟨o,ls,ol,lcs,lc⟩ := open_node left
    obtain ⟨w,rs,wr,rcs,rc⟩ := open_node right
    obtain ⟨rfl,perm⟩ := same_node (lc.trans rc.symm)
    have back : List.Forall₂ (fun k t => encode n v q d t = some k) rs (n.canonicalChildren b) :=
      rcs.flip
    obtain ⟨reordered,lookup,complete⟩ := List.perm_comp_forall₂ perm back
    exact ⟨_,ol,wr,reordered,complete,join_sites (fun a c b x y => ih (a := a) (b := b) (c := c) x y) lcs lookup⟩

end TetraStereo.Engine.RingChemicalPriority.MarkedHierarchy
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.MarkedHierarchy.same_node
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.MarkedHierarchy.isomorphic_of_code
