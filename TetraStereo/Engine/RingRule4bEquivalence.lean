import TetraStereo.Engine.RingRecursivePriorities

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.Recursive
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation

/-- A complete Rule 4b alternative. At each chiral occurrence the code records
whether its hand forms a like pair with this reference. It retains the prior
chemical observations, the parentage of every occurrence, and duplicates. -/
def pairCode? (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode)
    (facts : Facts) (ref : RS) : Option MarkedHierarchy.Code :=
  let role (p : List Nat) :=
    match (facts.lookup p).bind Reading.label with
    | none => 0
    | some (.chiral h) => if h = ref then 1 else 2
    | some (.pseudoasymmetric _) => 3
  MarkedHierarchy.encode m role [] (m.atomCount+1) arm

/-- Each side starts at a real, reached ligand in the original root's graph.
Its facts include all candidate carbon occurrences and a derivation for each. -/
structure ReferenceArm (m : RawMolecule) (g : Geometry) (path : List Nat) where
  node : RawMolecule.CanonicalBranchNode
  reached : occurrence? m path = some node
  facts : Facts
  complete : carbonSites m (m.atomCount+1) node = some (facts.map Prod.fst)
  supported : ∀ x ∈ facts, Supported m g x.1 x.2
  references : List RS
  selected : molecularReferences? m node facts false = some references
  codes : List MarkedHierarchy.Code
  interpreted : references.mapM (pairCode? m node facts) = some codes

/-- The permutation matches the full paired digraphs, allowing the R and S
alternatives to exchange places. -/
structure Rule4bTie (m : RawMolecule) (g : Geometry) (path : List Nat) where
  fragment : saturatedWithHalogens m = true
  frame : Frame
  depth : Nat
  incident : frameOK m path depth frame = true
  left : ReferenceArm m g (path ++ [frame.left])
  right : ReferenceArm m g (path ++ [frame.right])
  sameAlternatives : left.codes.Perm right.codes

theorem Rule4bTie.all_readings {m g p} (t : Rule4bTie m g p)
    {α : Type} (rank : MarkedHierarchy.Code → α) :
    (t.left.codes.map rank).Perm (t.right.codes.map rank) := t.sameAlternatives.map rank

private def referenceArm? (m : RawMolecule) (g : Geometry) (p : List Nat) (fs : Facts)
    (valid : ∀ x ∈ fs, Supported m g x.1 x.2) : Option (ReferenceArm m g p) := do
  let ⟨n,reach⟩ ← (occurrence? m p).attach
  if all : carbonSites m (m.atomCount+1) n = some (fs.map Prod.fst) then
    let ⟨refs,sel⟩ ← (molecularReferences? m n fs false).attach
    let ⟨codes,paired⟩ ← (refs.mapM (pairCode? m n fs)).attach
    return ⟨n,reach,fs,all,valid,refs,sel,codes,paired⟩
  else none

def verifyRule4bTie? (m : RawMolecule) (g : Geometry) (p : List Nat) (d : Nat)
    (f : Frame) (ls rs : Facts) (lh : ∀ x ∈ ls, Supported m g x.1 x.2)
    (rh : ∀ x ∈ rs, Supported m g x.1 x.2) : Option (Rule4bTie m g p) := do
  if frag : saturatedWithHalogens m = true then
    if ok : frameOK m p d f = true then
      let l ← referenceArm? m g (p ++ [f.left]) ls lh
      let r ← referenceArm? m g (p ++ [f.right]) rs rh
      if equal : l.codes.Perm r.codes then return ⟨frag,f,d,ok,l,r,equal⟩ else none
    else none
  else none

end TetraStereo.Engine.RingChemicalPriority.Recursive
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Recursive.Rule4bTie.all_readings
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Recursive.verifyRule4bTie?
