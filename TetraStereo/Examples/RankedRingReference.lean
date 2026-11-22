import TetraStereo.Engine.RingRecursivePriorities

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option Elab.async false

namespace TetraStereo.Examples.RankedRingReference
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open Engine.RingChemicalPriority Recursive

/-- Local indices in an arm start at its branching carbon. Its two oxygen
branches end in CH(F)Cl groups of opposite hand. The CH₂ branch leads to a
fluorinated methine and then to a fluorinated oxirane. -/
private def elements : List Element :=
  [.C,.O,.O,.C,.C,.C,.C,.C,.F,.Cl,.H,.F,.Cl,.H,.H,.H,.F,.H,.F,.O,.C,.H,.H]

private def connections : List (Nat × Nat) :=
  [(0,1),(0,2),(0,3),(1,4),(2,5),(3,6),(6,7),
   (4,8),(4,9),(4,10),(5,11),(5,12),(5,13),(3,14),(3,15),
   (6,16),(6,17),(7,18),(7,19),(7,20),(19,20),(20,21),(20,22)]

def molecule : RawMolecule where
  atoms := ([Element.C,.F,.H] ++ elements ++ elements).map AtomSpec.aliphatic
  bonds := (([(0,1),(0,2)] : List (Nat × Nat)) ++ [3,26].flatMap (fun offset =>
    (0,offset) :: connections.map (fun (a,b) => (offset+a,offset+b)))).map
    (fun (a,b) => ⟨a,b,.single⟩)

private def positions : List CartesianPoint3 :=
  [⟨4,-2,-2⟩,⟨5,0,-2⟩,⟨5,-2,0⟩,⟨6,-6,-6⟩,⟨6,1,-1⟩,⟨6,-1,1⟩,
   ⟨8,-7,-7⟩,⟨10,-6,-8⟩,⟨6,3,-1⟩,⟨6,1,1⟩,⟨7,0,-2⟩,
   ⟨6,-1,3⟩,⟨6,2,1⟩,⟨7,-3,0⟩,⟨6,-5,-7⟩,⟨6,-10,-8⟩,
   ⟨8,-6,-6⟩,⟨8,-10,-8⟩,⟨10,-4,-8⟩,⟨10,-6,-6⟩,⟨12,-7,-11⟩,⟨12,-5,-11⟩,⟨16,-11,-19⟩]

/-- Reflecting one arm exchanges its two upper CH(F)Cl readings. Exchanging
the terminal F and ring O positions in that same arm inverts its oxirane
center a second time. -/
def geometry : Geometry := fun i =>
  if i < 3 then ([⟨0,0,0⟩,⟨0,2,-1⟩,⟨0,-1,2⟩] : List CartesianPoint3)[i]?
  else if i < 26 then positions[i-3]?
  else
    let j := i-26
    let site := if j = 21 then some (⟨12,-7,-9⟩ : CartesianPoint3)
      else positions[if j = 18 then 19 else if j = 19 then 18 else j]?
    site.map CartesianPoint3.reflectX

/-- The right arm is now an exact reflection of the left, including the
oxirane center. Both arms have the same best Rule 4b reading. -/
def enantiomorphicGeometry : Geometry := fun i =>
  if i < 26 then geometry i else mirror geometry (i-23)

/-- Normalized barycentric weights in the four-neighbor tetrahedron. The
central F and H each carry 2/5, the two attached carbons each carry 1/10,
and each carbon within an arm is its four neighbors' centroid. -/
def ligandWeight (center ligand : Nat) : ℚ :=
  if center = 0 then (if ligand = 1 ∨ ligand = 2 then 2/5 else 1/10) else 1/4

def strictlyInside (g : Geometry) (i : Nat) : Prop :=
  let ns := molecule.writtenNeighbors i
  let w := ligandWeight i
  ns.length = 4 ∧ (readback? g ns).isSome = true ∧ (g i).isSome = true ∧
    (∀ j ∈ ns, 0 < w j) ∧ (ns.map w).sum = 1 ∧
    ∀ k : Fin 3,
      let coord (v : CartesianPoint3) := if k = 0 then v.x else if k = 1 then v.y else v.z
      (ns.mapM (fun j => (g j).map fun v => w j * coord v)).map List.sum = (g i).map coord

instance (g : Geometry) (i : Nat) : Decidable (strictlyInside g i) := by
  unfold strictlyInside
  infer_instance

/-- All carbon sites have a nonzero ligand volume and strictly positive
barycentric coordinates in both the supplied geometry and its reflection. -/
theorem carbon_frames_interior :
    molecule.atomCount = 49 ∧ ∀ i : Fin 49,
      (molecule.atoms[i.val]?).any (fun a => a.element == .C) = true →
        strictlyInside geometry i ∧ strictlyInside (mirror geometry) i := by
  decide +kernel

private def swapOArms (offset i : Nat) : Nat :=
  let pairs : List (Nat × Nat) := [(1,2),(4,5),(8,11),(9,12),(10,13)]
  if i < offset then i else
    ((pairs ++ pairs.map Prod.swap).lookup (i-offset)).map (offset+·) |>.getD i

private def exchangeArms (i : Nat) : Nat := if i < 3 then i else if i < 26 then i+23 else i-23

def hints : List Nat → Option Recursive.Frame
  | [0] => some ⟨.fourB,1,3,26,2,exchangeArms,false⟩
  | [0,i] => if i = 3 ∨ i = 26 then
      some ⟨.five,0,i+1,i+2,i+3,swapOArms i,true⟩ else none
  | _ => none

private def armFacts? (i : Nat) : Option (RawMolecule.CanonicalBranchNode × Facts) := do
  let arm ← occurrence? molecule [0,i]
  let paths ← carbonSites molecule (molecule.atomCount+1) arm
  let facts ← paths.mapM fun p => do
    let r ← derive molecule geometry hints (fun _ => 1) 2 p
    return (p,r.val)
  return (arm,facts)

private def armSummary (i : Nat) (reverse : Bool) :
    Option (List RS × Option (List RS) × List RS × List Nat × List Nat) := do
  let (arm,facts) ← armFacts? i
  let nearest ← (chiralSpheres facts reverse).find? (fun (row : List RS) => !row.isEmpty)
  let (refs,word) ← rankedArm? molecule arm facts reverse
  return (localizedRule4bReferencesFromPopulation nearest,
    molecularReferences? molecule arm facts reverse,refs,word.low.flatten,word.high.flatten)

/-- The O,O,CH₂ routes reach three chiral sites at equal distance. The two
sites reached through oxygen supply both references even though all three
sites counted together give a majority. Both reference-dependent rankings
are computed before the best complete word is chosen. -/
theorem competing_references :
    armSummary 3 false = some ([.S],none,[.R,.S],[1,0,1,0],[1,0,1,0]) ∧
    armSummary 26 false = some ([.R],none,[.R,.S],[1,0,1,1],[1,0,1,1]) ∧
    armSummary 3 true = some ([.R],none,[.R,.S],[1,0,1,0],[1,0,1,0]) ∧
    armSummary 26 true = some ([.S],none,[.R,.S],[1,0,1,1],[1,0,1,1]) := by
  refine ⟨?_,?_,?_,?_⟩ <;> decide +kernel

private def alternatives (i : Nat) (rev : Bool) :
    Option (List (List Nat) × List Nat × List Nat) := do
  let (arm,facts) ← armFacts? i
  let pop ← referencePopulation? molecule arm facts rev
  let r ← rankedRange? molecule arm facts rev .R
  let s ← rankedRange? molecule arm facts rev .S
  guard (r.low == r.high && s.low == s.high)
  return (pop.members.map Prod.fst,r.low.flatten,s.low.flatten)

/-- The two oxygen routes alone select the references. Exchanging geometry
exchanges which reference realizes the senior complete word on each arm. -/
theorem ranked_paths_and_alternatives :
    alternatives 3 false = some ([[0,3,4,7],[0,3,5,8]],[1,0,0,1],[1,0,1,0]) ∧
    alternatives 26 false = some ([[0,26,27,30],[0,26,28,31]],[1,0,1,1],[1,0,0,0]) ∧
    alternatives 3 true = some ([[0,3,4,7],[0,3,5,8]],[1,0,1,0],[1,0,0,1]) ∧
    alternatives 26 true = some ([[0,26,27,30],[0,26,28,31]],[1,0,0,0],[1,0,1,1]) := by
  refine ⟨?_,?_,?_,?_⟩ <;> decide +kernel

/-- The last oxirane pairing distinguishes the two arms. Their order is
preserved on reflection, giving an uppercase R at the central carbon. -/
theorem root_assignment :
    saturatedWithHalogens molecule = true ∧ Supported molecule geometry [0] ⟨.R,.S⟩ := by
  have h : (certifyHalogenated molecule geometry hints (fun _ => 1) 3 [0]).map Subtype.val =
      some ⟨.R,.S⟩ := by decide +kernel
  obtain ⟨r,_,eq⟩ := Option.map_eq_some_iff.mp h
  exact eq ▸ r.property

/-- Replacing a terminal Cl on the right by Br distinguishes the two
branching carbons only after traversing an oxygen and its attached methine.
The registry, bonds and all other atomic specifications are identical. -/
def brominated : RawMolecule := {molecule with atoms := molecule.atoms.set 35 (.aliphatic .Br)}

theorem deep_constitution :
    saturatedWithHalogens brominated = true ∧
    ligandRows? brominated [0] 3 2 = ligandRows? brominated [0] 26 2 ∧
    (ligandRows? brominated [0] 3 2).isSome = true ∧
    SiblingConstitution.compare? brominated [0,26] [0,3] = some .gt ∧
    SiblingConstitution.compare? molecule [0,26] [0,3] = some .eq ∧
    (SiblingConstitution.checked? molecule [10,22,23,10] [10,22,23,24]).map
      (fun c => (c.left.node.provenance,c.ordering)) = some (.ringDuplicate 0,.gt) ∧
    SiblingConstitution.compare? molecule [0,3,4] [0,26,27] = none := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

/-- A remote constitutional difference between same-element parents fixes
the order of their two descendant auxiliary occurrences. -/
theorem inherited_constitution :
    ((occurrence? brominated [1,0]).map (fun arm =>
      branchPrecedes brominated arm [] false none ([1,0,26,27,30],.S) ([1,0,3,4,7],.R))) =
      some true := by decide +kernel

end TetraStereo.Examples.RankedRingReference
assert_kernel_only TetraStereo.Examples.RankedRingReference.carbon_frames_interior
assert_kernel_only TetraStereo.Examples.RankedRingReference.competing_references
assert_kernel_only TetraStereo.Examples.RankedRingReference.root_assignment
assert_kernel_only TetraStereo.Examples.RankedRingReference.ranked_paths_and_alternatives
assert_kernel_only TetraStereo.Examples.RankedRingReference.deep_constitution
assert_kernel_only TetraStereo.Examples.RankedRingReference.inherited_constitution
