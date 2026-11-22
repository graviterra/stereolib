import TetraStereo.Engine.RingChemicalPriority

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation

/-- A finite graph symmetry realized by spatial reflection. Atom identity,
isotope, charge and every bond order are transported on the complete graph. -/
structure Reflects (m : RawMolecule) (g : Geometry) (p : Nat → Nat) : Prop where
  atoms : ∀ i : Fin m.atomCount, p i < m.atomCount ∧ p (p i) = i ∧ (g i).isSome = true ∧
    m.atoms[p i]? = m.atoms[i.val]? ∧ g (p i) = mirror g i
  bonds : ∀ i j : Fin m.atomCount, m.bondOrder (p i) (p j) = m.bondOrder i j

/-- Reflection-invariant observations on pointed ligands tie when this symmetry
fixes the root and takes one ligand to the other. These are the two obligations
for any interpretation of Rules 1–4 under P-92.1.3: molecular equivariance
and reflection invariance. -/
theorem earlier_rules_tie {α : Type} {m : RawMolecule} {g : Geometry} {p : Nat → Nat}
    (symmetry : Reflects m g p) (read : Geometry → Nat → Nat → α)
    (equivariant : ∀ f, Reflects m g f → ∀ root arm,
      read g (f root) (f arm) = read (mirror g) root arm)
    (invariant : ∀ root arm, read (mirror g) root arm = read g root arm)
    {root a b : Nat} (fixed : p root = root) (exchanged : p a = b) :
    read g root a = read g root b := by
  simpa [fixed,exchanged] using ((equivariant p symmetry root a).trans (invariant root a)).symm

/-- The tetrahedral C/H/O single-bond fragment: every H has one bond, O two,
and C four. Grouping identical terminal H ligands below uses the actual isotope. -/
private def saturated (terminalHalogens : Bool) (m : RawMolecule) : Bool :=
  m.admissible? && m.bonds.all (fun b => b.kind.order == 1 && b.kind != .aromatic) &&
  (List.range m.atomCount).all fun i =>
    let ns := m.writtenNeighbors i
    let bonded := ({m with neighborOrder := []} : RawMolecule).writtenNeighbors i
    decide (ns.Perm bonded) && (m.atoms[i]?).any fun a =>
      a.charge == 0 && !a.aromatic && a.explicitHydrogens == 0 && decide ns.Nodup &&
      match a.element with
      | .H => ns.length == 1
      | .F | .Cl | .Br | .I => terminalHalogens && ns.length == 1
      | .O => ns.length == 2
      | .C => ns.length == 4
      | _ => false

def saturatedCHO := saturated false

/-- Neutral C/H/O compounds with optional terminal monovalent halogens.
Only tetrahedral carbons can supply a stereogenic occurrence here. -/
def saturatedWithHalogens := saturated true

private def sameTerminalHydrogens (m : RawMolecule) (c : RawMolecule.CanonicalBranchNode) : Bool :=
  let ns := occurrenceLigandCursors m c
  ns.any fun a => ns.any fun b =>
    a.node.atom != b.node.atom && !a.node.forcedLeaf && !b.node.forcedLeaf &&
    (m.atoms[a.node.atom]?).any (fun x => x.element == .H && m.atoms[b.node.atom]? == some x)

/-- Exhaust the original branch. Every real C must have two identical H
ligands or appear in the returned list of candidate occurrences. Duplicate
nodes terminate. A depleted depth rejects even if all sites visited so far tie. -/
def carbonSites (m : RawMolecule) :
    Nat → RawMolecule.CanonicalBranchNode → Option (List (List Nat))
  | 0,_ => none
  | n+1,c => do
    if c.forcedLeaf then return []
    let atom ← m.atoms[c.atom]?
    let rest ← (m.canonicalChildren c).mapM (carbonSites m n)
    let here := if atom.element == .C && !sameTerminalHydrogens m c then [c.history.reverse] else []
    return here ++ rest.flatten

def singleSite? (m : RawMolecule) (root arm : Nat) : Option (List Nat) := do
  let start ← occurrence? m [root,arm]
  let [path] ← carbonSites m (m.atomCount + 1) start | none
  return path

/-- One node of the complete branch inventory before Rule 5. The complete
address retains parentage and the provenance retains the origin of duplicates.
For a singleton chiral auxiliary, Rule 4b has no second descriptor to pair;
Rule 4c has no lowercase descriptor to compare. -/
structure EarlierSite where
  address : List Nat
  atom : AtomSpec
  provenance : RawMolecule.CanonicalNodeProvenance
  chiralAuxiliary : Bool
  deriving DecidableEq

def earlierSites (m : RawMolecule) (aux : List Nat) :
    Nat → RawMolecule.CanonicalBranchNode → Option (List EarlierSite)
  | 0,_ => none
  | n+1,c => do
    let atom ← m.atoms[c.atom]?
    let children ← (m.canonicalChildren c).mapM (earlierSites m aux n)
    let address := c.history.reverse
    return ⟨address,atom,c.provenance,address == aux⟩ :: children.flatten

def EarlierSite.rename (p : Nat → Nat) (a : EarlierSite) : EarlierSite :=
  {a with address := a.address.map p}

/-- Constitutional and stereogenic-unit observations at an addressed node.
Duplicate provenance includes its original distance. Isotope data retain the
element, including when a mass number was omitted. -/
inductive EarlierRule where
  | nuclearCharge | duplicate | isotope | doubleBond | stereogenicClass | lowerHand

def EarlierRule.Value : EarlierRule → Type
  | .nuclearCharge => Nat
  | .duplicate => RawMolecule.CanonicalNodeProvenance
  | .isotope => Element × Option Nat
  | .stereogenicClass => Bool
  | .doubleBond | .lowerHand => Unit

def EarlierSite.observe (s : EarlierSite) (r : EarlierRule) : r.Value :=
  match r with
  | .nuclearCharge => s.atom.element.atomicNumber
  | .duplicate => s.provenance
  | .isotope => (s.atom.element,s.atom.isotope?)
  | .stereogenicClass => s.chiralAuxiliary
  | .doubleBond | .lowerHand => ()

/-- In the single-site fragment every other atom is constitutionally
nonstereogenic or a terminal duplicate. -/
def armHands (ss : List EarlierSite) (h : RS) : List RS :=
  ss.filterMap fun s => if s.chiralAuxiliary then some h else none

def likePairs : List RS → List Bool
  | [] => []
  | first :: rest => rest.map fun next => decide (first = next)

/-- Verified premises for applying Rule 5 to one pair of arms. The mirror
symmetry is checked on the entire molecule. The compared inventories cover
every occurrence, including terminal duplicates and both singleton chiral sites. -/
structure SinglePair (m : RawMolecule) (g : Geometry) (p : Nat → Nat)
    (root high a b low depth : Nat) where
  fragment : saturatedCHO m = true
  symmetry : Reflects m g p
  frame : [high,a,b,low].Perm (m.writtenNeighbors root)
  exchange : p root = root ∧ p high = high ∧ p low = low ∧ p a = b
  leftPath : List Nat
  rightPath : List Nat
  leftSite : singleSite? m root a = some leftPath
  rightSite : singleSite? m root b = some rightPath
  pathMap : leftPath.map p = rightPath
  leftNode : RawMolecule.CanonicalBranchNode
  rightNode : RawMolecule.CanonicalBranchNode
  leftArm : occurrence? m [root,a] = some leftNode
  rightArm : occurrence? m [root,b] = some rightNode
  leftInventory : List EarlierSite
  rightInventory : List EarlierSite
  leftEarlier : earlierSites m leftPath (m.atomCount+1) leftNode = some leftInventory
  rightEarlier : earlierSites m rightPath (m.atomCount+1) rightNode = some rightInventory
  sameEarlier : (leftInventory.map (EarlierSite.rename p)).Perm rightInventory
  upperAtoms : ∃ z x y w, [high,a,b,low].mapM (fun i => (m.atoms[i]?).map (·.element.atomicNumber)) =
    some [z,x,y,w] ∧ z > x ∧ x = y ∧ y > w
  leftHand : RS
  rightHand : RS
  leftRead : atomicAux? m g leftPath depth = some leftHand
  rightRead : atomicAux? m g rightPath depth = some rightHand
  opposite : leftHand.swap = rightHand
  onlyLeft : armHands leftInventory leftHand = [leftHand]
  onlyRight : armHands rightInventory rightHand = [rightHand]

private def verify (claim : Prop) [Decidable claim] : Option (PLift claim) :=
  if h : claim then some ⟨h⟩ else none

/-- Verify the candidate frame and locate the two auxiliaries in the graph. -/
def singlePair? (m : RawMolecule) (g : Geometry) (p : Nat → Nat)
    (root high a b low depth : Nat) : Option (SinglePair m g p root high a b low depth) := do
  let ⟨frag⟩ ← verify (saturatedCHO m = true)
  let ⟨atoms⟩ ← verify (∀ i : Fin m.atomCount, p i < m.atomCount ∧ p (p i) = i ∧ (g i).isSome = true ∧
    m.atoms[p i]? = m.atoms[i.val]? ∧ g (p i) = mirror g i)
  let ⟨bonds⟩ ← verify (∀ i j : Fin m.atomCount, m.bondOrder (p i) (p j) = m.bondOrder i j)
  let ⟨ex⟩ ← verify (p root = root ∧ p high = high ∧ p low = low ∧ p a = b)
  let frame := [high,a,b,low]
  let ⟨perm⟩ ← verify (frame.Perm (m.writtenNeighbors root))
  guard (decide frame.Nodup)
  let ⟨[z,x,y,w],zs⟩ ← (frame.mapM (fun i => (m.atoms[i]?).map (·.element.atomicNumber))).attach | none
  let ⟨order⟩ ← verify (z > x ∧ x = y ∧ y > w)
  let ⟨u,us⟩ ← (singleSite? m root a).attach
  let ⟨v,vs⟩ ← (singleSite? m root b).attach
  let ⟨pm⟩ ← verify (u.map p = v)
  let ⟨left,lc⟩ ← (occurrence? m [root,a]).attach
  let ⟨right,rc⟩ ← (occurrence? m [root,b]).attach
  let ⟨li,liEq⟩ ← (earlierSites m u (m.atomCount+1) left).attach
  let ⟨ri,riEq⟩ ← (earlierSites m v (m.atomCount+1) right).attach
  let ⟨same⟩ ← verify ((li.map (EarlierSite.rename p)).Perm ri)
  let ⟨lh,lr⟩ ← (atomicAux? m g u depth).attach
  let ⟨rh,rr⟩ ← (atomicAux? m g v depth).attach
  let ⟨opp⟩ ← verify (lh.swap = rh)
  let ⟨ol⟩ ← verify (armHands li lh = [lh])
  let ⟨orr⟩ ← verify (armHands ri rh = [rh])
  return ⟨frag,⟨atoms,bonds⟩,perm,ex,u,v,us,vs,pm,left,right,lc,rc,li,ri,
    liEq,riEq,same,⟨z,x,y,w,zs,order⟩,lh,rh,lr,rr,opp,ol,orr⟩

/-- Actual constitutional and stereo observations correspond at every
transported address, with multiplicities. Thus the whole addressed data for
these rules agree even if branch enumeration order differs. -/
theorem SinglePair.earlier_observations {m g p root high a b low depth}
    (c : SinglePair m g p root high a b low depth) (r : EarlierRule) :
    (c.leftInventory.map (fun s => (s.address.map p,s.observe r))).Perm
      (c.rightInventory.map (fun s => (s.address,s.observe r))) := by
  have h := c.sameEarlier.map (fun s => (s.address,s.observe r))
  cases r <;> simpa [EarlierSite.rename,EarlierSite.observe,List.map_map,Function.comp_def] using h

/-- Both branches exhaust Rule 4b with an empty list of descriptor pairs.
Rule 5 then distinguishes the independently derived opposite readings. -/
theorem SinglePair.four_b_tie {m g p root high a b low depth}
    (c : SinglePair m g p root high a b low depth) :
    likePairs (armHands c.leftInventory c.leftHand) = [] ∧
      likePairs (armHands c.rightInventory c.rightHand) = [] := by
  rw [c.onlyLeft,c.onlyRight]
  exact ⟨rfl,rfl⟩

def SinglePair.descriptor {m g p root high a b low depth}
    (c : SinglePair m g p root high a b low depth) : Option LocalizedTetrahedralRSPseudoDescriptor :=
  caseFromMirror? (fromAux m g high a b low c.leftPath c.rightPath depth)
    (fromAux m (mirror g) high a b low c.leftPath c.rightPath depth)

theorem SinglePair.casing {m g p root high a b low depth} (c : SinglePair m g p root high a b low depth) :
    c.descriptor = (pairedReading g high a b low (some c.leftHand) (some c.rightHand)).map
      (fun h => .pseudoasymmetric (pseudoRSOfRS h)) := by
  rw [SinglePair.descriptor,fromAux_mirror]
  simp only [fromAux,c.leftRead,c.rightRead]
  cases pairedReading g high a b low (some c.leftHand) (some c.rightHand) with
  | none => rfl
  | some h => cases h <;> rfl

def enantiomorphicCenter? (m : RawMolecule) (g : Geometry) (p : Nat → Nat)
    (root high a b low depth : Nat) : Option LocalizedTetrahedralRSPseudoDescriptor :=
  (singlePair? m g p root high a b low depth).bind SinglePair.descriptor

end TetraStereo.Engine.RingChemicalPriority
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.earlier_rules_tie
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.enantiomorphicCenter?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.SinglePair.casing
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.SinglePair.earlier_observations
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.SinglePair.four_b_tie
