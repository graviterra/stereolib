import TetraStereo.Engine.RingAtomicCarbonReport
import TetraStereo.OneCenter.OccurrenceStructuralNonbearingFacts

set_option autoImplicit false

namespace TetraStereo.Engine.LocalIsotopeCarbonReport
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingChemicalPriority Recursive IsotopePriority
open LocalizedChemicalRingPhysicalSense (inputGeometry)

/-- A real first-sphere occurrence reached by a single bond at a fresh root. -/
structure Arm (m : RawMolecule) (i : Nat) (focus : RawMolecule.CanonicalBranchNode) where
  cursor : CanonicalRerootCursor
  incoming : cursor.previous? = some focus
  address : cursor.node.history.reverse = [i,cursor.node.atom]
  real : cursor.node.provenance = .realAtom
  singleBond : m.bondOrder i cursor.node.atom = 1
  atom : AtomSpec
  source : m.atoms[cursor.node.atom]? = some atom
  positive : 0 < atom.element.atomicNumber
  prior : PriorObservation
  observed : observation? m [i] cursor = some prior

private def arm? (m : RawMolecule) (i : Nat) (focus : RawMolecule.CanonicalBranchNode)
    (c : CanonicalRerootCursor) : Option (Arm m i focus) := do
  let ⟨a,source⟩ ← (m.atoms[c.node.atom]?).attach
  let ⟨p,observed⟩ ← (observation? m [i] c).attach
  if h : c.previous? = some focus ∧ c.node.history.reverse = [i,c.node.atom] ∧
      c.node.provenance = .realAtom ∧ m.bondOrder i c.node.atom = 1 ∧ 0 < a.element.atomicNumber then
    return ⟨c,h.1,h.2.1,h.2.2.1,h.2.2.2.1,a,source,h.2.2.2.2,p,observed⟩
  none

def Arm.mass? {m i n} (a : Arm m i n) :=
  CIPRule2MassData.rule2MassPico? a.atom.element.atomicNumber a.atom.isotope?

/-- Every molecular bond incident to this atom connects it to the focus. -/
abbrev OnlyBondTo (m : RawMolecule) (site focus : Nat) : Prop :=
  ∀ b ∈ m.bonds, (b.source = site → b.target = focus) ∧ (b.target = site → b.source = focus)

/-- A terminal isotope comparison includes the source masses, the entire
earlier-rule observation and the remaining non-isotopic atom properties. -/
abbrev TerminalHigher {m i n} (a b : Arm m i n) : Prop :=
  a.cursor.children m = [] ∧ b.cursor.children m = [] ∧
  OnlyBondTo m a.cursor.node.atom i ∧ OnlyBondTo m b.cursor.node.atom i ∧ a.prior = b.prior ∧
  massIndependentAtom a.atom = massIndependentAtom b.atom ∧
  a.mass?.isSome = true ∧ b.mass?.isSome = true ∧ b.mass?.getD 0 < a.mass?.getD 0

abbrev Higher {m i n} (a b : Arm m i n) : Prop :=
  b.atom.element.atomicNumber < a.atom.element.atomicNumber ∨ TerminalHigher a b

/-- Earlier-rule readings agree throughout both complete terminal branches,
at every positive budget. Both strictly ordered masses are successful lookups
at the exact real atoms addressed by the two arms. -/
theorem terminal_priority {m i n} {a b : Arm m i n} (h : TerminalHigher a b) :
    (∀ d, Isomorphic m [i] (d+1) a.cursor b.cursor) ∧
    a.atom.element = b.atom.element ∧ a.atom.charge = b.atom.charge ∧
    a.atom.aromatic = b.atom.aromatic ∧
    ∃ heavy light, a.mass? = some heavy ∧ b.mass? = some light ∧ light < heavy := by
  obtain ⟨la,lb,_,_,prior,atom,ha,hb,less⟩ := h
  obtain ⟨el,ch,ar⟩ := (massIndependentAtom_eq_iff _ _).mp atom
  refine ⟨?_,el,ch,ar,?_⟩
  · intro d
    refine ⟨a.prior,a.observed,prior ▸ b.observed,[],?_,?_⟩
    · rw [lb]
    · rw [la]
      exact .nil
  · cases left : a.mass? <;> cases right : b.mass? <;> simp_all

structure Ranking (m : RawMolecule) (i : Nat) where
  focus : RawMolecule.CanonicalBranchNode
  reached : occurrence? m [i] = some focus
  four : (occurrenceLigandCursors m focus).length = 4
  distinct : ((occurrenceLigandCursors m focus).map (·.node.atom)).Nodup
  arms : List (Arm m i focus)
  complete : (arms.map (·.cursor)).Perm (occurrenceLigandCursors m focus)
  strict : arms.Pairwise Higher

def Ranking.order {m i} (r : Ranking m i) := r.arms.map (·.cursor.node.atom)

def ranking? (m : RawMolecule) (i : Nat) : Option (Ranking m i) := do
  let ⟨n,reached⟩ ← (occurrence? m [i]).attach
  let cs := occurrenceLigandCursors m n
  if h : cs.length = 4 ∧ (cs.map (·.node.atom)).Nodup then
    let arms ← cs.mapM (arm? m i n)
    let key (a : Arm m i n) := [a.atom.element.atomicNumber,a.mass?.getD 0]
    let sorted := arms.insertionSort (fun a b => key b ≤ key a)
    if covered : (sorted.map Arm.cursor).Perm cs then
      if strict : sorted.Pairwise Higher then
        return ⟨n,reached,h.1,h.2,sorted,covered,strict⟩
  none

private theorem official_leaf {m : RawMolecule} {c h : Fin m.atomCount}
    (neighbors : m.toMoleculeGraph.neighborFinset h = {c}) (singleBond : m.toMoleculeGraph.bond h c = 1) :
    m.toMoleculeGraph.officialCIPChildren (.rootFromEdge c h) = [] := by
  simp [MoleculeGraph.officialCIPChildren,MoleculeGraph.officialChildCopies,
    MoleculeGraph.officialNeighborCopies,OfficialCIPNode.rootFromEdge,OfficialCIPNode.parent?,
    OfficialCIPNode.isDuplicateLeaf,OfficialCIPNodeProvenance.isDuplicateLeaf,neighbors,singleBond]

/-- The molecular occurrence and the official digraph branch of one singly
bonded terminal hydrogen, with its complete sourced observation. -/
structure TerminalHydrogen (m : RawMolecule) (center : Fin m.atomCount) where
  arm : Arm m center.val (canonicalCenterRoot center.val)
  incident : arm.cursor ∈ occurrenceLigandCursors m (canonicalCenterRoot center.val)
  hydrogen : arm.atom.element = .H
  leaf : arm.cursor.children m = []
  noFrame : (m.ligandsWithLonePair arm.cursor.node.atom).length < 4
  observation : FullObservation
  measured : fullObservation? m [center.val] arm.cursor = some observation
  bound : arm.cursor.node.atom < m.atomCount
  ligand : arm.cursor.node.atom ∈ m.ligandsWithLonePair center.val
  adjacent : m.toMoleculeGraph.Adj center ⟨arm.cursor.node.atom,bound⟩
  officialLeaf : m.toMoleculeGraph.officialCIPChildren
    (.rootFromEdge center ⟨arm.cursor.node.atom,bound⟩) = []

private def terminalHydrogen? (m : RawMolecule) (center : Fin m.atomCount)
    (c : {c // c ∈ occurrenceLigandCursors m (canonicalCenterRoot center.val)}) :
    Option (TerminalHydrogen m center) := do
  let arm ← arm? m center.val (canonicalCenterRoot center.val) c.val
  if member : arm.cursor ∈ occurrenceLigandCursors m (canonicalCenterRoot center.val) then
    if terminal : arm.atom.element = .H ∧ arm.cursor.children m = [] ∧
        (m.ligandsWithLonePair arm.cursor.node.atom).length < 4 then
      let ⟨o,measured⟩ ← (fullObservation? m [center.val] arm.cursor).attach
      if bound : arm.cursor.node.atom < m.atomCount then
        let site : Fin m.atomCount := ⟨arm.cursor.node.atom,bound⟩
        if graph : arm.cursor.node.atom ∈ m.ligandsWithLonePair center.val ∧
            m.toMoleculeGraph.Adj center site ∧ m.toMoleculeGraph.neighborFinset site = {center} ∧
            m.toMoleculeGraph.bond site center = 1 then
          return ⟨arm,member,terminal.1,terminal.2.1,terminal.2.2,o,measured,bound,graph.1,graph.2.1,
            official_leaf graph.2.2.1 graph.2.2.2⟩
  none

structure HydrogenTie (m : RawMolecule) (i : Nat) where
  bound : i < m.atomCount
  carbon : (m.atoms[i]?).any (fun a => a.element == .C) = true
  reached : occurrence? m [i] = some (canonicalCenterRoot i)
  four : (occurrenceLigandCursors m (canonicalCenterRoot i)).length = 4
  distinct : ((occurrenceLigandCursors m (canonicalCenterRoot i)).map (·.node.atom)).Nodup
  left : TerminalHydrogen m ⟨i,bound⟩
  right : TerminalHydrogen m ⟨i,bound⟩
  different : left.arm.cursor.node.atom ≠ right.arm.cursor.node.atom
  same : left.observation = right.observation
  equalZ : m.atomZAt left.arm.cursor.node.atom = m.atomZAt right.arm.cursor.node.atom
  equalMass : m.atomMassAt left.arm.cursor.node.atom = m.atomMassAt right.arm.cursor.node.atom

def hydrogenTie? (m : RawMolecule) (i : Nat) : Option (HydrogenTie m i) := do
  if bound : i < m.atomCount then
    let n := canonicalCenterRoot i
    let cs := occurrenceLigandCursors m n
    if root : (m.atoms[i]?).any (fun a => a.element == .C) = true ∧ occurrence? m [i] = some n ∧
        cs.length = 4 ∧ (cs.map (·.node.atom)).Nodup then
      let hs := cs.attach.filterMap (terminalHydrogen? m ⟨i,bound⟩)
      return ← hs.findSome? fun a => hs.findSome? fun b =>
        if h : a.arm.cursor.node.atom ≠ b.arm.cursor.node.atom ∧ a.observation = b.observation ∧
            m.atomZAt a.arm.cursor.node.atom = m.atomZAt b.arm.cursor.node.atom ∧
            m.atomMassAt a.arm.cursor.node.atom = m.atomMassAt b.arm.cursor.node.atom then
          some ⟨bound,root.1,root.2.1,root.2.2.1,root.2.2.2,a,b,h.1,h.2.1,h.2.2.1,h.2.2.2⟩
        else none
  none

def HydrogenTie.official {m i} (h : HydrogenTie m i) :
    UniformTerminalArmData m ⟨canonicalCenterRoot i,none⟩ :=
  ⟨h.bound,_,_,h.left.bound,h.right.bound,h.left.ligand,h.right.ligand,h.different,
    h.left.adjacent,h.right.adjacent,h.left.officialLeaf,h.right.officialLeaf,h.equalZ,h.equalMass⟩

/-- The official rule-major comparator completes with equality for every fuel
on these exact molecular branches with their empty descriptor contexts. -/
theorem HydrogenTie.official_tie {m i} (h : HydrogenTie m i) (fuel : Nat) :
    ∃ c : CIPTraceCertificate, m.toMoleculeGraph.compareRuleMajorRootsWithFuel
      m.toMoleculeGraph.officialCIPChildren fuel
      (.rootFromEdge ⟨i,h.bound⟩ ⟨h.left.arm.cursor.node.atom,h.left.bound⟩)
      (.rootFromEdge ⟨i,h.bound⟩ ⟨h.right.arm.cursor.node.atom,h.right.bound⟩)
      .empty .empty = some c ∧ c.outcome = .eq :=
  uniformTerminalArmData_completedTie m _ h.official fuel

/-- No descendant can carry an auxiliary. The production evaluator supplies
no auxiliary on either hydrogen itself at every fuel and auxiliary state.
The complete source observations and these actual auxiliary readings agree
on the entire pair of branches at every positive observation depth. -/
theorem HydrogenTie.same_readings {m i} (h : HydrogenTie m i) (fuel d : Nat) (state : OccurrenceAuxState) :
    occurrenceFact? m fuel state h.left.arm.cursor.node = none ∧
    occurrenceFact? m fuel state h.right.arm.cursor.node = none ∧
    TreesMatch m (fun c => (fullObservation? m [i] c).map fun o => (o,occurrenceFact? m fuel state c.node))
      (d+1) h.left.arm.cursor h.right.arm.cursor := by
  have left := occurrenceFact?_eq_none_of_ligandCount_lt_four m fuel state _ h.left.noFrame
  have right := occurrenceFact?_eq_none_of_ligandCount_lt_four m fuel state _ h.right.noFrame
  refine ⟨left,right,⟨(h.left.observation,none),?_,?_,[],?_,?_⟩⟩
  · simp [h.left.measured,left]
  · simp [h.right.measured,right,h.same]
  · rw [h.right.leaf]
  · rw [h.left.leaf]
    exact .nil

inductive Verdict (m : RawMolecule) (g : Geometry) (depth i : Nat) where
  | atomic (cert : AtomicCarbonReport.Verdict m g depth i)
  | hydrogenTie (equal : HydrogenTie m i)
  | isotope (ranking : Ranking m i) (r : Reading) (observed : geometric g ranking.order ranking.order = some r)

def Verdict.label {m g depth i} : Verdict m g depth i → Option LocalizedAuxiliaryLabel
  | .atomic cert => cert.toReference.reading?.bind Reading.label
  | .hydrogenTie _ => none
  | .isotope _ r _ => r.label

theorem isotope_letter {m g depth i} (rank : Ranking m i) {r}
    (seen : geometric g rank.order rank.order = some r) :
    (Verdict.isotope (depth := depth) rank r seen).label = some (.chiral r.actual) ∧
    readback? g rank.order = some r.actual ∧
    readback? (mirror g) rank.order = some r.actual.swap := by
  obtain ⟨actual,_,label⟩ := constitutional_casing seen
  exact ⟨label,actual,by simp [readback_mirror,actual]⟩

def at? (m : RawMolecule) (g : Geometry) (depth i : Nat) : Option (Verdict m g depth i) := do
  if let some v := AtomicCarbonReport.at? m g depth i then return .atomic v
  if let some pair := hydrogenTie? m i then return .hydrogenTie pair
  let rank ← ranking? m i
  let ⟨r,seen⟩ ← (geometric g rank.order rank.order).attach
  return .isotope rank r seen

/-- A missing result at a center denotes an unresolved comparison or
readback. A refusal requires a molecular hydrogen-pair witness. -/
theorem at?_isSome_iff (m : RawMolecule) (g : Geometry) (depth i : Nat) :
    (at? m g depth i).isSome = true ↔
      (AtomicCarbonReport.at? m g depth i).isSome = true ∨ (hydrogenTie? m i).isSome = true ∨
      ∃ rank r, ranking? m i = some rank ∧ geometric g rank.order rank.order = some r := by
  cases old : AtomicCarbonReport.at? m g depth i with
  | some v => simp [at?,old]
  | none =>
    cases pair : hydrogenTie? m i with
    | some p => simp [at?,old,pair]
    | none =>
      cases ranked : ranking? m i with
      | none => simp [at?,old,pair,ranked]
      | some rank =>
        cases seen : geometric g rank.order rank.order with
        | none => simp [at?,old,pair,ranked,seen]
        | some r =>
          have attached {α : Type} {opt : Option α} {val : α} (h : opt = some val) :
              opt.attach = some ⟨val,h⟩ := by subst opt; rfl
          simp [at?,old,pair,ranked,seen,attached seen]

structure Report (input : LocalizedChemicalRing.Input) (depth : Nat) where
  rows : List ((i : Nat) × Verdict input.molecule (inputGeometry input.certified) depth i)
  inventory : rows.map Sigma.fst = RingCarbonReport.carbons input.molecule

def Report.labels {input depth} (r : Report input depth) :=
  r.rows.map fun row => (row.1,row.2.label)

private def collect (m : RawMolecule) (g : Geometry) (depth : Nat) :
    (ids : List Nat) → Option {rows : List ((i : Nat) × Verdict m g depth i) // rows.map Sigma.fst = ids}
  | [] => some ⟨[],rfl⟩
  | i :: ids => do
    let v ← at? m g depth i
    let tail ← collect m g depth ids
    return ⟨⟨i,v⟩ :: tail.val,by simp [tail.property]⟩

private theorem collect_isSome (m : RawMolecule) (g : Geometry) (depth : Nat) (ids : List Nat) :
    (collect m g depth ids).isSome = true ↔ ∀ i ∈ ids, (at? m g depth i).isSome = true := by
  induction ids with
  | nil => simp [collect]
  | cons i ids ih =>
    cases h : at? m g depth i <;> cases t : collect m g depth ids <;>
      simp [collect,h,t] at ih ⊢ <;> tauto

/-- Each successful report covers all carbons of the admitted input. -/
def check (input : LocalizedChemicalRing.Input) (depth : Nat) : Option (Report input depth) := do
  let rows ← collect input.molecule (inputGeometry input.certified) depth (RingCarbonReport.carbons input.molecule)
  return ⟨rows.val,rows.property⟩

/-- Exact whole-inventory coverage on the union of the existing atomic
profile and strict first-sphere orders refined by real terminal isotope masses. -/
theorem check_isSome_iff (input : LocalizedChemicalRing.Input) (depth : Nat) :
    (check input depth).isSome = true ↔ ∀ i ∈ RingCarbonReport.carbons input.molecule,
      (AtomicCarbonReport.at? input.molecule (inputGeometry input.certified) depth i).isSome = true ∨
      (hydrogenTie? input.molecule i).isSome = true ∨
      ∃ rank r, ranking? input.molecule i = some rank ∧
        geometric (inputGeometry input.certified) rank.order rank.order = some r := by
  have collected : (check input depth).isSome = (collect input.molecule (inputGeometry input.certified)
      depth (RingCarbonReport.carbons input.molecule)).isSome := by
    unfold check
    cases collect input.molecule (inputGeometry input.certified) depth (RingCarbonReport.carbons input.molecule) <;> rfl
  rw [collected,collect_isSome]
  simp only [at?_isSome_iff]

end TetraStereo.Engine.LocalIsotopeCarbonReport

assert_kernel_only TetraStereo.Engine.LocalIsotopeCarbonReport.terminal_priority
assert_kernel_only TetraStereo.Engine.LocalIsotopeCarbonReport.isotope_letter
assert_kernel_only TetraStereo.Engine.LocalIsotopeCarbonReport.check_isSome_iff
assert_kernel_only TetraStereo.Engine.LocalIsotopeCarbonReport.HydrogenTie.same_readings
assert_kernel_only TetraStereo.Engine.LocalIsotopeCarbonReport.HydrogenTie.official_tie
