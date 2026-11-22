import TetraStereo.Engine.RingRecursiveSignedReport
import TetraStereo.OneCenter.AuthoritativeLocalizedRuleMajorAnalysis

set_option autoImplicit false

namespace TetraStereo.Engine.RingSharedArmRefusal
open OneCenter CertifiedLocalizedCIPInput RingChemicalPriority LocalizedGenericMarkedRecalculation
open LocalizedMarkedTerminalGaugeSwap

abbrev Cursor := CanonicalRerootCursor
abbrev Atom := RingSilentPair.Atom

/-- A proposed exchange supplies only atom numbers. All of its chemical,
graph and comparison properties are established by the checker. -/
structure Hint where
  left : Nat
  right : Nat
  swaps : List (Nat × Nat)

def permutation (m : RawMolecule) : List (Nat × Nat) → Equiv.Perm (Atom m)
  | [] => Equiv.refl _
  | (a,b) :: xs =>
    if h : a < m.atomCount ∧ b < m.atomCount then
      (Equiv.swap (⟨a,h.1⟩ : Atom m) ⟨b,h.2⟩).trans (permutation m xs)
    else permutation m xs

private def source (m : RawMolecule) (a : Nat) : Bool :=
  (m.atomAt? a).any fun x => x.charge == 0 && !x.aromatic && x.explicitHydrogens == 0 && x.tetrahedral?.isNone

/-- For a real atom, an actual frame is either too small in this valence class
or contains an independently certified pair of equivalent terminal ligands.
Divalent neutral oxygen and sulfur and monovalent halogens and hydrogen are included. -/
def Inactive (m : RawMolecule) (a : Nat) : Prop :=
  let n := (m.writtenNeighbors a).length
  source m a = true ∧ (RingSilentPair.Neighbors m a (m.writtenNeighbors a)) ∧
    ((m.atomAt? a).any (fun x =>
      (([Element.H,.F,.Cl,.Br,.I].contains x.element && n == 1) ||
       ([Element.O,.S].contains x.element && n == 2))) = true ∧ (m.ligandsWithLonePair a).length < 4 ∨
     (m.atomAt? a).any (fun x => x.element == .C) = true ∧ n = 4 ∧ (RingTerminalPair.check? m a).isSome = true)

instance {m a} : Decidable (Inactive m a) := by unfold Inactive; infer_instance

/-- A closure occurrence is a digraph leaf. A real occurrence must be an
independently nonbearing atom different from the current root. -/
def Quiet (m : RawMolecule) (root : Nat) (c : Cursor) : Prop :=
  source m c.node.atom = true ∧
    ((c.node.forcedLeaf = true ∧ c.children m = []) ∨
      (c.node.provenance = .realAtom ∧ c.node.atom ≠ root ∧ Inactive m c.node.atom))

instance {m root c} : Decidable (Quiet m root c) := by unfold Quiet; infer_instance

private def sites (cs : List Cursor) := cs.map (·.node.atom)

structure Certificate (m : RawMolecule) (d i : Nat) where
  focus : RawMolecule.CanonicalBranchNode
  reached : occurrence? m [i] = some focus
  root : (m.atoms[i]?).any (fun a => a.element == .C) = true
  bound : i < m.atomCount
  four : (sites (occurrenceLigandCursors m focus)).length = 4
  neighbors : RingSilentPair.Neighbors m i (sites (occurrenceLigandCursors m focus))
  left : Cursor
  right : Cursor
  leftAt : left ∈ occurrenceLigandCursors m focus
  rightAt : right ∈ occurrenceLigandCursors m focus
  distinct : left.node.atom ≠ right.node.atom
  attached : left.node.parent = i ∧ right.node.parent = i
  ls : List Cursor
  rs : List Cursor
  full : RingSilentPair.walk? m (IsotopePriority.budget m + 1) left = some ls ∧
    RingSilentPair.walk? m (IsotopePriority.budget m + 1) right = some rs
  quiet : ∀ c ∈ ls ++ rs, Quiet m i c
  remote : ∀ a ∈ sites (ls ++ rs), a ≠ i → Inactive m a
  eligible : carbonSites m (m.atomCount+1) left.node = some [] ∧ carbonSites m (m.atomCount+1) right.node = some []
  tied : IsotopePriority.TreesMatch m (CursorTie.observe? m [i] []) (IsotopePriority.budget m+1) left right
  other : RingSilentPair.OthersStrict m i d (sites (occurrenceLigandCursors m focus)) left.node.atom right.node.atom
  table : ReferenceFrame.Table
  computed : RingSilentPair.ordinary? m d i (sites (occurrenceLigandCursors m focus)) left.node.atom right.node.atom = some table
  refusal : RingSilentPair.Refuses (sites (occurrenceLigandCursors m focus)) left.node.atom right.node.atom table
  exchange : Equiv.Perm (Atom m)
  fixed : exchange ⟨i,bound⟩ = ⟨i,bound⟩
  symmetry : RingSilentPair.Symmetry m i left.node.atom right.node.atom (sites (occurrenceLigandCursors m focus))
    (sites (ls ++ rs)) exchange

def checkExchange? (m : RawMolecule) (d i left right : Nat) (e : Equiv.Perm (Atom m)) : Option (Certificate m d i) := do
  let ⟨focus,reached⟩ ← (occurrence? m [i]).attach
  let cs := occurrenceLigandCursors m focus
  if h : (m.atoms[i]?).any (fun a => a.element == .C) = true ∧ i < m.atomCount ∧
      (sites cs).length = 4 ∧ RingSilentPair.Neighbors m i (sites cs) then
    let pred (a : Nat) (c : Cursor) := c.node.atom == a
    let ⟨l,hl⟩ ← (cs.find? (pred left)).attach
    let ⟨r,hr⟩ ← (cs.find? (pred right)).attach
    let a := l.node.atom
    let b := r.node.atom
    if localPair : a ≠ b ∧ l.node.parent = i ∧ r.node.parent = i then
      let limit := IsotopePriority.budget m + 1
      let ⟨ls,lo⟩ ← (RingSilentPair.walk? m limit l).attach
      let ⟨rs,ro⟩ ← (RingSilentPair.walk? m limit r).attach
      if localData : (∀ s ∈ ls ++ rs, Quiet m i s) ∧ (∀ a ∈ sites (ls ++ rs), a ≠ i → Inactive m a) ∧
          carbonSites m (m.atomCount+1) l.node = some [] ∧ carbonSites m (m.atomCount+1) r.node = some [] then
        if matchTrees : IsotopePriority.treesMatch m (CursorTie.observe? m [i] []) limit l r = true then
          if symmetric : e ⟨i,h.2.1⟩ = ⟨i,h.2.1⟩ ∧
              RingSilentPair.Symmetry m i a b (sites cs) (sites (ls ++ rs)) e then
            if strict : RingSilentPair.OthersStrict m i d (sites cs) a b then
              let ⟨t,hTable⟩ ← (RingSilentPair.ordinary? m d i (sites cs) a b).attach
              if refusal : RingSilentPair.Refuses (sites cs) a b t then
                return ⟨focus,reached,h.1,h.2.1,h.2.2.1,h.2.2.2,l,r,List.mem_of_find?_eq_some hl,
                  List.mem_of_find?_eq_some hr,localPair.1,localPair.2,ls,rs,⟨lo,ro⟩,localData.1,localData.2.1,localData.2.2,
                  IsotopePriority.treesMatch_sound matchTrees,strict,t,hTable,refusal,e,symmetric.1,symmetric.2⟩
  none

def check? (m : RawMolecule) (d i : Nat) (hint : Hint) : Option (Certificate m d i) :=
  checkExchange? m d i hint.left hint.right (permutation m hint.swaps)

theorem Certificate.no_publication {m d i} (c : Certificate m d i)
    {s} (mem : s ∈ c.ls ++ c.rs) (fuel : Nat) (state : OccurrenceAuxState) :
    occurrenceFact? m fuel state s.node = none := by
  obtain ⟨a,found,data⟩ := (Option.any_eq_true _ _).mp (c.quiet s mem).1
  simp only [Bool.and_eq_true] at data
  exact occurrenceFact?_eq_none_of_tetrahedral?_eq_none m fuel state s.node a found
    (Option.isNone_iff_eq_none.mp data.2)

theorem Certificate.structural_absence {m d i} (c : Certificate m d i)
    {s} (mem : s ∈ c.ls ++ c.rs) :
    (s.node.forcedLeaf = true ∧ s.children m = []) ∨
      ((m.ligandsWithLonePair s.node.atom).length < 4 ∨
       ∃ t : RingTerminalPair.Certificate m s.node.atom, RingTerminalPair.check? m s.node.atom = some t) := by
  rcases (c.quiet s mem).2 with closure | real
  · exact Or.inl closure
  · rcases real.2.2.2.2 with small | pair
    · exact Or.inr (Or.inl small.2)
    · exact Or.inr (Or.inr (Option.isSome_iff_exists.mp pair.2.2))

theorem Certificate.graph_exchange {m d i} (c : Certificate m d i) :
    (∀ x : Atom m, m.atoms.get (c.exchange x) = m.atoms.get x) ∧ c.exchange ∈ m.toMoleculeGraph.Aut :=
  ⟨fun x => (c.symmetry.1 x).1,fun x => congrArg (fun a : AtomSpec => a.element.atomicNumber) (c.symmetry.1 x).1,
    fun x => (c.symmetry.1 x).2,fun x => congrArg AtomSpec.charge (c.symmetry.1 x).1,c.symmetry.2.1⟩

/-- Every other atom is either structurally nonbearing or is fixed together
with every atom in its own local frame. This also covers remote ring atoms
that occur more than once among the two retained walks. -/
theorem Certificate.remote_frames {m d i} (c : Certificate m d i) (a : Atom m) (different : a.val ≠ i) :
    Inactive m a.val ∨ (c.exchange a = a ∧ ∀ b : Atom m, m.toMoleculeGraph.Adj a b → c.exchange b = b) := by
  by_cases inside : a.val ∈ sites (c.ls ++ c.rs)
  · exact Or.inl (c.remote _ inside different)
  · exact Or.inr ⟨c.symmetry.2.2.1 a inside,fun b edge => c.symmetry.2.2.2.2 a b different inside edge⟩

theorem Certificate.hand_exchange {m d i} (c : Certificate m d i) (g : Geometry) {order : List Nat}
    (covers : order.Perm (sites (occurrenceLigandCursors m c.focus))) :
    readback? g (order.map (swapAtom c.left.node.atom c.right.node.atom)) = (readback? g order).map RS.swap :=
  readback_swapAtom g _ _ c.distinct order (covers.nodup_iff.mpr c.neighbors.1)
    (covers.length_eq.trans c.four) (covers.mem_iff.mpr (List.mem_map_of_mem c.leftAt))
    (covers.mem_iff.mpr (List.mem_map_of_mem c.rightAt))

theorem Certificate.ordinary_refusal {m d i} (c : Certificate m d i) :
    let ids := sites (occurrenceLigandCursors m c.focus)
    (ReferenceFrame.marks ids c.table).length = 2 ∧ ∀ rev, ReferenceFrame.coherent ids c.table rev = true ∧
      ReferenceFrame.orders ids c.table rev = [] ∧ ReferenceFrame.orderAt c.table rev c.left.node.atom c.right.node.atom = some .eq ∧
      ReferenceFrame.orderAt c.table rev c.right.node.atom c.left.node.atom = some .eq :=
  ⟨c.refusal.1.length_eq,c.refusal.2⟩


/-- Enumerate canonical neighbors directly in atom-number order. This is
extensionally the official sorted neighbor set and reduces in the kernel. -/
def listedNeighbors (ci : CertifiedLocalizedCIPInput) (a : ci.Atom) : List ci.Atom :=
  (List.finRange _).filter fun b => decide (ci.moleculeGraph.Adj a b)

theorem listedNeighbors_eq (ci : CertifiedLocalizedCIPInput) (a : ci.Atom) :
    (ci.moleculeGraph.neighborFinset a).sort (· ≤ ·) = listedNeighbors ci a := by
  apply (Finset.sortedLT_sort _).eq_of_mem_iff
  · exact ((List.sortedLT_finRange _).pairwise.sublist (List.filter_sublist ..)).sortedLT
  · intro x
    simp [listedNeighbors,Finset.mem_sort,MoleculeGraph.mem_neighborFinset]

private def listedCopies (ci : CertifiedLocalizedCIPInput) (a : ci.Atom) :=
  (listedNeighbors ci a).flatMap fun b => (List.range (ci.moleculeGraph.bond a b)).map fun idx => (b,idx)

def listedChildren (ci : CertifiedLocalizedCIPInput) (node : OfficialCIPNode ci.Atom) : List (OfficialCIPNode ci.Atom) :=
  if node.isDuplicateLeaf then [] else
  let copies := match node.current? with
    | none => []
    | some a => match node.parent? with
      | none => listedCopies ci a
      | some parent => (listedCopies ci a).filter fun copy => !(copy.1 == parent && copy.2 == 0)
  copies.map fun copy => node.extend copy.1 copy.2

theorem listedChildren_eq (ci : CertifiedLocalizedCIPInput) : listedChildren ci = ci.executableOfficialCIPChildren := by
  funext node
  simp only [listedChildren,executableOfficialCIPChildren,executableOfficialChildCopies,
    executableOfficialNeighborCopies,listedNeighbors_eq,listedCopies]
  cases current : node.current? <;> cases parent : node.parent? <;> rfl

/-- The two roots are constructed from molecular atom numbers. The compiler
uses the certified finite-atom bound and retains its addressed source nodes. -/
def officialAt? (ci : CertifiedLocalizedCIPInput) (root a b : Nat) : Option CIPTraceCertificate := do
  if h : root < ci.certified.input.molecule.atomCount ∧ a < ci.certified.input.molecule.atomCount ∧
      b < ci.certified.input.molecule.atomCount then
    let observe := ci.certified.input.molecule.semanticExactOfficialRule1aObservation
    let n := ci.certified.input.molecule.atomCount + 1
    let l ← ci.moleculeGraph.buildObservedExactOfficialRuleMajorKey observe (listedChildren ci) n (.rootFromEdge ⟨root,h.1⟩ ⟨a,h.2.1⟩)
    let r ← ci.moleculeGraph.buildObservedExactOfficialRuleMajorKey observe (listedChildren ci) n (.rootFromEdge ⟨root,h.1⟩ ⟨b,h.2.2⟩)
    let _ ← ExactOfficialRuleMajorKey.compareObserved? ci.moleculeGraph observe l r
    return CIPTraceCertificate.ofTrace (ExactOfficialRuleMajorKey.compareTraceObserved ci.moleculeGraph observe l r)
  none

theorem officialAt?_canonical (ci : CertifiedLocalizedCIPInput) (c : ci.TetrahedralCenter) (a b : Fin 4) :
    officialAt? ci c.val.val (ci.canonicalLigandAtom c a).val (ci.canonicalLigandAtom c b).val =
      ci.compareRuleMajorConstitutionAt? c a b := by
  simp [officialAt?,c.val.isLt,(ci.canonicalLigandAtom c a).isLt,(ci.canonicalLigandAtom c b).isLt,
    listedChildren_eq,compareRuleMajorConstitutionAt?,buildExecutableExactOfficialRuleMajorKey]

/-- Every directed comparison in the ordinary table is checked against the
independent full constitutional trace, including both orientations of the tie. -/
def ValidSigns (ci : CertifiedLocalizedCIPInput) (i : Nat) (ids : List Nat) (t : ReferenceFrame.Table) : Prop :=
  ∀ a ∈ ids, ∀ b ∈ ids, a ≠ b →
    let seen := (officialAt? ci i a b).map CIPTraceCertificate.outcome
    seen.isSome = true ∧ ∀ rev : Bool, ReferenceFrame.orderAt t rev a b = seen

instance {ci i ids t} : Decidable (ValidSigns ci i ids t) := by unfold ValidSigns; infer_instance

structure OfficialCertificate (input : LocalizedChemicalRing.Input) (depth i : Nat) extends Certificate input.molecule depth i where
  signs : ValidSigns input.certified i (sites (occurrenceLigandCursors input.molecule focus)) table

def officialExchange? (input : LocalizedChemicalRing.Input) (depth i left right : Nat)
    (e : Equiv.Perm (Atom input.molecule)) : Option (OfficialCertificate input depth i) := do
  let cert ← checkExchange? input.molecule depth i left right e
  if h : ValidSigns input.certified i (sites (occurrenceLigandCursors input.molecule cert.focus)) cert.table then
    return ⟨cert,h⟩
  none

def officialCheck? (input : LocalizedChemicalRing.Input) (depth i : Nat) (hint : Hint) :
    Option (OfficialCertificate input depth i) :=
  officialExchange? input depth i hint.left hint.right (permutation input.molecule hint.swaps)

private theorem find_arm {cs : List Cursor} (unique : (sites cs).Nodup) {l : Cursor} (inCs : l ∈ cs) :
    cs.find? (fun c => c.node.atom == l.node.atom) = some l := by
  cases h : cs.find? (fun c => c.node.atom == l.node.atom) with
  | none =>
    have absent := List.find?_eq_none.mp h l inCs
    simp at absent
  | some y =>
    have equal : y.node.atom = l.node.atom :=
      eq_of_beq (List.find?_some (p := fun c : Cursor => c.node.atom == l.node.atom) h)
    exact congrArg some (List.inj_on_of_nodup_map unique (List.mem_of_find?_eq_some h) inCs equal)

set_option maxHeartbeats 1000000 in
/-- A certificate is specified by mathematical and molecular conditions.
Rechecking its own exchange reconstructs the entire certificate, including
the original molecular walks and comparison table. -/
theorem Certificate.recheck {m d i} (c : Certificate m d i) :
    checkExchange? m d i c.left.node.atom c.right.node.atom c.exchange = some c := by
  have got (α : Type) (o : Option α) (x : α) (h : o = some x) : o.attach = some ⟨x,h⟩ :=
    Option.attach_eq_some o ⟨x,h⟩
  have root := got _ _ _ c.reached
  have l := got _ _ _ (find_arm c.neighbors.1 c.leftAt)
  have r := got _ _ _ (find_arm c.neighbors.1 c.rightAt)
  have ls := got _ _ _ c.full.1
  have rs := got _ _ _ c.full.2
  have t := got _ _ _ c.computed
  have base : (m.atoms[i]?).any (fun a => a.element == .C) = true ∧ i < m.atomCount ∧
      (sites (occurrenceLigandCursors m c.focus)).length = 4 ∧ RingSilentPair.Neighbors m i (sites (occurrenceLigandCursors m c.focus)) :=
    ⟨c.root,c.bound,c.four,c.neighbors⟩
  have localPair := And.intro c.distinct c.attached
  have localData := And.intro c.quiet (And.intro c.remote c.eligible)
  have symmetric := And.intro c.fixed c.symmetry
  unfold checkExchange?
  rw [root]
  dsimp only [Option.bind_eq_bind,Option.bind_some]
  rw [dif_pos base,l]
  dsimp only [Option.bind_eq_bind,Option.bind_some]
  rw [r]
  dsimp only [Option.bind_eq_bind,Option.bind_some]
  rw [dif_pos localPair,ls]
  dsimp only [Option.bind_eq_bind,Option.bind_some]
  rw [rs]
  dsimp only [Option.bind_eq_bind,Option.bind_some]
  rw [dif_pos localData,dif_pos (IsotopePriority.treesMatch_complete c.tied),dif_pos symmetric,
    dif_pos c.other,t]
  dsimp only [Option.bind_eq_bind,Option.bind_some]
  rw [dif_pos c.refusal]
  rfl

theorem OfficialCertificate.recheck {input d i} (c : OfficialCertificate input d i) :
    officialExchange? input d i c.left.node.atom c.right.node.atom c.exchange = some c := by
  simp [officialExchange?,c.toCertificate.recheck,c.signs]

theorem official_exists_iff (input : LocalizedChemicalRing.Input) (d i : Nat) :
    Nonempty (OfficialCertificate input d i) ↔
      ∃ a b e, (officialExchange? input d i a b e).isSome = true := by
  constructor
  · rintro ⟨c⟩
    exact ⟨_,_,_,by rw [c.recheck]; rfl⟩
  · rintro ⟨a,b,e,h⟩
    exact ⟨(officialExchange? input d i a b e).get h⟩

private theorem OfficialCertificate.ligand_member {input d i} (cert : OfficialCertificate input d i)
    (center : input.certified.TetrahedralCenter) (rootId : center.val.val = i) (x : Fin 4) :
    (input.certified.canonicalLigandAtom center x).val ∈ sites (occurrenceLigandCursors input.molecule cert.focus) := by
  let a := input.certified.canonicalLigandAtom center x
  have positive : 0 < input.molecule.bondOrder i a.val := by
    rw [← rootId]
    exact (LocalizedChemicalRingPhysicalSense.adj_iff input.molecule input.certified input.agreement
      input.admissible.1.1 input.admissible.1.2 input.supported _ _).mp (input.certified.canonicalLigandAtom_adj center x)
  have bond := cert.neighbors.2.2 ⟨a.val,(input.molecule.bondOrder_pos_endpoint_lt input.admissible.1.1 positive).2⟩
  by_contra missing
  change a.val ∉ _ at missing
  change input.molecule.bondOrder i a.val = _ at bond
  rw [bond,if_neg missing] at positive
  exact (Nat.lt_irrefl 0) positive

theorem OfficialCertificate.source_trace {input d i} (cert : OfficialCertificate input d i)
    (center : input.certified.TetrahedralCenter) (rootId : center.val.val = i)
    (x y : Fin 4) (different : x ≠ y) :
    ∃ trace, input.certified.DeclarativeRuleMajorConstitutionalTrace center x y trace ∧ ∀ rev,
      ReferenceFrame.orderAt cert.table rev (input.certified.canonicalLigandAtom center x).val
        (input.certified.canonicalLigandAtom center y).val = some (cipTraceOutcome trace) := by
  subst i
  have ne : (input.certified.canonicalLigandAtom center x).val ≠ (input.certified.canonicalLigandAtom center y).val :=
    fun e => different (input.certified.canonicalLigandAtom_injective center (Fin.ext e))
  have signs := cert.signs _ (cert.ligand_member center rfl x) _ (cert.ligand_member center rfl y) ne
  rw [officialAt?_canonical] at signs
  cases h : input.certified.compareRuleMajorConstitutionAt? center x y with
  | none => simp [h] at signs
  | some t =>
    refine ⟨t.trace,input.certified.compareRuleMajorConstitutionAt?_sound_declarative_trace _ _ _ _ h,?_⟩
    simpa [h,t.sound] using signs.2

/-- At a strict constitutional comparison, every later context produces
the displayed sign. At the sole tied pair equal contexts preserve equality.
In particular the structurally empty context works on every edge. -/
theorem OfficialCertificate.full_comparison {input d i} (c : OfficialCertificate input d i)
    (center : input.certified.TetrahedralCenter) (rootId : center.val.val = i) (x y : Fin 4)
    (different : x ≠ y) (rev : Bool) (ctx : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (sameOnTie : ReferenceFrame.orderAt c.table rev (input.certified.canonicalLigandAtom center x).val
      (input.certified.canonicalLigandAtom center y).val = some .eq → ctx x = ctx y) :
    (input.certified.compareRuleMajorAt? center ctx x y).map CIPTraceCertificate.outcome =
      ReferenceFrame.orderAt c.table rev (input.certified.canonicalLigandAtom center x).val
        (input.certified.canonicalLigandAtom center y).val := by
  subst i
  have ne : (input.certified.canonicalLigandAtom center x).val ≠ (input.certified.canonicalLigandAtom center y).val :=
    fun e => different (input.certified.canonicalLigandAtom_injective center (Fin.ext e))
  have signs := c.signs _ (c.ligand_member center rfl x) _ (c.ligand_member center rfl y) ne
  rw [officialAt?_canonical] at signs
  obtain ⟨trace,h⟩ := Option.isSome_iff_exists.mp (input.certified.compareRuleMajorConstitutionAt?_isSome center x y)
  have atEdge := signs.2 rev
  simp only [h,Option.map_some] at atEdge
  rw [atEdge]
  simp only [compareRuleMajorAt?,h]
  by_cases eqn : cipTraceOutcome trace.trace = .eq
  · have same := sameOnTie (atEdge.trans (congrArg some (trace.sound.symm.trans eqn)))
    simp [CIPRuleEngine.compareDigraphThenOfficialTrace_outcome_of_digraph_eq eqn,same,← trace.sound,eqn]
  · simp [CIPRuleEngine.compareDigraphThenOfficialTrace_outcome_of_digraph_ne_eq eqn,trace.sound]

/-- Build one candidate graph exchange from aligned occurrences. Repeated
visits from opposite sides of a ring contribute the same transposition.
Only sibling permutations are enumerated. Every proposed whole-molecule
permutation subsequently passes through the independent certificate checker. -/
private def align? (m : RawMolecule) : Nat → Cursor → Cursor → Option (List (Nat × Nat))
  | 0,_,_ => none
  | n+1,l,r => do
    guard (m.atoms[l.node.atom]? == m.atoms[r.node.atom]?)
    let ls := l.children m
    let rs := r.children m
    guard (ls.length == rs.length && ls.length ≤ 4)
    let below ← rs.permutations'.findSome? fun perm =>
      (ls.zip perm).mapM fun (x,y) => align? m n x y
    let a := l.node.atom
    let b := r.node.atom
    return (if a = b then below.flatten else (min a b,max a b) :: below.flatten)

def discover? (input : LocalizedChemicalRing.Input) (d i : Nat) : Option (OfficialCertificate input d i) := do
  let m := input.molecule
  let focus ← occurrence? m [i]
  let cs := occurrenceLigandCursors m focus
  cs.findSome? fun l => cs.findSome? fun r => do
    guard (l.node.atom < r.node.atom)
    guard (m.atoms[l.node.atom]? == m.atoms[r.node.atom]?)
    let pairs ← align? m (IsotopePriority.budget m+1) l r
    officialCheck? input d i ⟨l.node.atom,r.node.atom,pairs.eraseDups⟩

/-- The opt-in public result carries the checked raw certificate and the
official comparison evidence. Previously returned rows keep their original proofs. -/
abbrev Row (input : LocalizedChemicalRing.Input) (d i : Nat) :=
  Sum (RecursiveSigned.CarbonVerdict input.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified) d i)
    (OfficialCertificate input d i)

def label {input d i} : Row input d i → Option LocalizedAuxiliaryLabel
  | .inl c => c.label
  | .inr _ => none

def carbon? (input : LocalizedChemicalRing.Input) (d i : Nat) (hint : Option Hint) : Option (Row input d i) :=
  if i ∉ RingCarbonReport.carbons input.molecule then none else
  (RecursiveSigned.carbon? input.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified) d i).map Sum.inl <|>
    ((match hint with
      | some candidate => officialCheck? input d i candidate
      | none => discover? input d i).map Sum.inr)

abbrev Report (input : LocalizedChemicalRing.Input) (d : Nat) :=
  List ((i : Nat) × Row input d i)

def report? (input : LocalizedChemicalRing.Input) (depth : Nat) (hints : Nat → Option Hint := fun _ => none) : Option (Report input depth) :=
  (RingCarbonReport.carbons input.molecule).mapM fun i =>
    (carbon? input depth i (hints i)).map (Sigma.mk i)

def labels {input d} (rows : Report input d) := rows.map fun x => (x.1,label x.2)

theorem report_inventory {input depth hints r} (found : report? input depth hints = some r) :
    r.map Sigma.fst = RingCarbonReport.carbons input.molecule := by
  have go (ids : List Nat) (rows : Report input depth)
      (got : ids.mapM (m := Option) (fun i => (carbon? input depth i (hints i)).map (Sigma.mk i)) = some rows) :
      rows.map Sigma.fst = ids := by
    induction ids generalizing rows with
    | nil => simpa using got.symm
    | cons i is ih =>
      rw [List.mapM_cons] at got
      cases hi : carbon? input depth i (hints i) <;>
        cases rest : is.mapM (m := Option) (fun j => (carbon? input depth j (hints j)).map (Sigma.mk j)) <;>
        simp [hi,rest] at got
      subst rows
      simp [ih _ rest]
  exact go _ r found

end TetraStereo.Engine.RingSharedArmRefusal

assert_kernel_only TetraStereo.Engine.RingSharedArmRefusal.Certificate.no_publication
assert_kernel_only TetraStereo.Engine.RingSharedArmRefusal.Certificate.structural_absence
assert_kernel_only TetraStereo.Engine.RingSharedArmRefusal.Certificate.graph_exchange
assert_kernel_only TetraStereo.Engine.RingSharedArmRefusal.Certificate.hand_exchange
assert_kernel_only TetraStereo.Engine.RingSharedArmRefusal.Certificate.ordinary_refusal
assert_kernel_only TetraStereo.Engine.RingSharedArmRefusal.report_inventory

assert_kernel_only TetraStereo.Engine.RingSharedArmRefusal.OfficialCertificate.source_trace

assert_kernel_only TetraStereo.Engine.RingSharedArmRefusal.OfficialCertificate.full_comparison

assert_kernel_only TetraStereo.Engine.RingSharedArmRefusal.Certificate.remote_frames

assert_kernel_only TetraStereo.Engine.RingSharedArmRefusal.official_exists_iff
