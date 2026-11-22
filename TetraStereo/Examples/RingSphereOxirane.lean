import TetraStereo.Engine.RingSpherePublication
import TetraStereo.Engine.RingFIFOAlternatives
import TetraStereo.Engine.RingSiblingKeyObstruction
import TetraStereo.Examples.RingFrozenSilentOxirane

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace TetraStereo.Examples.RingSphereOxirane
open OneCenter Engine
open RingFrozenSilentOxirane (input molecule spatial)
open RingActivePairs (Site Arm)
open RingNestedActivePair (Frame Reader)
open RingActivePairReport (Matrix Slot)

/-- Recover the comparison's complete molecular frame from a real call in
the chosen geometry's chronology. Reuse its active mark and its visible
publication store when evaluating every ordered pair of physical ligands. -/
def chronologicalMatrix (rev far : Bool) : Option (List Int) := do
  let g := if rev then LocalizedGenericMarkedRecalculation.mirror RingFrozenSilentOxirane.geometry
    else RingFrozenSilentOxirane.geometry
  let derivation ← CentresRing.Molecular.derive molecule g RingFrozenSilentOxirane.layout
  let path := if far then [1,2,0] else [1,0]
  let call ← derivation.calls.find? fun c =>
    c.frame.focus == path && c.comparison.left == 3 && c.comparison.right == 4
  let read ← CentresRing.Molecular.prepare call.frame
  let atoms := [1,2,3,4]
  let rows ← atoms.mapM fun a => atoms.mapM fun b => do
    if a = b then return (0 : Int)
    let tests ← read a b
    return (← CentresRing.Molecular.decideSteps (CentresRing.Molecular.results tests.val)).2
  return rows.flatten

/-- All four independently computed matrices agree with the values measured
in the corresponding original or reflected source invocation. -/
theorem chronological_matrix (rev far : Bool) :
    chronologicalMatrix rev far = some RingFrozenSilentOxirane.expectedMatrix := by
  cases rev <;> cases far <;> rfl

def sourceScores (far : Bool) (a b : Slot) : Option (Int × Int) := do
  return ((← (← chronologicalMatrix false far)[4*a.val+b.val]?),
    (← (← chronologicalMatrix true far)[4*a.val+b.val]?))

def sourceMatrix (far : Bool) : Matrix (sourceScores far) :=
  (RingActivePairReport.matrix? (sourceScores far)).get (by cases far <;> rfl)

def sourceRefusal (far : Bool) : RingOrdinaryPairRefusal.Certificate (sourceMatrix far) :=
  (RingOrdinaryPairRefusal.find? (sourceMatrix far)).get (by cases far <;> rfl)

/-- At both real occurrence/store combinations the independently evaluated
molecular score matrix has one tied pair and precludes a ranking or Rule 6. -/
theorem source_refusals (far rev : Bool) :
    ¬Nonempty (RingActivePairReport.Ranking (sourceMatrix far) rev) ∧
      (RingChemicalPriority.ReferenceFrame.marks RingOrdinaryPairRefusal.ids
        (RingOrdinaryPairRefusal.table (sourceMatrix far) rev)).length ∉ [3,4] :=
  ⟨(sourceRefusal far).no_ranking rev,(sourceRefusal far).no_promotion rev⟩

def original : input.certified.Atom := ⟨1,by decide +kernel⟩
def hist (s : Site input) := s.val.node.history.map Fin.val
private def site? (path : List Nat) := (RingActiveDistanceSchedule.sites input).find? (fun q =>
  q.val.root == original && q.val.node.provenance == .realAtom && hist q == path)
private abbrev frozen (f : Site input) :=
  RingNestedActivePair.masked f (RingClosedGroupTie.atRoot input original)
private def scores {f : Site input} (frame : Frame input f) (read : Reader input) (a b : Slot) :=
  RingSpherePriority.edge? input f (frame.arm a).occurrence (frame.arm b).occurrence read

/-- Each oxygen has a child hydrogen. The source priority keys of those
two nonterminal oxygen arms coincide. The previously required strict row is unavailable. -/
structure Witness (path : List Nat) where
  f : Site input
  a : Site input
  b : Site input
  addresses : hist f = path ∧ hist a = 3 :: path ∧ hist b = 4 :: path
  originalRoot : f.val.root = original
  frame : Frame input f
  oldMissing : (RingNestedActivePair.edge? input f a b (frozen f)).isNone = true
  proximalMissing : RingProximalUnit.edge? input f a b (frozen f) = none
  bothAmbiguous : RingSiblingKeyObstruction.Collision input ⟨a,some f⟩ ∧
    RingSiblingKeyObstruction.Collision input ⟨b,some f⟩
  exact : RingSpherePriority.score? input f a b (frozen f) = some (0,0)
  matrix : Matrix (scores frame (frozen f))
  refusal : RingOrdinaryPairRefusal.Certificate matrix
  tiedAtoms : frame.atoms [refusal.a,refusal.b] = [3,4] ∨ frame.atoms [refusal.a,refusal.b] = [4,3]

theorem Witness.physical {path} (w : Witness path) (rev : Bool) :
    ¬Nonempty (RingActivePairReport.Ranking w.matrix rev) ∧
      (RingChemicalPriority.ReferenceFrame.marks RingOrdinaryPairRefusal.ids
        (RingOrdinaryPairRefusal.table w.matrix rev)).length ∉ [3,4] :=
  ⟨w.refusal.no_ranking rev,w.refusal.no_promotion rev⟩

theorem Witness.signed_certificate {path} (w : Witness path) :
    ∃ c : RingSpherePriority.Certificate input w.f w.a w.b (frozen w.f), c.score = (0,0) :=
  RingSpherePriority.score_source w.exact

private def checkWith? (path : List Nat) (view : Reader input)
    (computed : view = RingClosedGroupTie.atRoot input original) : Option (Witness path) := do
  let f ← site? path
  let a ← site? (3 :: path)
  let b ← site? (4 :: path)
  let frame ← RingNestedActivePair.frame? input f
  let read := RingNestedActivePair.masked f view
  if addr : hist f = path ∧ hist a = 3 :: path ∧ hist b = 4 :: path ∧ f.val.root = original then
    if missing : (RingNestedActivePair.edge? input f a b read).isNone = true ∧
        RingProximalUnit.edge? input f a b read = none then
      if olds : (RingRetainedSiblingOrder.chemicalChildren? input ⟨a,some f⟩).isNone = true ∧
          (RingRetainedSiblingOrder.chemicalChildren? input ⟨b,some f⟩).isNone = true then
        if exactScore : RingSpherePriority.score? input f a b read = some (0,0) then
          let matrix ← RingActivePairReport.matrix? (scores frame read)
          let refusal ← RingOrdinaryPairRefusal.find? matrix
          if tied : frame.atoms [refusal.a,refusal.b] = [3,4] ∨ frame.atoms [refusal.a,refusal.b] = [4,3] then
            have ambiguous := And.intro
              ((RingSiblingKeyObstruction.missing_iff ..).mp (Option.isNone_iff_eq_none.mp olds.1))
              ((RingSiblingKeyObstruction.missing_iff ..).mp (Option.isNone_iff_eq_none.mp olds.2))
            return by
              subst view
              exact ⟨f,a,b,⟨addr.1,addr.2.1,addr.2.2.1⟩,addr.2.2.2,frame,missing.1,missing.2,ambiguous,
              exactScore,matrix,refusal,tied⟩
  none

/-- Produce the signed score and refusal proofs at the requested occurrence
under the actual frozen distance schedule for original carbon C1. -/
def witness? (path : List Nat) : Option (Witness path) :=
  checkWith? path (RingActiveDistanceSchedule.snapshot (RingClosedGroupTie.publicationTable input original))
    (RingClosedGroupTie.table_readback ..)

/-- The reported state is a completed absence in the original C1 schedule.
At either interior C0 address the preceding publication rule left an open cell. -/
structure Publication (path : List Nat) where
  site : Site input
  pathId : hist site = path
  bound : site.val.root = original
  issued : RingSpherePublication.atRoot input original site = some none
  extended : path = [1] ∨ RingClosedGroupTie.publish? input site
    (RingActiveDistanceSchedule.frozen (RingSpherePublication.atRoot input original) site) = none

theorem Publication.derived {path} (p : Publication path) :
    RingSpherePublication.Derivation input p.site none := RingSpherePublication.derivation p.bound p.issued

private def issueWith? (path : List Nat) (view : Reader input)
    (computed : view = RingSpherePublication.atRoot input original) : Option (Publication path) := do
  let site ← site? path
  if bound : hist site = path ∧ site.val.root = original ∧ view site = some none then
    if previous : path = [1] ∨ RingClosedGroupTie.publish? input site
        (RingActiveDistanceSchedule.frozen view site) = none then
      return by
        subst view
        exact ⟨site,bound.1,bound.2.1,bound.2.2,previous⟩
  none

private def publicationView (root : input.certified.Atom) : Reader input :=
  RingActiveDistanceSchedule.snapshot (RingSpherePublication.publicationTable input root)

/-- Materialize the original C1 table once before querying its cells. -/
private def originalRows : RingActiveDistanceSchedule.Table input := RingSpherePublication.publicationTable input original

private theorem view_exact (root : input.certified.Atom) : publicationView root = RingSpherePublication.atRoot input root :=
  RingSpherePublication.table_readback ..

def publication? (path : List Nat) : Option (Publication path) :=
  issueWith? path (RingActiveDistanceSchedule.snapshot originalRows) (view_exact original)

/-- Whole-molecule projection for a configured carbon at its own original root. -/
def originalRefusal? (root : input.certified.Atom) : Option
    {q : Site input // q.val.root = root ∧ hist q = [root.val] ∧
      RingSpherePublication.Derivation input q none} := do
  let q ← (RingActiveDistanceSchedule.sites input).find? fun v =>
    v.val.root == root && v.val.node.provenance == .realAtom && hist v == [root.val]
  if h : q.val.root = root ∧ hist q = [root.val] ∧ publicationView root q = some none then
    return ⟨q,h.1,h.2.1,RingSpherePublication.derivation h.1 (by simpa only [view_exact] using h.2.2)⟩
  none

def verify : IO Unit := do
  let view := RingActiveDistanceSchedule.snapshot (RingClosedGroupTie.publicationTable input original)
  for path in [[0,1],[0,2,1]] do
    let some w := checkWith? path view (RingClosedGroupTie.table_readback ..) |
      throw (IO.userError s!"missing frozen refusal at retained C0 path {path}")
    let left : Arm input := ⟨w.a,some w.f⟩
    let right : Arm input := ⟨w.b,some w.f⟩
    for (arm,ids) in [(left,[5,6]),(right,[7,8])] do
      let children := RingClosedPairGroup.children input arm
      unless children.map (fun c => c.occurrence.val.node.history.head?.map Fin.val) == ids.map some &&
        children.all (fun c => (RingClosedPairGroup.children input c).length == 1) do
        throw (IO.userError s!"wrong O–H substituents at {path}")
      let walks := RingFIFOAlternatives.outcomes (RingFIFOAlternatives.chemicalPermit input) id arm
      unless walks.length == 2 && (walks.map fun xs => xs.map (fun t => hist t.occurrence)).eraseDups.length == 2 do
        throw (IO.userError s!"missing two sibling orders at {path}")
    let some slots := ([1,2,3,4] : List Nat).mapM (fun atom =>
      (List.finRange 4).find? fun k => w.frame.atoms [k] == [atom]) |
      throw (IO.userError s!"unidentified physical carriers at {path}")
    let rows := slots.flatMap fun a => slots.map fun b => w.matrix.get a b
    unless rows.map Prod.fst == RingFrozenSilentOxirane.expectedMatrix &&
        rows.map Prod.snd == RingFrozenSilentOxirane.expectedMatrix do
      throw (IO.userError s!"molecular and release comparison matrices differ at {path}")
    IO.println s!"C0 history {path}: two admissible sibling orders on each arm, N3/N4 score 0/0; 2+1+1 refusal"
  let scheduled := RingActiveDistanceSchedule.snapshot originalRows
  for path in [[0,1],[0,2,1],[1]] do
    let some _ := issueWith? path scheduled (view_exact original) |
      throw (IO.userError s!"missing distance-scheduled refusal at {path}")
    IO.println s!"{path}: original C1 distance schedule publishes a proved absence"
  let other : input.certified.Atom := ⟨0,by decide +kernel⟩
  unless (originalRefusal? other).isSome do throw (IO.userError "missing original C0 refusal")
  IO.println "Both detected carbons, C0 and C1, have original-root refusals"

end TetraStereo.Examples.RingSphereOxirane

assert_kernel_only TetraStereo.Examples.RingSphereOxirane.witness?
assert_kernel_only TetraStereo.Examples.RingSphereOxirane.Witness.physical
assert_kernel_only TetraStereo.Examples.RingSphereOxirane.Witness.signed_certificate
assert_kernel_only TetraStereo.Examples.RingSphereOxirane.Publication.derived
assert_kernel_only TetraStereo.Examples.RingSphereOxirane.publication?
assert_kernel_only TetraStereo.Examples.RingSphereOxirane.originalRefusal?

assert_kernel_only TetraStereo.Examples.RingSphereOxirane.source_refusals
assert_kernel_only TetraStereo.Examples.RingSphereOxirane.chronological_matrix
