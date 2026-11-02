import TetraStereo.OneCenter.LocalizedAxialRootPerception
import TetraStereo.OneCenter.P93AcyclicConfiguration

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Molecule-wide open axial-chain perception

Starting from the exact terminal roots, this module follows the constitution's physical order-two
neighbours directly.  It refuses fuel exhaustion, a repeated atom (closed cycle), and two or more
forward continuations (branching).  A successful even frame is canonically oriented from the
smaller terminal atom, so the two terminal roots of one open axis do not produce two units.
-/

namespace CertifiedLocalizedCIPInput

/-- Physical order-two neighbours other than the atom from which the walk arrived. -/
def localizedAxialForwardNeighbors
    (input : CertifiedLocalizedCIPInput) (previous current : input.Atom) :
    List input.Atom :=
  (input.localizedOrderTwoNeighbors current).filter fun neighbor => neighbor ≠ previous

@[simp] theorem mem_localizedAxialForwardNeighbors_iff
    (input : CertifiedLocalizedCIPInput) (previous current neighbor : input.Atom) :
    neighbor ∈ input.localizedAxialForwardNeighbors previous current ↔
      input.moleculeGraph.bond current neighbor = 2 ∧ neighbor ≠ previous := by
  simp [localizedAxialForwardNeighbors]

/-- Independent proof-relevant meaning of a finite, nonrepeating, unbranched walk to the opposite
terminal.  `seen` contains the already visited prefix before `current`. -/
inductive DeclarativeLocalizedAxialChainWalk
    (input : CertifiedLocalizedCIPInput) :
    input.Atom → input.Atom → List input.Atom → List input.Atom → Prop
  | terminal {previous current seen}
      (forward : input.localizedAxialForwardNeighbors previous current = []) :
      input.DeclarativeLocalizedAxialChainWalk previous current seen [current]
  | linear {previous current seen next tail}
      (forward : input.localizedAxialForwardNeighbors previous current = [next])
      (fresh : next ∉ seen)
      (rest : input.DeclarativeLocalizedAxialChainWalk
        current next (current :: seen) tail) :
      input.DeclarativeLocalizedAxialChainWalk
        previous current seen (current :: tail)

/-- Fuel-bounded physical walk.  Every unresolved topology is refused; no continuation is chosen
from a branch and no ring cut is treated as a terminal. -/
def localizedAxialChainWalk?
    (input : CertifiedLocalizedCIPInput) :
    Nat → input.Atom → input.Atom → List input.Atom → Option (List input.Atom)
  | 0, _previous, _current, _seen => none
  | fuel + 1, previous, current, seen =>
      match input.localizedAxialForwardNeighbors previous current with
      | [] => some [current]
      | [next] =>
          if next ∈ seen then none
          else (input.localizedAxialChainWalk? fuel current next (current :: seen)).map
            (current :: ·)
      | _first :: _second :: _rest => none

/-- Every successful graph walk has the independent terminal/linear derivation above. -/
theorem localizedAxialChainWalk?_sound
    (input : CertifiedLocalizedCIPInput) :
    ∀ fuel previous current seen path,
      input.localizedAxialChainWalk? fuel previous current seen = some path →
        input.DeclarativeLocalizedAxialChainWalk previous current seen path
  | 0, previous, current, seen, path, computed => by
      simp [localizedAxialChainWalk?] at computed
  | fuel + 1, previous, current, seen, path, computed => by
      unfold localizedAxialChainWalk? at computed
      generalize forwardIdentity :
          input.localizedAxialForwardNeighbors previous current = forward at computed
      cases forward with
      | nil =>
          simp at computed
          subst path
          exact DeclarativeLocalizedAxialChainWalk.terminal forwardIdentity
      | cons next rest =>
          cases rest with
          | nil =>
              by_cases repeated : next ∈ seen
              · simp [repeated] at computed
              · cases tailComputed : input.localizedAxialChainWalk?
                    fuel current next (current :: seen) with
                | none => simp [repeated, tailComputed] at computed
                | some tail =>
                    simp [repeated, tailComputed] at computed
                    subst path
                    exact DeclarativeLocalizedAxialChainWalk.linear
                      forwardIdentity repeated
                      (input.localizedAxialChainWalk?_sound fuel current next
                        (current :: seen) tail tailComputed)
          | cons second more => simp at computed

/-- The declarative walk is executable at every fuel at least its returned path length.  This
separates semantic linearity from the later finite-cardinality bound. -/
theorem localizedAxialChainWalk?_complete_of_length
    (input : CertifiedLocalizedCIPInput)
    {previous current : input.Atom} {seen path : List input.Atom}
    (derived : input.DeclarativeLocalizedAxialChainWalk
      previous current seen path) :
    ∀ fuel, path.length ≤ fuel →
      input.localizedAxialChainWalk? fuel previous current seen = some path := by
  induction derived with
  | terminal forward =>
      intro fuel enough
      cases fuel with
      | zero => simp at enough
      | succ fuel => simp [localizedAxialChainWalk?, forward]
  | @linear previous current seen next tail forward fresh rest inductionHypothesis =>
      intro fuel enough
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          have tailEnough : tail.length ≤ fuel := by
            apply Nat.le_of_succ_le_succ
            simpa using enough
          simp [localizedAxialChainWalk?, forward, fresh,
            inductionHypothesis fuel tailEnough]

/-- A declarative walk always begins at its stated current atom. -/
theorem DeclarativeLocalizedAxialChainWalk.head?_eq_current
    (input : CertifiedLocalizedCIPInput)
    {previous current : input.Atom} {seen path : List input.Atom}
    (derived : input.DeclarativeLocalizedAxialChainWalk
      previous current seen path) :
    path.head? = some current := by
  cases derived <;> rfl

/-- Consecutive atoms in every declarative axial walk are connected by physical double bonds. -/
theorem DeclarativeLocalizedAxialChainWalk.isChain_doubleBond
    (input : CertifiedLocalizedCIPInput)
    {previous current : input.Atom} {seen path : List input.Atom}
    (derived : input.DeclarativeLocalizedAxialChainWalk
      previous current seen path) :
    List.IsChain (fun left right => input.moleculeGraph.bond left right = 2) path := by
  induction derived with
  | terminal => exact List.isChain_singleton _
  | @linear previous current seen next tail forward fresh rest inductionHypothesis =>
      have nextPresent : next ∈
          input.localizedAxialForwardNeighbors previous current := by
        simp [forward]
      have doubleBond : input.moleculeGraph.bond current next = 2 :=
        (input.mem_localizedAxialForwardNeighbors_iff
          previous current next).mp nextPresent |>.1
      apply inductionHypothesis.cons
      intro head headPresent
      rw [DeclarativeLocalizedAxialChainWalk.head?_eq_current input rest] at headPresent
      simp only [Option.mem_def, Option.some.injEq] at headPresent
      subst head
      exact doubleBond

/-- Under the executable caller invariant `current ∉ seen`, a declarative walk is nonrepeating
and none of its returned atoms belongs to the prior prefix. -/
theorem DeclarativeLocalizedAxialChainWalk.nodup_and_avoids_seen
    (input : CertifiedLocalizedCIPInput)
    {previous current : input.Atom} {seen path : List input.Atom}
    (derived : input.DeclarativeLocalizedAxialChainWalk
      previous current seen path)
    (currentFresh : current ∉ seen) :
    path.Nodup ∧ ∀ atom, atom ∈ path → atom ∉ seen := by
  induction derived with
  | terminal forward =>
      exact ⟨by simp, by
        intro atom present
        simp only [List.mem_singleton] at present
        subst atom
        exact currentFresh⟩
  | @linear previous current seen next tail forward fresh rest inductionHypothesis =>
      have nextPresent : next ∈
          input.localizedAxialForwardNeighbors previous current := by
        simp [forward]
      have nextDouble : input.moleculeGraph.bond current next = 2 :=
        (input.mem_localizedAxialForwardNeighbors_iff
          previous current next).mp nextPresent |>.1
      have nextNeCurrent : next ≠ current := by
        intro same
        subst next
        have impossible : (0 : Nat) = 2 := by
          simpa only [input.moleculeGraph.bond_self] using nextDouble
        exact Nat.noConfusion impossible
      have nextFreshPrefix : next ∉ current :: seen := by
        simp [nextNeCurrent, fresh]
      obtain ⟨tailNodup, tailAvoids⟩ := inductionHypothesis nextFreshPrefix
      constructor
      · rw [List.nodup_cons]
        exact ⟨
          fun currentPresent => tailAvoids current currentPresent (by simp),
          tailNodup⟩
      · intro atom present
        rw [List.mem_cons] at present
        rcases present with identity | tailPresent
        · subst atom
          exact currentFresh
        · exact fun atomSeen => tailAvoids atom tailPresent (by simp [atomSeen])

/-- A complete open path associated with one independently valid terminal root. -/
def DeclarativeLocalizedAxialChainFromRoot
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRootCandidate) (path : List input.Atom) : Prop :=
  input.DeclarativeLocalizedAxialRootCandidate root ∧
    ∃ tail,
      path = root.terminal :: tail ∧
      input.DeclarativeLocalizedAxialChainWalk
        root.terminal root.firstAxis [root.terminal] tail

/-- Follow one terminal root through the complete open order-two chain. -/
def localizedAxialChainFromRoot?
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.LocalizedAxialRootCandidate) : Option (List input.Atom) :=
  (input.localizedAxialChainWalk?
    fuel root.terminal root.firstAxis [root.terminal]).map (root.terminal :: ·)

/-- Root validity plus successful execution implies the independent complete path relation. -/
theorem localizedAxialChainFromRoot?_sound
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.LocalizedAxialRootCandidate)
    (rootValid : input.DeclarativeLocalizedAxialRootCandidate root)
    (path : List input.Atom)
    (computed : input.localizedAxialChainFromRoot? fuel root = some path) :
    input.DeclarativeLocalizedAxialChainFromRoot root path := by
  unfold localizedAxialChainFromRoot? at computed
  cases tailComputed : input.localizedAxialChainWalk?
      fuel root.terminal root.firstAxis [root.terminal] with
  | none => simp [tailComputed] at computed
  | some tail =>
      simp [tailComputed] at computed
      subst path
      exact ⟨rootValid, tail, rfl,
        input.localizedAxialChainWalk?_sound fuel root.terminal root.firstAxis
          [root.terminal] tail tailComputed⟩

/-- Any independently derived root path runs once fuel covers its non-root tail. -/
theorem localizedAxialChainFromRoot?_complete_of_length
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRootCandidate) (path : List input.Atom)
    (derived : input.DeclarativeLocalizedAxialChainFromRoot root path)
    (fuel : Nat) (enough : path.length ≤ fuel + 1) :
    input.localizedAxialChainFromRoot? fuel root = some path := by
  rcases derived with ⟨_rootValid, tail, pathIdentity, walk⟩
  subst path
  unfold localizedAxialChainFromRoot?
  have tailEnough : tail.length ≤ fuel := by simpa using enough
  rw [input.localizedAxialChainWalk?_complete_of_length walk fuel tailEnough]
  rfl

/-- Every independently derived root path is simple.  In particular its length is bounded by the
finite semantic atom carrier, so the molecule-size traversal budget is sufficient. -/
theorem DeclarativeLocalizedAxialChainFromRoot.path_nodup
    (input : CertifiedLocalizedCIPInput)
    {root : input.LocalizedAxialRootCandidate} {path : List input.Atom}
    (derived : input.DeclarativeLocalizedAxialChainFromRoot root path) :
    path.Nodup := by
  rcases derived with ⟨rootValid, tail, pathIdentity, walk⟩
  have firstNeTerminal : root.firstAxis ≠ root.terminal := by
    intro same
    have doubleBond := rootValid.1
    rw [same, input.moleculeGraph.bond_self] at doubleBond
    exact Nat.noConfusion doubleBond
  obtain ⟨tailNodup, tailAvoids⟩ :=
    DeclarativeLocalizedAxialChainWalk.nodup_and_avoids_seen input walk
      (by simp [firstNeTerminal])
  rw [pathIdentity, List.nodup_cons]
  exact ⟨fun terminalPresent =>
    tailAvoids root.terminal terminalPresent (by simp), tailNodup⟩

/-- The complete root path is a chain of physical double bonds from terminal to terminal. -/
theorem DeclarativeLocalizedAxialChainFromRoot.path_isChain_doubleBond
    (input : CertifiedLocalizedCIPInput)
    {root : input.LocalizedAxialRootCandidate} {path : List input.Atom}
    (derived : input.DeclarativeLocalizedAxialChainFromRoot root path) :
    List.IsChain (fun left right => input.moleculeGraph.bond left right = 2) path := by
  rcases derived with ⟨rootValid, tail, pathIdentity, walk⟩
  rw [pathIdentity]
  apply (DeclarativeLocalizedAxialChainWalk.isChain_doubleBond input walk).cons
  intro head headPresent
  rw [DeclarativeLocalizedAxialChainWalk.head?_eq_current input walk] at headPresent
  simp only [Option.mem_def, Option.some.injEq] at headPresent
  subst head
  exact rootValid.1

/-- One canonically oriented, open, nonordinary even cumulene axis. -/
structure LocalizedEvenAxialChainFrame (input : CertifiedLocalizedCIPInput) where
  root : input.LocalizedAxialRootCandidate
  path : List input.Atom
  deriving DecidableEq, Repr

def LocalizedEvenAxialChainFrame.doubleBondCount
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedEvenAxialChainFrame) : Nat :=
  frame.path.length - 1

/-- Independent meaning of the molecule-wide even-axis perception result. -/
def DeclarativeLocalizedEvenAxialChainFrame
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedEvenAxialChainFrame) : Prop :=
  input.DeclarativeLocalizedAxialChainFromRoot frame.root frame.path ∧
    1 < frame.doubleBondCount ∧ Even frame.doubleBondCount ∧
    ∃ oppositeTerminal,
      frame.path.getLast? = some oppositeTerminal ∧
      frame.root.terminal < oppositeTerminal

/-- Authority-facing statement that a molecule-level even-axis frame is an open consecutive
double-bond chain whose unique P-93 route is even-cumulene analysis. -/
def DeclarativeLocalizedEvenAxialP93Route
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedEvenAxialChainFrame) : Prop :=
  ∃ nonempty : frame.doubleBondCount ≠ 0,
    BlueBookP93.Acyclic.DoubleBondAnalysisRouteApplies
      (.openChain frame.doubleBondCount nonempty) .evenOpenCumulene

/-- Independent molecule-level even-axis meaning refines the independent P-93 topology/parity
routing relation. -/
theorem DeclarativeLocalizedEvenAxialChainFrame.authority_route
    (input : CertifiedLocalizedCIPInput)
    {frame : input.LocalizedEvenAxialChainFrame}
    (derived : input.DeclarativeLocalizedEvenAxialChainFrame frame) :
    input.DeclarativeLocalizedEvenAxialP93Route frame := by
  have longer : 1 < frame.doubleBondCount := derived.2.1
  have even : Even frame.doubleBondCount := derived.2.2.1
  have nonempty : frame.doubleBondCount ≠ 0 := by omega
  have notOrdinary : frame.doubleBondCount ≠ 1 := by omega
  have notOdd : ¬Odd frame.doubleBondCount := by
    intro odd
    exact (Nat.not_even_iff_odd.mpr odd) even
  exact ⟨nonempty, notOrdinary, notOdd⟩

/-- Classify one root as an open even cumulene and retain only the canonical terminal direction. -/
def localizedEvenAxialChainFromRoot?
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRootCandidate) :
    Option input.LocalizedEvenAxialChainFrame := do
  let path ← input.localizedAxialChainFromRoot?
    (input.certified.input.molecule.atomCount + 1) root
  let frame : input.LocalizedEvenAxialChainFrame := { root, path }
  if _even : 1 < frame.doubleBondCount ∧ Even frame.doubleBondCount then
    let oppositeTerminal ← path.getLast?
    if _canonical : root.terminal < oppositeTerminal then some frame else none
  else none

/-- Successful single-root classification has the exact open-chain, parity, and canonical
orientation meaning. -/
theorem localizedEvenAxialChainFromRoot?_sound
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRootCandidate)
    (rootValid : input.DeclarativeLocalizedAxialRootCandidate root)
    (frame : input.LocalizedEvenAxialChainFrame)
    (computed : input.localizedEvenAxialChainFromRoot? root = some frame) :
    input.DeclarativeLocalizedEvenAxialChainFrame frame := by
  unfold localizedEvenAxialChainFromRoot? at computed
  cases pathComputed : input.localizedAxialChainFromRoot?
      (input.certified.input.molecule.atomCount + 1) root with
  | none => simp [pathComputed] at computed
  | some path =>
      let candidate : input.LocalizedEvenAxialChainFrame := { root, path }
      by_cases even : 1 < candidate.doubleBondCount ∧ Even candidate.doubleBondCount
      · cases lastComputed : path.getLast? with
        | none => simp [pathComputed, candidate, even, lastComputed] at computed
        | some oppositeTerminal =>
            by_cases canonical : root.terminal < oppositeTerminal
            · simp [pathComputed, candidate, even, lastComputed, canonical] at computed
              subst frame
              exact ⟨
                input.localizedAxialChainFromRoot?_sound
                  (input.certified.input.molecule.atomCount + 1)
                  root rootValid path pathComputed,
                even.1, even.2, oppositeTerminal, lastComputed, canonical⟩
            · simp [pathComputed, candidate, even, lastComputed, canonical] at computed
      · simp [pathComputed, candidate, even] at computed

/-- Independent even-frame evidence is complete once the finite walk bound covers its path. -/
theorem localizedEvenAxialChainFromRoot?_complete_of_length
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedEvenAxialChainFrame)
    (derived : input.DeclarativeLocalizedEvenAxialChainFrame frame)
    (enough : frame.path.length ≤ input.certified.input.molecule.atomCount + 2) :
    input.localizedEvenAxialChainFromRoot? frame.root = some frame := by
  rcases derived with ⟨pathDerived, longer, even, oppositeTerminal,
    lastComputed, canonical⟩
  change 1 < frame.path.length - 1 at longer
  change Even (frame.path.length - 1) at even
  have pathComputed : input.localizedAxialChainFromRoot?
      (input.certified.input.molecule.atomCount + 1) frame.root = some frame.path :=
    input.localizedAxialChainFromRoot?_complete_of_length frame.root frame.path
      pathDerived (input.certified.input.molecule.atomCount + 1) (by simpa using enough)
  unfold localizedEvenAxialChainFromRoot?
  rw [pathComputed]
  simp [LocalizedEvenAxialChainFrame.doubleBondCount, longer, even,
    lastComputed, canonical]

/-- The independent frame's simple path is automatically no longer than the molecular atom
carrier. -/
theorem DeclarativeLocalizedEvenAxialChainFrame.path_length_le_atomCount
    (input : CertifiedLocalizedCIPInput)
    {frame : input.LocalizedEvenAxialChainFrame}
    (derived : input.DeclarativeLocalizedEvenAxialChainFrame frame) :
    frame.path.length ≤ input.certified.input.molecule.atomCount := by
  have bounded :=
    (DeclarativeLocalizedAxialChainFromRoot.path_nodup input derived.1).length_le_card
  simpa [CertifiedLocalizedCIPInput.Atom] using bounded

/-- Every perceived canonical even-axis frame retains the exact double-bond chain relation. -/
theorem DeclarativeLocalizedEvenAxialChainFrame.path_isChain_doubleBond
    (input : CertifiedLocalizedCIPInput)
    {frame : input.LocalizedEvenAxialChainFrame}
    (derived : input.DeclarativeLocalizedEvenAxialChainFrame frame) :
    List.IsChain (fun left right => input.moleculeGraph.bond left right = 2) frame.path :=
  DeclarativeLocalizedAxialChainFromRoot.path_isChain_doubleBond input derived.1

/-- Therefore the selected molecule-size budget is unconditionally complete for every
independently valid open even-axis frame. -/
theorem localizedEvenAxialChainFromRoot?_complete
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedEvenAxialChainFrame)
    (derived : input.DeclarativeLocalizedEvenAxialChainFrame frame) :
    input.localizedEvenAxialChainFromRoot? frame.root = some frame := by
  apply input.localizedEvenAxialChainFromRoot?_complete_of_length frame derived
  have bounded :=
    DeclarativeLocalizedEvenAxialChainFrame.path_length_le_atomCount input derived
  omega

/-- Canonical molecule-wide open-even-axis carrier. -/
def localizedEvenAxialChains (input : CertifiedLocalizedCIPInput) :
    List input.LocalizedEvenAxialChainFrame :=
  input.localizedAxialRootCandidates.filterMap input.localizedEvenAxialChainFromRoot?

/-- Every member of the molecule-wide carrier satisfies the independent even-axis relation. -/
theorem mem_localizedEvenAxialChains_implies_declarative
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedEvenAxialChainFrame)
    (present : frame ∈ input.localizedEvenAxialChains) :
    input.DeclarativeLocalizedEvenAxialChainFrame frame := by
  rw [localizedEvenAxialChains, List.mem_filterMap] at present
  obtain ⟨root, rootPresent, computed⟩ := present
  exact input.localizedEvenAxialChainFromRoot?_sound root
    ((input.mem_localizedAxialRootCandidates_iff root).mp rootPresent)
    frame computed

/-- Every molecule-wide perceived even axis therefore has the independently transcribed P-93
open-even-cumulene route, not merely a production-specific parity flag. -/
theorem mem_localizedEvenAxialChains_implies_authority_route
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedEvenAxialChainFrame)
    (present : frame ∈ input.localizedEvenAxialChains) :
    input.DeclarativeLocalizedEvenAxialP93Route frame :=
  (input.mem_localizedEvenAxialChains_implies_declarative frame present).authority_route input

/-- Subject only to the explicit finite path-length bound, whole-molecule membership is exactly
the independent canonical even-axis relation. -/
theorem mem_localizedEvenAxialChains_iff_of_length_le
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedEvenAxialChainFrame)
    (enough : frame.path.length ≤ input.certified.input.molecule.atomCount + 2) :
    frame ∈ input.localizedEvenAxialChains ↔
      input.DeclarativeLocalizedEvenAxialChainFrame frame := by
  constructor
  · exact input.mem_localizedEvenAxialChains_implies_declarative frame
  · intro derived
    rw [localizedEvenAxialChains, List.mem_filterMap]
    exact ⟨frame.root,
      (input.mem_localizedAxialRootCandidates_iff frame.root).mpr derived.1.1,
      input.localizedEvenAxialChainFromRoot?_complete_of_length frame derived enough⟩

/-- Exact unconditional molecule-wide coverage of canonical open even cumulene axes. -/
theorem mem_localizedEvenAxialChains_iff
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedEvenAxialChainFrame) :
    frame ∈ input.localizedEvenAxialChains ↔
      input.DeclarativeLocalizedEvenAxialChainFrame frame := by
  constructor
  · exact input.mem_localizedEvenAxialChains_implies_declarative frame
  · intro derived
    rw [localizedEvenAxialChains, List.mem_filterMap]
    exact ⟨frame.root,
      (input.mem_localizedAxialRootCandidates_iff frame.root).mpr derived.1.1,
      input.localizedEvenAxialChainFromRoot?_complete frame derived⟩

/-- Canonical root identity prevents duplicate frames in the molecule-wide carrier. -/
theorem localizedEvenAxialChains_nodup
    (input : CertifiedLocalizedCIPInput) :
    input.localizedEvenAxialChains.Nodup := by
  unfold localizedEvenAxialChains
  apply List.Nodup.filterMap
  · intro left right frame leftComputed rightComputed
    unfold localizedEvenAxialChainFromRoot? at leftComputed rightComputed
    cases leftPathComputed : input.localizedAxialChainFromRoot?
        (input.certified.input.molecule.atomCount + 1) left with
    | none => simp [leftPathComputed] at leftComputed
    | some leftPath =>
        cases rightPathComputed : input.localizedAxialChainFromRoot?
            (input.certified.input.molecule.atomCount + 1) right with
        | none => simp [rightPathComputed] at rightComputed
        | some rightPath =>
            let leftFrame : input.LocalizedEvenAxialChainFrame :=
              { root := left, path := leftPath }
            let rightFrame : input.LocalizedEvenAxialChainFrame :=
              { root := right, path := rightPath }
            by_cases leftEven :
                1 < leftFrame.doubleBondCount ∧ Even leftFrame.doubleBondCount
            · cases leftLastComputed : leftPath.getLast? with
              | none => simp [leftPathComputed, leftFrame, leftEven,
                  leftLastComputed] at leftComputed
              | some leftLast =>
                  by_cases leftCanonical : left.terminal < leftLast
                  · simp [leftPathComputed, leftFrame, leftEven, leftLastComputed,
                      leftCanonical] at leftComputed
                    subst frame
                    by_cases rightEven :
                        1 < rightFrame.doubleBondCount ∧ Even rightFrame.doubleBondCount
                    · cases rightLastComputed : rightPath.getLast? with
                      | none => simp [rightPathComputed, rightFrame, rightEven,
                          rightLastComputed] at rightComputed
                      | some rightLast =>
                          by_cases rightCanonical : right.terminal < rightLast
                          · simp [rightPathComputed, rightFrame, rightEven,
                              rightLastComputed, rightCanonical] at rightComputed
                            exact rightComputed.1.symm
                          · simp [rightPathComputed, rightFrame, rightEven,
                              rightLastComputed, rightCanonical] at rightComputed
                    · simp [rightPathComputed, rightFrame, rightEven] at rightComputed
                  · simp [leftPathComputed, leftFrame, leftEven, leftLastComputed,
                      leftCanonical] at leftComputed
            · simp [leftPathComputed, leftFrame, leftEven] at leftComputed
  · exact input.localizedAxialRootCandidates_nodup

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
