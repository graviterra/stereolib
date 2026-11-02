import TetraStereo.OneCenter.LocalizedAxialChainPerception

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Molecule-wide open odd-cumulene perception

The shared open order-two-chain walker already rejects cycles, repeated atoms, branches, and fuel
truncation.  This module selects exactly the nonordinary odd-length paths and chooses the smaller
terminal atom as the unique molecule-wide orientation.  The same carrier applies when the open
cumulative segment is included in a larger cyclic system through non-double ring bonds.
-/

namespace CertifiedLocalizedCIPInput

/-- One canonically oriented maximal open cumulene having an odd number greater than one of
consecutive physical double bonds. -/
structure LocalizedOddCumuleneChainFrame (input : CertifiedLocalizedCIPInput) where
  root : input.LocalizedAxialRootCandidate
  path : List input.Atom
  deriving DecidableEq, Repr

def LocalizedOddCumuleneChainFrame.doubleBondCount
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedOddCumuleneChainFrame) : Nat :=
  frame.path.length - 1

/-- Independent exact meaning of a canonical molecule-wide odd-cumulene frame. -/
def DeclarativeLocalizedOddCumuleneChainFrame
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedOddCumuleneChainFrame) : Prop :=
  input.DeclarativeLocalizedAxialChainFromRoot frame.root frame.path ∧
    1 < frame.doubleBondCount ∧ Odd frame.doubleBondCount ∧
    ∃ oppositeTerminal,
      frame.path.getLast? = some oppositeTerminal ∧
      frame.root.terminal < oppositeTerminal

/-- Authority-facing P-93 route selected by an independently valid odd frame. -/
def DeclarativeLocalizedOddCumuleneP93Route
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedOddCumuleneChainFrame) : Prop :=
  ∃ nonempty : frame.doubleBondCount ≠ 0,
    BlueBookP93.Acyclic.DoubleBondAnalysisRouteApplies
      (.openChain frame.doubleBondCount nonempty) .oddOpenCumulene

theorem DeclarativeLocalizedOddCumuleneChainFrame.authority_route
    (input : CertifiedLocalizedCIPInput)
    {frame : input.LocalizedOddCumuleneChainFrame}
    (derived : input.DeclarativeLocalizedOddCumuleneChainFrame frame) :
    input.DeclarativeLocalizedOddCumuleneP93Route frame := by
  have longer : 1 < frame.doubleBondCount := derived.2.1
  have odd : Odd frame.doubleBondCount := derived.2.2.1
  have nonempty : frame.doubleBondCount ≠ 0 := by omega
  have notOrdinary : frame.doubleBondCount ≠ 1 := by omega
  exact ⟨nonempty, notOrdinary, odd⟩

/-- Classify one exact terminal root as a canonical open odd cumulene. -/
def localizedOddCumuleneChainFromRoot?
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRootCandidate) :
    Option input.LocalizedOddCumuleneChainFrame := do
  let path ← input.localizedAxialChainFromRoot?
    (input.certified.input.molecule.atomCount + 1) root
  let frame : input.LocalizedOddCumuleneChainFrame := { root, path }
  if _odd : 1 < frame.doubleBondCount ∧ Odd frame.doubleBondCount then
    let oppositeTerminal ← path.getLast?
    if _canonical : root.terminal < oppositeTerminal then some frame else none
  else none

/-- Successful single-root classification has the complete chain, odd parity, and canonical
orientation meaning. -/
theorem localizedOddCumuleneChainFromRoot?_sound
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRootCandidate)
    (rootValid : input.DeclarativeLocalizedAxialRootCandidate root)
    (frame : input.LocalizedOddCumuleneChainFrame)
    (computed : input.localizedOddCumuleneChainFromRoot? root = some frame) :
    input.DeclarativeLocalizedOddCumuleneChainFrame frame := by
  unfold localizedOddCumuleneChainFromRoot? at computed
  cases pathComputed : input.localizedAxialChainFromRoot?
      (input.certified.input.molecule.atomCount + 1) root with
  | none => simp [pathComputed] at computed
  | some path =>
      let candidate : input.LocalizedOddCumuleneChainFrame := { root, path }
      by_cases odd : 1 < candidate.doubleBondCount ∧ Odd candidate.doubleBondCount
      · cases lastComputed : path.getLast? with
        | none => simp [pathComputed, candidate, odd, lastComputed] at computed
        | some oppositeTerminal =>
            by_cases canonical : root.terminal < oppositeTerminal
            · simp [pathComputed, candidate, odd, lastComputed, canonical] at computed
              subst frame
              exact ⟨
                input.localizedAxialChainFromRoot?_sound
                  (input.certified.input.molecule.atomCount + 1)
                  root rootValid path pathComputed,
                odd.1, odd.2, oppositeTerminal, lastComputed, canonical⟩
            · simp [pathComputed, candidate, odd, lastComputed, canonical] at computed
      · simp [pathComputed, candidate, odd] at computed

/-- A successful root classifier retains exactly the supplied root. -/
theorem localizedOddCumuleneChainFromRoot?_root
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRootCandidate)
    (frame : input.LocalizedOddCumuleneChainFrame)
    (computed : input.localizedOddCumuleneChainFromRoot? root = some frame) :
    frame.root = root := by
  unfold localizedOddCumuleneChainFromRoot? at computed
  cases pathComputed : input.localizedAxialChainFromRoot?
      (input.certified.input.molecule.atomCount + 1) root with
  | none => simp [pathComputed] at computed
  | some path =>
      let candidate : input.LocalizedOddCumuleneChainFrame := { root, path }
      by_cases odd : 1 < candidate.doubleBondCount ∧ Odd candidate.doubleBondCount
      · cases lastComputed : path.getLast? with
        | none => simp [pathComputed, candidate, odd, lastComputed] at computed
        | some oppositeTerminal =>
            by_cases canonical : root.terminal < oppositeTerminal
            · simp [pathComputed, candidate, odd, lastComputed, canonical] at computed
              subst frame
              rfl
            · simp [pathComputed, candidate, odd, lastComputed, canonical] at computed
      · simp [pathComputed, candidate, odd] at computed

/-- Declarative odd-frame evidence is executable whenever the finite walk budget covers its path. -/
theorem localizedOddCumuleneChainFromRoot?_complete_of_length
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedOddCumuleneChainFrame)
    (derived : input.DeclarativeLocalizedOddCumuleneChainFrame frame)
    (enough : frame.path.length ≤ input.certified.input.molecule.atomCount + 2) :
    input.localizedOddCumuleneChainFromRoot? frame.root = some frame := by
  rcases derived with ⟨pathDerived, longer, odd, oppositeTerminal,
    lastComputed, canonical⟩
  change 1 < frame.path.length - 1 at longer
  change Odd (frame.path.length - 1) at odd
  have pathComputed : input.localizedAxialChainFromRoot?
      (input.certified.input.molecule.atomCount + 1) frame.root = some frame.path :=
    input.localizedAxialChainFromRoot?_complete_of_length frame.root frame.path
      pathDerived (input.certified.input.molecule.atomCount + 1) (by simpa using enough)
  unfold localizedOddCumuleneChainFromRoot?
  rw [pathComputed]
  simp [LocalizedOddCumuleneChainFrame.doubleBondCount, longer, odd,
    lastComputed, canonical]

theorem DeclarativeLocalizedOddCumuleneChainFrame.path_length_le_atomCount
    (input : CertifiedLocalizedCIPInput)
    {frame : input.LocalizedOddCumuleneChainFrame}
    (derived : input.DeclarativeLocalizedOddCumuleneChainFrame frame) :
    frame.path.length ≤ input.certified.input.molecule.atomCount := by
  have bounded :=
    (DeclarativeLocalizedAxialChainFromRoot.path_nodup input derived.1).length_le_card
  simpa [CertifiedLocalizedCIPInput.Atom] using bounded

theorem DeclarativeLocalizedOddCumuleneChainFrame.path_isChain_doubleBond
    (input : CertifiedLocalizedCIPInput)
    {frame : input.LocalizedOddCumuleneChainFrame}
    (derived : input.DeclarativeLocalizedOddCumuleneChainFrame frame) :
    List.IsChain (fun left right => input.moleculeGraph.bond left right = 2) frame.path :=
  DeclarativeLocalizedAxialChainFromRoot.path_isChain_doubleBond input derived.1

/-- The molecule-size budget is unconditionally sufficient for every valid odd frame. -/
theorem localizedOddCumuleneChainFromRoot?_complete
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedOddCumuleneChainFrame)
    (derived : input.DeclarativeLocalizedOddCumuleneChainFrame frame) :
    input.localizedOddCumuleneChainFromRoot? frame.root = some frame := by
  apply input.localizedOddCumuleneChainFromRoot?_complete_of_length frame derived
  have bounded :=
    DeclarativeLocalizedOddCumuleneChainFrame.path_length_le_atomCount input derived
  omega

/-- Canonical molecule-wide carrier of maximal open odd cumulenes. -/
def localizedOddCumuleneChains (input : CertifiedLocalizedCIPInput) :
    List input.LocalizedOddCumuleneChainFrame :=
  input.localizedAxialRootCandidates.filterMap input.localizedOddCumuleneChainFromRoot?

theorem mem_localizedOddCumuleneChains_implies_declarative
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedOddCumuleneChainFrame)
    (present : frame ∈ input.localizedOddCumuleneChains) :
    input.DeclarativeLocalizedOddCumuleneChainFrame frame := by
  rw [localizedOddCumuleneChains, List.mem_filterMap] at present
  obtain ⟨root, rootPresent, computed⟩ := present
  exact input.localizedOddCumuleneChainFromRoot?_sound root
    ((input.mem_localizedAxialRootCandidates_iff root).mp rootPresent) frame computed

theorem mem_localizedOddCumuleneChains_implies_authority_route
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedOddCumuleneChainFrame)
    (present : frame ∈ input.localizedOddCumuleneChains) :
    input.DeclarativeLocalizedOddCumuleneP93Route frame :=
  (input.mem_localizedOddCumuleneChains_implies_declarative frame present).authority_route input

/-- Executable molecule-wide membership is exactly the independent canonical odd-chain relation. -/
theorem mem_localizedOddCumuleneChains_iff
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedOddCumuleneChainFrame) :
    frame ∈ input.localizedOddCumuleneChains ↔
      input.DeclarativeLocalizedOddCumuleneChainFrame frame := by
  constructor
  · exact input.mem_localizedOddCumuleneChains_implies_declarative frame
  · intro derived
    rw [localizedOddCumuleneChains, List.mem_filterMap]
    exact ⟨frame.root,
      (input.mem_localizedAxialRootCandidates_iff frame.root).mpr derived.1.1,
      input.localizedOddCumuleneChainFromRoot?_complete frame derived⟩

/-- Canonical terminal orientation prevents duplicate odd-cumulene frames. -/
theorem localizedOddCumuleneChains_nodup
    (input : CertifiedLocalizedCIPInput) :
    input.localizedOddCumuleneChains.Nodup := by
  unfold localizedOddCumuleneChains
  apply List.Nodup.filterMap
  · intro left right frame leftComputed rightComputed
    have leftRoot := input.localizedOddCumuleneChainFromRoot?_root
      left frame leftComputed
    have rightRoot := input.localizedOddCumuleneChainFromRoot?_root
      right frame rightComputed
    exact leftRoot.symm.trans rightRoot
  · exact input.localizedAxialRootCandidates_nodup

/-- Proof-relevant canonical molecule-wide odd-cumulene carrier. -/
abbrev LocalizedOddCumuleneChain (input : CertifiedLocalizedCIPInput) :=
  { frame : input.LocalizedOddCumuleneChainFrame //
    frame ∈ input.localizedOddCumuleneChains }

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
