import TetraStereo.OneCenter.AuthoritativeLocalizedCIPAnalysis

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Molecule-wide localized axial-root perception

The tetrahedral occurrence carrier cannot discover a molecule whose only final stereogenic unit
is an axis.  This module begins the independent axial carrier at the semantic graph itself.  It
enumerates every atom having exactly one physical order-two neighbour, together with that first
axis partner.  Ordinary double bonds and odd cumulenes are intentionally still candidates here;
chain parity and endpoint stereogenicity belong to later filters.
-/

namespace CertifiedLocalizedCIPInput

/-- Canonically ordered physical order-two neighbours of one semantic atom. -/
def localizedOrderTwoNeighbors
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) : List input.Atom :=
  ((input.moleculeGraph.neighborFinset atom).filter fun neighbor =>
      input.moleculeGraph.bond atom neighbor = 2).sort (· ≤ ·)

@[simp] theorem mem_localizedOrderTwoNeighbors_iff
    (input : CertifiedLocalizedCIPInput) (atom neighbor : input.Atom) :
    neighbor ∈ input.localizedOrderTwoNeighbors atom ↔
      input.moleculeGraph.bond atom neighbor = 2 := by
  simp only [localizedOrderTwoNeighbors, Finset.mem_sort, Finset.mem_filter]
  constructor
  · exact fun present => present.2
  · intro doubleBond
    exact ⟨by simp [MoleculeGraph.Adj, doubleBond], doubleBond⟩

theorem localizedOrderTwoNeighbors_nodup
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    (input.localizedOrderTwoNeighbors atom).Nodup := by
  exact Finset.sort_nodup _ _

/-- One oriented molecule-wide candidate starts at a terminal atom and enters its unique
order-two neighbour. -/
structure LocalizedAxialRootCandidate (input : CertifiedLocalizedCIPInput) where
  terminal : input.Atom
  firstAxis : input.Atom
  deriving DecidableEq, Repr

/-- Independent graph meaning of a terminal order-two start. -/
def DeclarativeLocalizedAxialRootCandidate
    (input : CertifiedLocalizedCIPInput)
    (candidate : input.LocalizedAxialRootCandidate) : Prop :=
  input.moleculeGraph.bond candidate.terminal candidate.firstAxis = 2 ∧
    ∀ neighbor, input.moleculeGraph.bond candidate.terminal neighbor = 2 →
      neighbor = candidate.firstAxis

/-- Detect the unique first axis partner at one atom. -/
def localizedAxialRootCandidateAt?
    (input : CertifiedLocalizedCIPInput) (terminal : input.Atom) :
    Option input.LocalizedAxialRootCandidate :=
  match input.localizedOrderTwoNeighbors terminal with
  | [firstAxis] => some { terminal, firstAxis }
  | _ => none

/-- A detected root is exactly an atom with one physical order-two neighbour. -/
theorem localizedAxialRootCandidateAt?_sound
    (input : CertifiedLocalizedCIPInput) (terminal : input.Atom)
    (candidate : input.LocalizedAxialRootCandidate)
    (computed : input.localizedAxialRootCandidateAt? terminal = some candidate) :
    candidate.terminal = terminal ∧
      input.DeclarativeLocalizedAxialRootCandidate candidate := by
  unfold localizedAxialRootCandidateAt? at computed
  cases neighborsIdentity : input.localizedOrderTwoNeighbors terminal with
  | nil => simp [neighborsIdentity] at computed
  | cons first rest =>
      cases rest with
      | nil =>
          simp [neighborsIdentity] at computed
          subst candidate
          refine ⟨rfl,
            (input.mem_localizedOrderTwoNeighbors_iff terminal first).mp ?_, ?_⟩
          · simp [neighborsIdentity]
          · intro neighbor doubleBond
            have present : neighbor ∈ input.localizedOrderTwoNeighbors terminal :=
              (input.mem_localizedOrderTwoNeighbors_iff terminal neighbor).mpr doubleBond
            simpa [neighborsIdentity] using present
      | cons second more => simp [neighborsIdentity] at computed

/-- The graph relation is also complete: every atom with one order-two neighbour is detected. -/
theorem localizedAxialRootCandidateAt?_complete
    (input : CertifiedLocalizedCIPInput)
    (candidate : input.LocalizedAxialRootCandidate)
    (derived : input.DeclarativeLocalizedAxialRootCandidate candidate) :
    input.localizedAxialRootCandidateAt? candidate.terminal = some candidate := by
  have exactMembers : ∀ neighbor,
      neighbor ∈ input.localizedOrderTwoNeighbors candidate.terminal ↔
        neighbor = candidate.firstAxis := by
    intro neighbor
    rw [input.mem_localizedOrderTwoNeighbors_iff]
    constructor
    · exact derived.2 neighbor
    · intro identity
      subst neighbor
      exact derived.1
  have singleton : input.localizedOrderTwoNeighbors candidate.terminal =
      [candidate.firstAxis] := by
    generalize neighborsIdentity :
        input.localizedOrderTwoNeighbors candidate.terminal = neighbors
    cases neighbors with
    | nil =>
        have present : candidate.firstAxis ∈
            input.localizedOrderTwoNeighbors candidate.terminal :=
          (input.mem_localizedOrderTwoNeighbors_iff
            candidate.terminal candidate.firstAxis).mpr derived.1
        simp [neighborsIdentity] at present
    | cons first rest =>
        have firstPresent : first ∈
            input.localizedOrderTwoNeighbors candidate.terminal := by
          simp [neighborsIdentity]
        have firstIdentity : first = candidate.firstAxis :=
          (exactMembers first).mp firstPresent
        cases rest with
        | nil => simp [firstIdentity]
        | cons second more =>
            have secondPresent : second ∈
                input.localizedOrderTwoNeighbors candidate.terminal := by
              simp [neighborsIdentity]
            have secondIdentity : second = candidate.firstAxis :=
              (exactMembers second).mp secondPresent
            have nodup := input.localizedOrderTwoNeighbors_nodup candidate.terminal
            rw [neighborsIdentity] at nodup
            simp [firstIdentity, secondIdentity] at nodup
  simp [localizedAxialRootCandidateAt?, singleton]

/-- Every terminal order-two start in the molecule, in ascending terminal-atom order. -/
def localizedAxialRootCandidates (input : CertifiedLocalizedCIPInput) :
    List input.LocalizedAxialRootCandidate :=
  ((Finset.univ : Finset input.Atom).sort (· ≤ ·)).filterMap
    input.localizedAxialRootCandidateAt?

/-- Exact molecule-wide root coverage. -/
theorem mem_localizedAxialRootCandidates_iff
    (input : CertifiedLocalizedCIPInput)
    (candidate : input.LocalizedAxialRootCandidate) :
    candidate ∈ input.localizedAxialRootCandidates ↔
      input.DeclarativeLocalizedAxialRootCandidate candidate := by
  rw [localizedAxialRootCandidates, List.mem_filterMap]
  constructor
  · rintro ⟨terminal, _present, computed⟩
    exact (input.localizedAxialRootCandidateAt?_sound
      terminal candidate computed).2
  · intro derived
    exact ⟨candidate.terminal, by simp,
      input.localizedAxialRootCandidateAt?_complete candidate derived⟩

/-- The molecule-wide executable root carrier contains no duplicate candidate. -/
theorem localizedAxialRootCandidates_nodup
    (input : CertifiedLocalizedCIPInput) :
    input.localizedAxialRootCandidates.Nodup := by
  unfold localizedAxialRootCandidates
  apply List.Nodup.filterMap
  · intro left right candidate leftComputed rightComputed
    have leftTerminal :=
      (input.localizedAxialRootCandidateAt?_sound
        left candidate leftComputed).1
    have rightTerminal :=
      (input.localizedAxialRootCandidateAt?_sound
        right candidate rightComputed).1
    exact leftTerminal.symm.trans rightTerminal
  · exact Finset.sort_nodup _ _

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
