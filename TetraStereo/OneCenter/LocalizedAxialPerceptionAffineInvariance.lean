import TetraStereo.OneCenter.CIPRule3CyclicDescriptorAffineInvariance
import TetraStereo.OneCenter.LocalizedAxialChainPerception

/-!
# Coordinate naturality of open axial-chain perception

Coordinate mapping does not alter constitution.  Because the perceived roots and chains are
dependent types indexed by their input, this fact nevertheless requires explicit transport
theorems.  They are supplied here for every root, walk, canonical even-chain frame, and the final
deduplicated perception list.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

def LocalizedAxialRootCandidate.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (candidate : input.LocalizedAxialRootCandidate)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedAxialRootCandidate :=
  { terminal := candidate.terminal
    firstAxis := candidate.firstAxis }

@[simp] theorem localizedAxialRootCandidateAt?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (terminal : input.Atom)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedAxialRootCandidateAt? terminal =
      (input.localizedAxialRootCandidateAt? terminal).map
        (fun candidate => candidate.mapSpatialPoints mapPoint) := by
  unfold localizedAxialRootCandidateAt?
  rw [localizedOrderTwoNeighbors_mapSpatialPoints input mapPoint terminal]
  cases input.localizedOrderTwoNeighbors terminal with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second more => rfl

private theorem filterMap_rootCandidates_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    ∀ atoms : List input.Atom,
      atoms.filterMap
          (input.mapSpatialPoints mapPoint).localizedAxialRootCandidateAt? =
        (atoms.filterMap input.localizedAxialRootCandidateAt?).map
          (fun candidate => candidate.mapSpatialPoints mapPoint)
  | [] => rfl
  | atom :: atoms => by
      simp only [List.filterMap_cons]
      rw [localizedAxialRootCandidateAt?_mapSpatialPoints]
      cases input.localizedAxialRootCandidateAt? atom <;>
        simp [filterMap_rootCandidates_mapSpatialPoints input mapPoint atoms]

@[simp] theorem localizedAxialRootCandidates_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedAxialRootCandidates =
      input.localizedAxialRootCandidates.map
        (fun candidate => candidate.mapSpatialPoints mapPoint) := by
  unfold localizedAxialRootCandidates
  exact filterMap_rootCandidates_mapSpatialPoints input mapPoint
    ((Finset.univ : Finset input.Atom).sort (· ≤ ·))

@[simp] theorem localizedAxialForwardNeighbors_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (previous current : input.Atom)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedAxialForwardNeighbors previous current =
      input.localizedAxialForwardNeighbors previous current := by
  unfold localizedAxialForwardNeighbors
  rw [localizedOrderTwoNeighbors_mapSpatialPoints input mapPoint current]
  apply List.filter_congr
  intro neighbor present
  rfl

@[simp] theorem localizedAxialChainWalk?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3) :
    ∀ fuel previous current seen,
      (input.mapSpatialPoints mapPoint).localizedAxialChainWalk?
          fuel previous current seen =
        input.localizedAxialChainWalk? fuel previous current seen
  | 0, previous, current, seen => rfl
  | fuel + 1, previous, current, seen => by
      unfold localizedAxialChainWalk?
      rw [localizedAxialForwardNeighbors_mapSpatialPoints]
      cases forwardEq : input.localizedAxialForwardNeighbors previous current with
      | nil => rfl
      | cons next rest =>
          cases rest with
          | cons second more => rfl
          | nil =>
              by_cases repeated : next ∈ seen
              · simp [repeated]
              · simp only [repeated, ↓reduceIte,
                  localizedAxialChainWalk?_mapSpatialPoints input mapPoint fuel]
                apply Option.ext
                intro path
                rfl

@[simp] theorem localizedAxialChainFromRoot?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.LocalizedAxialRootCandidate)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedAxialChainFromRoot?
        fuel (root.mapSpatialPoints mapPoint) =
      input.localizedAxialChainFromRoot? fuel root := by
  unfold localizedAxialChainFromRoot?
  simp only [LocalizedAxialRootCandidate.mapSpatialPoints,
    localizedAxialChainWalk?_mapSpatialPoints]
  apply Option.ext
  intro path
  rfl

def LocalizedEvenAxialChainFrame.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (frame : input.LocalizedEvenAxialChainFrame)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedEvenAxialChainFrame :=
  { root := frame.root.mapSpatialPoints mapPoint
    path := frame.path }

@[simp] theorem localizedEvenAxialChainFromRoot?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRootCandidate)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedEvenAxialChainFromRoot?
        (root.mapSpatialPoints mapPoint) =
      (input.localizedEvenAxialChainFromRoot? root).map
        (fun frame => frame.mapSpatialPoints mapPoint) := by
  unfold localizedEvenAxialChainFromRoot?
  simp only [atomCount_mapSpatialPoints]
  rw [localizedAxialChainFromRoot?_mapSpatialPoints]
  cases pathEq : input.localizedAxialChainFromRoot?
      (input.certified.input.molecule.atomCount + 1) root with
  | none => rfl
  | some path =>
      by_cases even : 1 < path.length - 1 ∧ Even (path.length - 1)
      · simp only [LocalizedEvenAxialChainFrame.doubleBondCount, even, and_self,
          ↓reduceIte]
        cases lastEq : path.getLast? with
        | none => simp [lastEq]
        | some opposite =>
            by_cases canonical : root.terminal < opposite <;>
              simp [lastEq, canonical, LocalizedEvenAxialChainFrame.mapSpatialPoints,
                LocalizedAxialRootCandidate.mapSpatialPoints]
      · simp [LocalizedEvenAxialChainFrame.doubleBondCount,
          LocalizedEvenAxialChainFrame.mapSpatialPoints, even]

private theorem filterMap_evenChains_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    ∀ roots : List input.LocalizedAxialRootCandidate,
      (roots.map fun root => root.mapSpatialPoints mapPoint).filterMap
          (input.mapSpatialPoints mapPoint).localizedEvenAxialChainFromRoot? =
        (roots.filterMap input.localizedEvenAxialChainFromRoot?).map
          (fun frame => frame.mapSpatialPoints mapPoint)
  | [] => rfl
  | root :: roots => by
      simp only [List.map_cons, List.filterMap_cons]
      rw [localizedEvenAxialChainFromRoot?_mapSpatialPoints]
      cases input.localizedEvenAxialChainFromRoot? root <;>
        simp [filterMap_evenChains_mapSpatialPoints input mapPoint roots]

@[simp] theorem localizedEvenAxialChains_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedEvenAxialChains =
      input.localizedEvenAxialChains.map
        (fun frame => frame.mapSpatialPoints mapPoint) := by
  unfold localizedEvenAxialChains
  rw [localizedAxialRootCandidates_mapSpatialPoints]
  exact filterMap_evenChains_mapSpatialPoints input mapPoint
    input.localizedAxialRootCandidates

/-- Transport a proof-carrying member of the canonical even-axis carrier. -/
def LocalizedEvenAxialChain.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (axis : input.LocalizedEvenAxialChain)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedEvenAxialChain :=
  ⟨axis.1.mapSpatialPoints mapPoint, by
    rw [localizedEvenAxialChains_mapSpatialPoints]
    exact List.mem_map.mpr ⟨axis.1, axis.2, rfl⟩⟩

@[simp] theorem LocalizedEvenAxialChain.mapSpatialPoints_val
    {input : CertifiedLocalizedCIPInput}
    (axis : input.LocalizedEvenAxialChain)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (axis.mapSpatialPoints mapPoint).1 = axis.1.mapSpatialPoints mapPoint :=
  rfl

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
