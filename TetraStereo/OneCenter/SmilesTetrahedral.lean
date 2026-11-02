import TetraStereo.OneCenter.KernelPermutationEnumeration
import TetraStereo.OneCenter.ExplicitHydrogens
import TetraStereo.OneCenter.BranchSphereKey
import TetraStereo.OneCenter.CanonicalComparisonFrame
import TetraStereo.OneCenter.CanonicalTreeProfile
import TetraStereo.OneCenter.OfficialContextPerception
import TetraStereo.OneCenter.RS
import TetraStereo.OneCenter.DescriptorFixedPoint
import TetraStereo.OneCenter.StereochemicalElements
import TetraStereo.OneCenter.PolyhedralConfiguration
import TetraStereo.OneCenter.CIPAuthoritativeBranchComparator
import TetraStereo.OneCenter.CanonicalRule3Hierarchy

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

/-!
  Stereochemical analysis of an OpenSMILES string.

  This is the library's chemist-facing entry point: a string in, and for every stereogenic unit
  either a descriptor or an explicit, typed reason the assignment was withheld.

  The path is: parse, materialise implicit hydrogens into their OpenSMILES neighbour positions
  (`ExplicitHydrogens`), rank branches with the shared hierarchical digraph (`BranchSphereKey`), and combine
  the written-order parity with the parity of the written-to-priority permutation.  Double bonds
  reuse the same ranking through `ChemistryNormalizationResult.cipDoubleBondStereo?`.

  Everything is computable, so an assignment can be evaluated and checked rather than only reasoned
  about.

  ### The contract

  A descriptor is emitted only when the production ranking strictly separates the branches it
  depends on. A detected candidate that cannot be settled is refused with a reason; units classified
  as non-stereogenic by perception may be omitted. `StereoRefusal` distinguishes a centre with no
  stereochemistry written, a centre tied by both available comparisons, and a centre the ranking
  could not settle — the last being the honest signal that bounded digraph construction or a later
  sequence rule is required. The validation gate permits no known wrong assignment.
-/

/-- A stereogenic unit located in a parsed molecule. -/
inductive StereoUnit where
  | tetrahedral (atom : ℕ)
  | doubleBond (left right : ℕ)
  | axis (start finish : ℕ)
  | plane (atoms : List ℕ)
  | helix (path : List ℕ)
  | polyhedron (center : ℕ)
  deriving DecidableEq, Repr

/-- Why an assignment was withheld. -/
inductive StereoRefusal where
  /-- The input records no stereochemistry at this unit. -/
  | notSpecified
  /-- The centre does not have four neighbours once hydrogens are explicit. -/
  | wrongLigandCount (found : ℕ)
  /-- Two or more branches tie under the currently perceived Rules 1a/1b/2 evidence. -/
  | notStereogenic
  /-- Bounded hierarchical construction or its independent cross-check did not safely order the
  branches. -/
  | rankingUnresolved
  /-- Directional markers around a double bond are absent or contradict each other. -/
  | markerEvidenceUnusable
  /-- The centre lies in two or more rings, where the branch ranking is unfaithful. -/
  | polycyclicCentre
  /-- The centre is not carbon.  Phosphorus, sulfur and nitrogen centres need the lone-pair and
  phantom-ligand conventions this ranking does not implement. -/
  | unsupportedCentreElement
  deriving DecidableEq, Repr

/-- Human-readable label for a refusal, for command-line and report output. -/
def StereoRefusal.label : StereoRefusal → String
  | notSpecified => "no stereochemistry written"
  | wrongLigandCount found => "expected four ligands, found " ++ toString found
  | notStereogenic => "unresolved: pending descriptor-dependent rules"
  | rankingUnresolved => "unresolved: bounded hierarchical comparison inconclusive"
  | markerEvidenceUnusable => "directional markers absent or contradictory"
  | polycyclicCentre => "unresolved: polycyclic centre"
  | unsupportedCentreElement => "unsupported: tetrahedral centre element"

/-- P-91/P-92 descriptor vocabulary for a geometrically enantiomorphic double bond.

Unlike ordinary `E/Z`, these two descriptors are reflection-variant.  Keeping them in a distinct
type makes the public analyzer unable to spell the former non-IUPAC lowercase `e/z` result. -/
inductive SequenceDoubleBondDescriptor where
  | seqCis
  | seqTrans
  deriving DecidableEq, Repr

/-- The result for one stereogenic unit. -/
inductive StereoOutcome where
  | tetrahedral (value : RS)
  | pseudoTetrahedral (value : PseudoRS)
  | alkene (value : DoubleBondStereo)
  | enantiomorphicDoubleBond (value : SequenceDoubleBondDescriptor)
  | axial (value : AxialDescriptor)
  | planar (value : PlanarDescriptor)
  | helical (value : HelicalDescriptor)
  | polyhedral (value : PolyhedralDescriptor)
  | refused (reason : StereoRefusal)
  deriving DecidableEq, Repr

/-- Human-readable label for an outcome. -/
def StereoOutcome.label : StereoOutcome → String
  | tetrahedral RS.R => "R"
  | tetrahedral RS.S => "S"
  | pseudoTetrahedral PseudoRS.r => "r"
  | pseudoTetrahedral PseudoRS.s => "s"
  | alkene DoubleBondStereo.E => "E"
  | alkene DoubleBondStereo.Z => "Z"
  | alkene DoubleBondStereo.unspecified => "unspecified"
  | enantiomorphicDoubleBond SequenceDoubleBondDescriptor.seqCis => "seqCis"
  | enantiomorphicDoubleBond SequenceDoubleBondDescriptor.seqTrans => "seqTrans"
  | axial AxialDescriptor.Ra => "Ra"
  | axial AxialDescriptor.Sa => "Sa"
  | planar PlanarDescriptor.Rp => "Rp"
  | planar PlanarDescriptor.Sp => "Sp"
  | helical HelicalDescriptor.P => "P"
  | helical HelicalDescriptor.M => "M"
  | polyhedral descriptor => descriptor.label
  | refused reason => "refused (" ++ reason.label ++ ")"

/-- Convert terminal senior-ligand geometry into the P-92 descriptor family used when exactly one
endpoint is distinguished by enantiomorphic ligands.  `Z`-like together geometry is `seqCis` and
`E`-like opposite geometry is `seqTrans`; missing geometry never becomes a descriptor. -/
def sequenceDoubleBondOutcomeOfGeometry : DoubleBondStereo → StereoOutcome
  | DoubleBondStereo.Z =>
      StereoOutcome.enantiomorphicDoubleBond SequenceDoubleBondDescriptor.seqCis
  | DoubleBondStereo.E =>
      StereoOutcome.enantiomorphicDoubleBond SequenceDoubleBondDescriptor.seqTrans
  | DoubleBondStereo.unspecified =>
      StereoOutcome.refused StereoRefusal.markerEvidenceUnusable

/-- Whether this outcome carries a descriptor. -/
def StereoOutcome.assigned : StereoOutcome → Bool
  | refused _ => false
  | _ => true

/-- One analysed stereogenic unit. -/
structure StereoAssignment where
  unit : StereoUnit
  outcome : StereoOutcome
  deriving DecidableEq, Repr

/-- Rendered as `atom 1: S` or `bond 2=3: refused (...)`. -/
def StereoAssignment.label (assignment : StereoAssignment) : String :=
  match assignment.unit with
  | StereoUnit.tetrahedral atom =>
      "atom " ++ toString atom ++ ": " ++ assignment.outcome.label
  | StereoUnit.doubleBond left right =>
      "bond " ++ toString left ++ "=" ++ toString right ++ ": " ++ assignment.outcome.label
  | StereoUnit.axis start finish =>
      "axis " ++ toString start ++ "-" ++ toString finish ++ ": " ++ assignment.outcome.label
  | StereoUnit.plane atoms =>
      "plane " ++ String.intercalate "-" (atoms.map toString) ++ ": " ++ assignment.outcome.label
  | StereoUnit.helix path =>
      "helix " ++ String.intercalate "-" (path.map toString) ++ ": " ++ assignment.outcome.label
  | StereoUnit.polyhedron center =>
      "polyhedron " ++ toString center ++ ": " ++ assignment.outcome.label

namespace RawMolecule

/-- Number of inversions in a list of positions, which fixes the sign of the permutation. -/
def inversionCount : List ℕ → ℕ
  | [] => 0
  | x :: xs => (xs.filter fun y => decide (y < x)).length + inversionCount xs

/-- Whether the permutation taking written order to priority order is even. -/
def permutationIsEven (positions : List ℕ) : Bool :=
  inversionCount positions % 2 == 0

/-- Combine the written-order parity with the parity of the written-to-priority permutation.

`@@` (`clockwise`) means that, viewed from the first written neighbour, the remaining three run
clockwise.  Reordering the neighbours by an odd permutation exchanges the two senses, so the
descriptor depends only on the parity of the reordering.

The absolute sense is anchored by two independent references: `N[C@@H](C)C(=O)O` is the OpenSMILES
specification's L-alanine, which is (S); and `[C@H](F)(Cl)Br` is (S) by direct geometric reasoning,
since `@` puts F, Cl, Br anticlockwise viewed from the bracket hydrogen, so with that hydrogen
pointing away Br, Cl, F run anticlockwise. -/
def descriptorOfParity (parity : TetrahedralInputParity) (evenPermutation : Bool) : RS :=
  match parity with
  | TetrahedralInputParity.clockwise => if evenPermutation then RS.R else RS.S
  | TetrahedralInputParity.anticlockwise => if evenPermutation then RS.S else RS.R







def centreElementSupported : Element → Bool
  | Element.B => true
  | Element.C => true
  | Element.N => true
  | Element.O => true
  | Element.P => true
  | Element.S => true
  | Element.Si => true
  | Element.Ge => true
  | Element.As => true
  | Element.Se => true
  | Element.Sn => true
  | Element.Sb => true
  | Element.Te => true
  | Element.Pb => true
  | Element.Bi => true
  | _ => false

/-- Main-group elements whose explicitly configured three-coordinate pyramidal form can use the
P-93.3 lowest-priority phantom atom as the fourth notional tetrahedral position. -/
def centreElementUsesLonePair : Element → Bool
  | Element.N | Element.O | Element.P | Element.As | Element.S | Element.Se
  | Element.Sb | Element.Te | Element.Bi => true
  | _ => false

/-- Ligands of a centre, with a lone pair supplied when a heteroatom centre is three-coordinate.

CIP treats the phantom position of an explicitly configured three-coordinate main-group
stereocentre as atomic number zero, ranked below every physical ligand.  This implementation adopts
the implicit-hydrogen position for its written lone-pair convention: immediately after the atom
the centre was reached from, or first when the centre opens a component.  This is a repository
convention, not a claim that OpenSMILES specifies lone-pair ordering.

The phantom is represented by an index past the end of the atom list, for which `atomZAt` is `0` and
which has no bonds, so it ranks last and expands to nothing without any special casing downstream. -/
def ligandsWithLonePair (mol : RawMolecule) (idx : ℕ) : List ℕ :=
  let written := mol.writtenNeighbors idx
  match mol.atomAt? idx with
  | some spec =>
      if centreElementUsesLonePair spec.element && written.length == 3 then
        -- Recorded introduction history distinguishes a component root from a later ring closure.
        -- Raw graphs without that history retain the legacy incoming-bond fallback.
        let phantom := mol.atomCount
        let hasPreceding := mol.hydrogenHasPreceding idx
        if hasPreceding then
          match written with
          | [] => [phantom]
          | first :: rest => first :: phantom :: rest
        else
          phantom :: written
      else
        written
  | none => written

/-- Whether two branches are established to tie rather than merely left unresolved. -/
def hasTiedBranches (mol : RawMolecule) (fuel center : ℕ) (ligands : List ℕ) : Bool :=
  (List.range ligands.length).any fun i =>
    (List.range ligands.length).any fun j =>
      i < j &&
        (mol.compareBranchesStatus fuel center (ligands.getD i 0) (ligands.getD j 0) ==
          BranchComparisonStatus.tied)

/-- Whether at least one ligand pair exceeded the safe comparison boundary. -/
def hasUnresolvedBranches (mol : RawMolecule) (fuel center : ℕ) (ligands : List ℕ) : Bool :=
  (List.range ligands.length).any fun i =>
    (List.range ligands.length).any fun j =>
      i < j &&
        (mol.compareBranchesStatus fuel center (ligands.getD i 0) (ligands.getD j 0) ==
          BranchComparisonStatus.unresolved)

/-- Compare one already priority-sorted sphere of exact Rule-1a labels. -/
def compareRule1aLabelSphere : List CIPAtomicLabel → List CIPAtomicLabel → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | left :: lefts, right :: rights =>
      match compareCIPAtomicLabel left right with
      | Ordering.eq => compareRule1aLabelSphere lefts rights
      | decision => decision

/-- The first substituent sphere of one branch under exact Rule 1a.

Using canonical nodes here is essential for mancude systems: a multiple-bond duplicate may carry a
fractional atomic-number label obtained from the Kekulé ensemble, not the duplicated atom's plain
atomic number.  Unsupported mancude averaging remains a refusal. -/
def firstCanonicalRule1aSphere? (mol : RawMolecule) (root : CanonicalBranchNode) :
    Option (List CIPAtomicLabel) := do
  let children := mol.canonicalChildren root
  if 3 < children.length then none else
  let labels ← children.mapM mol.canonicalFirstSphereRule1aLabel?
  let before := fun left right => compareCIPAtomicLabel left right != Ordering.lt
  let phantom : CIPAtomicLabel := { numerator := 0, denominator := 1 }
  some (sortDescBy before labels ++ List.replicate (3 - labels.length) phantom)

/-- Compare the root and first substituent sphere of two branches without constructing their full
bounded digraphs.

This is an exact Rule-1a comparison: exact canonical root labels decide first, followed by the three
parent-preserving canonical child labels (including fractional mancude, multiple-bond, and
ring-closure duplicates).  A tie is deliberately left unresolved here, since breaking it would
require a later sphere or sequence rule. -/
def compareBranchesAtFirstPairedSphere? (mol : RawMolecule) (center left right : ℕ) : Option Ordering :=
  let leftRoot := canonicalRoot center left
  let rightRoot := canonicalRoot center right
  match mol.canonicalRule1aLabel? leftRoot, mol.canonicalRule1aLabel? rightRoot with
  | some leftLabel, some rightLabel =>
      match compareCIPAtomicLabel leftLabel rightLabel with
      | Ordering.eq => do
          let leftSphere ← mol.firstCanonicalRule1aSphere? leftRoot
          let rightSphere ← mol.firstCanonicalRule1aSphere? rightRoot
          match compareRule1aLabelSphere leftSphere rightSphere with
          | Ordering.eq => none
          | decision => some decision
      | decision => some decision
  | _, _ => none

/-- Rank a center with one, and only one, bounded constitutional comparison exhausted.

All other ligand pairs must already be strictly ordered, and the exact parent-preserving Rule-1a
root/first-sphere comparison must strictly order the exhausted pair.  Because it does not descend,
this fallback is independent of the recursive comparator's depth and width bounds.  It admits the
two bounded-topology Rule-1a cases without turning broadly unresolved high-symmetry cages into
stereogenic centers. -/
def rankBranchPositionsWithSinglePairedFallback? (mol : RawMolecule) (fuel center : ℕ)
    (ligands : List ℕ) : Option (List ℕ) :=
  if !mol.atomLiesInCycle fuel center then none else
  let pairs := (List.range ligands.length).flatMap fun i =>
    (List.range ligands.length).filterMap fun j => if i < j then some (i, j) else none
  let unresolved := pairs.filter fun pair =>
    mol.compareBranchesStatus fuel center (ligands.getD pair.1 0) (ligands.getD pair.2 0) ==
      BranchComparisonStatus.unresolved
  if unresolved.length != 1 || mol.hasTiedBranches fuel center ligands then none else
    let compareAt := fun left right =>
      let leftAtom := ligands.getD left 0
      let rightAtom := ligands.getD right 0
      match mol.compareBranchesStatus fuel center leftAtom rightAtom with
      | BranchComparisonStatus.lower => some Ordering.lt
      | BranchComparisonStatus.higher => some Ordering.gt
      | BranchComparisonStatus.tied => some Ordering.eq
      | BranchComparisonStatus.unresolved =>
          mol.compareBranchesAtFirstPairedSphere? center leftAtom rightAtom
    let before := fun left right => compareAt left right != some Ordering.lt
    let sorted := sortDescBy before (List.range ligands.length)
    let strict := (List.range (sorted.length - 1)).all fun index =>
      match sorted[index]?, sorted[index + 1]? with
      | some left, some right => compareAt left right == some Ordering.gt
      | _, _ => false
    if strict then some sorted else none

/-- Assign `R/S` at one parsed tetrahedral centre, or say why not.

`mol` is expected to have explicit hydrogens already; see `withExplicitHydrogens`. -/
def tetrahedralOutcome (mol : RawMolecule) (fuel idx : ℕ) : StereoOutcome :=
  match mol.atomAt? idx with
  | none => StereoOutcome.refused StereoRefusal.notSpecified
  | some spec =>
      match spec.tetrahedral? with
      | none => StereoOutcome.refused StereoRefusal.notSpecified
      | some parity =>
        -- Supported centers either expose four ligand positions directly or are a three-coordinate
        -- N/P/S center whose fourth position is the lone pair materialized by
        -- `ligandsWithLonePair`.  Root P/S oxido multiple-bond semantics are handled by the shared
        -- hierarchical comparator.
        if !centreElementSupported spec.element then
          StereoOutcome.refused StereoRefusal.unsupportedCentreElement
        else
          let ligands := mol.ligandsWithLonePair idx
          if ligands.length != 4 then
            StereoOutcome.refused (StereoRefusal.wrongLigandCount ligands.length)
          else
            match mol.rankBranchPositions? fuel idx ligands with
            | some positions =>
                StereoOutcome.tetrahedral (descriptorOfParity parity (permutationIsEven positions))
            | none =>
                match mol.rankBranchPositionsWithSinglePairedFallback? fuel idx ligands with
                | some positions =>
                    StereoOutcome.tetrahedral
                      (descriptorOfParity parity (permutationIsEven positions))
                | none =>
                    if mol.hasTiedBranches fuel idx ligands then
                      StereoOutcome.refused StereoRefusal.notStereogenic
                    else
                    match mol.rankBranchPositionsAuthoritative? idx ligands with
                    | some positions => StereoOutcome.tetrahedral
                        (descriptorOfParity parity (permutationIsEven positions))
                    | none =>
                        if mol.hasAuthoritativelyUnresolvedBranches idx ligands then
                          StereoOutcome.refused StereoRefusal.rankingUnresolved
                        else if mol.hasAuthoritativelyTiedBranches idx ligands then
                          StereoOutcome.refused StereoRefusal.notStereogenic
                        else
                          StereoOutcome.refused StereoRefusal.rankingUnresolved

end RawMolecule

/-- Fuel sufficient to walk any branch of a molecule of this size. -/
def analysisFuel (mol : RawMolecule) : ℕ :=
  2 * mol.atomCount + 2

namespace RawMolecule

/-- Width-unbounded CIP-senior substituent at one end of a double bond.

This is the authoritative counterpart of `RawMolecule.seniorAlkeneSubstituent?`.  The local and
terminal cases are identical; the only recursive branch uses the molecular-depth comparator and
therefore cannot turn a frontier-width refusal into a tie. -/
def seniorAlkeneSubstituentAuthoritative?
    (mol : RawMolecule) (carbon partner : ℕ) : Option ℕ :=
  match mol.alkeneSubstituents carbon partner with
  | [] => none
  | [s] =>
      match mol.firstSphereLabel? s with
      | some label =>
          if firstSphereUnknown label then none
          else if mol.doubleBondEndpointHasLonePairSide carbon partner then some s
          else if firstSphereOutranks label implicitHydrogenLabel then some s
          else none
      | none => none
  | [s, t] =>
      match mol.firstSphereLabel? s, mol.firstSphereLabel? t with
      | some ls, some lt =>
          if firstSphereUnknown ls || firstSphereUnknown lt then none
          else
            let sr := RawMolecule.canonicalRoot carbon s
            let tr := RawMolecule.canonicalRoot carbon t
            if mol.canonicalTerminal sr && mol.canonicalTerminal tr then
              match mol.compareCanonicalNodeThrough? CanonicalRuleStage.rule2 sr tr with
              | some Ordering.gt => some s
              | some Ordering.lt => some t
              | _ => none
            else
              match mol.compareBranchesAuthoritative? carbon s t with
              | some Ordering.gt => some s
              | some Ordering.lt => some t
              | some Ordering.eq =>
                  if firstSphereOutranks ls lt then some s
                  else if firstSphereOutranks lt ls then some t
                  else none
              | none => none
      | _, _ => none
  | _ :: _ :: _ :: _ => none

end RawMolecule

namespace ChemistryNormalizationResult

/-- Position of an atom in a breadth-first branch walk. -/
def branchAtomPosition : List ℕ → ℕ → ℕ
  | [], _ => 0
  | atom :: rest, target => if atom == target then 0 else branchAtomPosition rest target + 1

/-- The substituent through which a branch reaches a double-bond endpoint. -/
def branchEntrySubstituent? (mol : RawMolecule) (center endpoint partner : ℕ)
    (reachable : List ℕ) : Option ℕ :=
  let substituents := mol.alkeneSubstituents endpoint partner
  if substituents.contains center then some center
  else
    match substituents.filter fun atom => reachable.contains atom with
    | [] => none
    | first :: rest =>
        some (rest.foldl (fun best atom =>
          if branchAtomPosition reachable atom < branchAtomPosition reachable best then atom else best)
          first)

/-- Rule-3 sequence geometry as viewed from one incoming ligand branch.

Absolute `E/Z` is not by itself `seqcis/seqtrans`: approaching the unit through its junior
substituent reverses the sequence sense. -/
def branchRule3Geometry? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (center : ℕ) (reachable : List ℕ) (left right : ℕ) : Option OfficialRule3Geometry :=
  let leftPosition := branchAtomPosition reachable left
  let rightPosition := branchAtomPosition reachable right
  let near := if leftPosition ≤ rightPosition then left else right
  let far := if leftPosition ≤ rightPosition then right else left
  let farReferenceSide? :=
    match result.seniorSideAt? far near with
    | some side => some side
    | none =>
        ((mol.alkeneSubstituents far near).filterMap fun substituent =>
          result.stereobonds.substituentSideMarker? far substituent).head?
  match branchEntrySubstituent? mol center near far reachable, farReferenceSide? with
  | some entry, some farSeniorSide =>
      let entrySide? :=
        match result.stereobonds.substituentSideMarker? near entry with
        | some side => some side
        | none =>
            match (mol.alkeneSubstituents near far).filter fun atom => atom != entry with
            | [other] =>
                (result.stereobonds.substituentSideMarker? near other).map
                  DirectionalBondMarker.flip
            | _ => none
      match entrySide? with
      | some entrySide =>
          if entrySide == farSeniorSide then some OfficialRule3Geometry.seqcis
          else some OfficialRule3Geometry.seqtrans
      | none => none
  | _, _ => none

/-- One physical Rule-3 geometrical unit as viewed from a ligand occurrence. -/
structure Rule3GeometryOccurrence where
  left : ℕ
  right : ℕ
  near : ℕ
  distance : ℕ
  geometry : OfficialRule3Geometry
  deriving DecidableEq, Repr

def Rule3GeometryOccurrence.sameUnit
    (left right : Rule3GeometryOccurrence) : Bool :=
  left.left == right.left && left.right == right.right

def Rule3GeometryOccurrence.sameEntryEndpoint
    (left right : Rule3GeometryOccurrence) : Bool :=
  left.sameUnit right && left.near == right.near

/-- Perceived geometrical units on a ligand branch in breadth-first order, retaining identity. -/
def rule3GeometryOccurrencesOnBranch (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (center ligand : ℕ) : List Rule3GeometryOccurrence :=
  let reachable := mol.reachableAvoiding (mol.atomCount + 1) center [ligand] [ligand]
  let units := result.stereobonds.doubleBondAssignments.filterMap fun assignment =>
    let left := assignment.1
    let right := assignment.2.1
    let leftPosition := branchAtomPosition reachable left
    let rightPosition := branchAtomPosition reachable right
    let near := if leftPosition ≤ rightPosition then left else right
    let far := if leftPosition ≤ rightPosition then right else left
    let entry? := branchEntrySubstituent? mol center near far reachable
    let sharedWithAnotherLigand := (mol.ligandsWithLonePair center).any fun otherLigand =>
      if otherLigand == ligand || mol.atomCount ≤ otherLigand then false else
        let otherReachable := mol.reachableAvoiding (mol.atomCount + 1) center
          [otherLigand] [otherLigand]
        otherReachable.contains left && otherReachable.contains right
    let sharedThroughSameEntry := (mol.ligandsWithLonePair center).any fun otherLigand =>
      if otherLigand == ligand || mol.atomCount ≤ otherLigand || entry?.isNone then false else
        let otherReachable := mol.reachableAvoiding (mol.atomCount + 1) center
          [otherLigand] [otherLigand]
        let otherLeftPosition := branchAtomPosition otherReachable left
        let otherRightPosition := branchAtomPosition otherReachable right
        let otherNear := if otherLeftPosition ≤ otherRightPosition then left else right
        let otherFar := if otherLeftPosition ≤ otherRightPosition then right else left
        otherReachable.contains left && otherReachable.contains right && otherNear == near &&
          branchEntrySubstituent? mol center otherNear otherFar otherReachable == entry?
    let cyclicRoot := mol.atomLiesInCycle (2 * mol.atomCount + 2) center
    if reachable.contains left && reachable.contains right &&
        !sharedThroughSameEntry && (!sharedWithAnotherLigand || cyclicRoot) then
      let distance := min leftPosition rightPosition
      -- At a tetrahedral root Rule 3 is the branch-relative `seqcis/seqtrans` relation: entering
      -- the geometrical unit through its junior side reverses the absolute E/Z sense.  When this
      -- same sequence is consulted merely to choose an alkene's senior substituent, retain the
      -- absolute geometry; treating the alkene endpoint itself as an incoming tetrahedral path
      -- circularly reverses coupled E/Z assignments.
      if (mol.atomAt? center).any fun spec => spec.tetrahedral?.isSome then
        if cyclicRoot then
          match result.branchRule3Geometry? mol center reachable left right with
          | some geometry =>
              some { left := min left right, right := max left right, near, distance, geometry }
          | none => none
        else
          match Option.first (result.perceivedDoubleBondStereo? left right)
              (result.stereobonds.perceivedDoubleBondStereo? left right) with
          | some DoubleBondStereo.Z =>
              some { left := min left right, right := max left right, near, distance,
                     geometry := OfficialRule3Geometry.seqcis }
          | some DoubleBondStereo.E =>
              some { left := min left right, right := max left right, near, distance,
                     geometry := OfficialRule3Geometry.seqtrans }
          | _ => none
      else
        match Option.first (result.perceivedDoubleBondStereo? left right)
            (result.stereobonds.perceivedDoubleBondStereo? left right) with
        | some DoubleBondStereo.Z =>
            some { left := min left right, right := max left right, near, distance,
                   geometry := OfficialRule3Geometry.seqcis }
        | some DoubleBondStereo.E =>
            some { left := min left right, right := max left right, near, distance,
                   geometry := OfficialRule3Geometry.seqtrans }
        | _ => none
    else
      none
  let ordered := sortDescBy (fun left right => left.distance ≤ right.distance) units
  if (mol.atomAt? center).any fun spec => spec.tetrahedral?.isSome then
    if !mol.atomLiesInCycle (2 * mol.atomCount + 2) center && 1 < ordered.length then
      -- A sequence of coupled geometrical units transports the branch-entry frame through the
      -- intervening units.  Relative to the absolute E/Z markers this reverses the sequence sense;
      -- a single isolated unit retains its direct `seqcis/seqtrans` mapping.
      ordered.map fun occurrence =>
        { occurrence with geometry :=
            match occurrence.geometry with
            | OfficialRule3Geometry.seqcis => OfficialRule3Geometry.seqtrans
            | OfficialRule3Geometry.seqtrans => OfficialRule3Geometry.seqcis
            | OfficialRule3Geometry.nonstereogenic =>
                OfficialRule3Geometry.nonstereogenic }
    else ordered
  else ordered

/-- Rule-3 geometry values on one branch, without their physical-unit identities. -/
def rule3GeometrySequenceOnBranch (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (center ligand : ℕ) : List OfficialRule3Geometry :=
  (result.rule3GeometryOccurrencesOnBranch mol center ligand).map
    Rule3GeometryOccurrence.geometry

/-- Lexicographic Rule-3 sequence comparison.  Missing evidence does not create a priority. -/
def compareRule3GeometrySequences :
    List OfficialRule3Geometry → List OfficialRule3Geometry → Ordering
  | [], [] => Ordering.eq
  | left :: lefts, right :: rights =>
      match OfficialRule3Geometry.compare left right with
      | Ordering.eq => compareRule3GeometrySequences lefts rights
      | decision => decision
  | left :: lefts, [] =>
      match OfficialRule3Geometry.compare left OfficialRule3Geometry.nonstereogenic with
      | Ordering.eq => compareRule3GeometrySequences lefts []
      | decision => decision
  | [], right :: rights =>
      match OfficialRule3Geometry.compare OfficialRule3Geometry.nonstereogenic right with
      | Ordering.eq => compareRule3GeometrySequences [] rights
      | decision => decision

/-- Compare Rule-3 occurrences after cancelling matching views of the same physical unit. -/
def compareRule3GeometryOccurrences
    : List Rule3GeometryOccurrence → List Rule3GeometryOccurrence → Ordering
  | [], [] => Ordering.eq
  | left :: lefts, right :: rights =>
      if left.sameUnit right then
        compareRule3GeometryOccurrences lefts rights
      else
        match OfficialRule3Geometry.compare left.geometry right.geometry with
        | Ordering.eq => compareRule3GeometryOccurrences lefts rights
        | decision => decision
  | left :: lefts, [] =>
      match OfficialRule3Geometry.compare left.geometry OfficialRule3Geometry.nonstereogenic with
      | Ordering.eq => compareRule3GeometryOccurrences lefts []
      | decision => decision
  | [], right :: rights =>
      match OfficialRule3Geometry.compare OfficialRule3Geometry.nonstereogenic right.geometry with
      | Ordering.eq => compareRule3GeometryOccurrences [] rights
      | decision => decision

/-- Whether a shared geometrical unit has an independently ranked reference at its far endpoint.

When it does, two ring arms may legitimately receive different `seqcis/seqtrans` labels from that
unit (for example an exocyclic `C=C(Br)H`).  When the far substituents tie, using those two labels
would rank the paths that are themselves still needed to establish the geometrical reference. -/
def sharedRule3UnitHasIndependentFarReference (mol : RawMolecule) (_fuel : ℕ)
    (left right : Rule3GeometryOccurrence) : Bool :=
  if !left.sameEntryEndpoint right then false else
  let far := if left.near == left.left then left.right else left.left
  (mol.seniorAlkeneSubstituentAuthoritative? far left.near).isSome

/-- Pairwise shared-unit cancellation with independently referenced geometries retained. -/
def compareRule3GeometryOccurrencesAtCenter (mol : RawMolecule) (fuel : ℕ) :
    List Rule3GeometryOccurrence → List Rule3GeometryOccurrence → Ordering
  | [], [] => Ordering.eq
  | left :: lefts, right :: rights =>
      if left.sameUnit right &&
          !sharedRule3UnitHasIndependentFarReference mol fuel left right then
        compareRule3GeometryOccurrencesAtCenter mol fuel lefts rights
      else
        match OfficialRule3Geometry.compare left.geometry right.geometry with
        | Ordering.eq => compareRule3GeometryOccurrencesAtCenter mol fuel lefts rights
        | decision => decision
  | left :: lefts, [] =>
      match OfficialRule3Geometry.compare left.geometry OfficialRule3Geometry.nonstereogenic with
      | Ordering.eq => compareRule3GeometryOccurrencesAtCenter mol fuel lefts []
      | decision => decision
  | [], right :: rights =>
      match OfficialRule3Geometry.compare OfficialRule3Geometry.nonstereogenic right.geometry with
      | Ordering.eq => compareRule3GeometryOccurrencesAtCenter mol fuel [] rights
      | decision => decision

/-- An occurrence is circular at this center when another ligand reaches the same physical
geometrical unit and that unit has no independently ranked far reference.  This predicate is
unary in the ligand: it consults the whole center once instead of changing meaning with the
opponent selected for a particular comparison. -/
def rule3OccurrenceCircularAtCenter (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel center ligand : ℕ) (occurrence : Rule3GeometryOccurrence) : Bool :=
  (mol.ligandsWithLonePair center).any fun otherLigand =>
    if otherLigand == ligand || mol.atomCount ≤ otherLigand then false else
      (result.rule3GeometryOccurrencesOnBranch mol center otherLigand).any fun otherOccurrence =>
        occurrence.sameUnit otherOccurrence &&
          !sharedRule3UnitHasIndependentFarReference mol fuel occurrence otherOccurrence

/-- Whether Rule 3 is describing a coupled two-unit topology around one four-way constitutional
tie.  In this shape the two physical units partition the four ligand occurrences before Rule 6
sequences their topology, so cancelling each shared unit independently would make the comparator
non-transitive. -/
def hasCoupledRule3PerfectMatching (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (_fuel center : ℕ) : Bool :=
  let ligands := mol.ligandsWithLonePair center
  if ligands.length != 4 then false else
  let positions := List.range ligands.length
  let constitutionallyTied := positions.all fun leftIndex =>
    positions.all fun rightIndex =>
      if leftIndex < rightIndex then
        mol.compareBranchesAuthoritativeStatus center
          (ligands.getD leftIndex 0) (ligands.getD rightIndex 0) ==
            RawMolecule.BranchComparisonStatus.tied
      else true
  let occurrences := ligands.map fun ligand =>
    result.rule3GeometryOccurrencesOnBranch mol center ligand
  let singletonOccurrences := occurrences.all fun branch => branch.length == 1
  let flattened := occurrences.flatten
  let units := (flattened.map fun occurrence =>
    (occurrence.left, occurrence.right)).eraseDups
  let eachUnitOccursTwice := units.all fun unit =>
    (flattened.countP fun occurrence =>
      occurrence.left == unit.1 && occurrence.right == unit.2) == 2
  constitutionallyTied && singletonOccurrences && units.length == 2 && eachUnitOccursTwice

/-- Canonical Rule-3 occurrences of one ligand.

The special coupled perfect-matching topology retains its two physical units, as before.  In every
other topology, a circular shared unit without an independent far reference is removed from every
ligand that reaches it.  Pairwise same-unit cancellation cannot define a preorder because the same
ligand then acquires different effective observations against different opponents. -/
def canonicalRule3OccurrencesOnBranch (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel center ligand : ℕ) : List Rule3GeometryOccurrence :=
  let occurrences := result.rule3GeometryOccurrencesOnBranch mol center ligand
  if result.hasCoupledRule3PerfectMatching mol fuel center then occurrences
  else occurrences.filter fun occurrence =>
    !rule3OccurrenceCircularAtCenter result mol fuel center ligand occurrence

/-- Remove semantically inert trailing nonstereogenic observations. -/
def trimTrailingRule3Zeros (priorities : List ℕ) : List ℕ :=
  (priorities.reverse.dropWhile fun priority => priority == 0).reverse

/-- Opponent-independent Rule-3 key for one ligand. -/
def rule3CanonicalSignature (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel center ligand : ℕ) : List ℕ :=
  trimTrailingRule3Zeros
    ((canonicalRule3OccurrencesOnBranch result mol fuel center ligand).map fun occurrence =>
      occurrence.geometry.priority)

/-- Lawful Rule-3 comparison obtained by pulling back list lexicographic order along the unary
canonical signature. -/
def compareRule3CanonicalSignatures (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel center left right : ℕ) : Ordering :=
  compare (rule3CanonicalSignature result mol fuel center left)
    (rule3CanonicalSignature result mol fuel center right)

/-- Center-aware Rule-3 comparison.

A lone shared unit is a circular comparison of its own two entry substituents and cancels.  The
four-ligand/two-unit perfect-matching shape retains the geometry values consistently for every pair
because those values form the partition consumed by Rule 6. -/
def compareRule3GeometryAtCenter (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel center left right : ℕ) : Ordering :=
  compareRule3CanonicalSignatures result mol fuel center left right

/-- The former flat Rule-3 gate, preserved explicitly as diagnostic history.

Its `near`, `distance` and entry choices are read from the breadth-first discovery index, which is
bond-list order.  No live decision path calls it; historical counterexample modules cite it under
this explicit name. -/
def compareBranchesThroughRule3Legacy? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel center left right : ℕ) : Option Ordering :=
  match mol.compareBranchesStatus fuel center left right with
  | .lower => some Ordering.lt
  | .higher => some Ordering.gt
  | .unresolved =>
      match mol.compareBranchesAuthoritativeStatus center left right with
      | .lower => some Ordering.lt
      | .higher => some Ordering.gt
      | .unresolved => none
      | .tied =>
          some (result.compareRule3GeometryAtCenter mol fuel center left right)
  | .tied =>
      -- Two entry paths to the same physical geometrical unit cannot use their different entry
      -- frames to rank each other.  Cancel matching identities pairwise before Rule 3 compares
      -- the remaining occurrence sequences.
      some (result.compareRule3GeometryAtCenter mol fuel center left right)

/-! ### Source-bound Rule-3 hierarchy compilation

The flat occurrence layer reads `near`, `distance` and the sequence order from the breadth-first
discovery index, which is a bond-list artefact inside one layer.  The definitions below replace
every live decision path: each observation is attached to a real `CanonicalBranchNode`, its
endpoints are the actual `parent`/`atom` of the incoming double edge, and its entry is the
predecessor recorded in the node history.  No list index is read.  The flat signatures above
remain available as diagnostics.

Two provenance distinctions are load bearing here:

* a canonical branch tree can address one physical double-bond unit at several occurrences (distinct
  simple paths through a ring).  Every addressed occurrence is preserved in the compiled hierarchy,
  but physical multiplicity — the coupled perfect-matching count and the non-cyclic transport flip —
  is counted per ligand by unordered unit key, never by occurrence count;
* a missing Rule-3 geometry is not by itself proof that the unit is inapplicable.  A double bond
  that is *proved* structurally unable to carry `E/Z` (for example a carbonyl `C=O`, whose oxygen
  has no second substituent at all) is a determinate absence, while an applicable unit whose
  geometry is unread or unspecified remains unknown evidence and refuses.

The structural test below deliberately uses only actual substituent absence and indistinguishable
hydrogens.  It does not call `doubleBondStereogenicity`, whose `notStereogenic` also covers a
constitutional tie between heavier substituents; such a tie may still be broken by later sequence
rules and must remain unknown. -/

/-- One physical Rule-3 unit as read from a real canonical node. -/
structure Rule3SourceUnit where
  near : ℕ
  far : ℕ
  entry? : Option ℕ
  deriving DecidableEq, Repr

namespace Rule3SourceUnit

/-- Unordered physical-unit identity. -/
def key (unit : Rule3SourceUnit) : ℕ × ℕ :=
  (min unit.near unit.far, max unit.near unit.far)

def sameUnit (left right : Rule3SourceUnit) : Bool :=
  left.key == right.key

def sameEntryEndpoint (left right : Rule3SourceUnit) : Bool :=
  left.sameUnit right && left.near == right.near && left.entry? == right.entry?

/-- Full addressed identity of one observation: ligand, incoming endpoint, far endpoint and the
actual history predecessor.

The entry is load bearing.  Same-entry sharing is decided by the entry as well as by the endpoints,
so an exclusion key without it would suppress a different incoming occurrence of the same edge. -/
def addressedKey (unit : Rule3SourceUnit) (ligand : ℕ) : ℕ × ℕ × ℕ × Option ℕ :=
  (ligand, unit.near, unit.far, unit.entry?)

end Rule3SourceUnit

/-- One representative per physical unit from a ligand's addressed canonical occurrences.

`foldr` keeps the last occurrence of each unordered unit key; the representative identity does not
matter, only the physical multiplicity and the unit key.  Addressed occurrences are preserved
separately in the compiled hierarchy. -/
def distinctRule3Units (units : List Rule3SourceUnit) : List Rule3SourceUnit :=
  units.foldr
    (fun unit kept =>
      if kept.any (fun other => other.sameUnit unit) then kept else unit :: kept) []

/-- `seqcis`/`seqtrans` transport through an intervening unit. -/
def flipRule3Geometry : OfficialRule3Geometry → OfficialRule3Geometry
  | .seqcis => .seqtrans
  | .seqtrans => .seqcis
  | .nonstereogenic => .nonstereogenic

/-- Whole-centre physical admission policy for Rule 3.

Computed once per centre and reused for every pair of ligands.  `excluded` holds the full addressed
occurrence identity `(ligand, near, far, entry?)` of every physically excluded observation; `flipped`
holds the ligands whose absolute observations carry the existing sequence-transport flip. -/
structure Rule3CenterPolicy where
  cyclic : Bool
  coupled : Bool
  excluded : List (ℕ × ℕ × ℕ × Option ℕ)
  flipped : List ℕ
  deriving DecidableEq, Repr

/-- Branch children for Rule-3 observation, pruning any re-entry to the stereogenic centre. -/
def rule3BranchChildren (mol : RawMolecule) (center : ℕ)
    (node : RawMolecule.CanonicalBranchNode) : List RawMolecule.CanonicalBranchNode :=
  if node.atom == center then [] else mol.canonicalChildren node

/-- Preorder source nodes of one canonical branch tree, to the supplied depth fuel.  Duplicate,
ring and phantom nodes are leaves by construction. -/
def rule3SourceNodes (mol : RawMolecule) (center : ℕ) :
    ℕ → List RawMolecule.CanonicalBranchNode → List RawMolecule.CanonicalBranchNode
  | 0, nodes => nodes
  | fuel + 1, nodes =>
      nodes ++ rule3SourceNodes mol center fuel
        (nodes.flatMap fun node => rule3BranchChildren mol center node)

/-- The source-bound unit of one canonical node.

Only real nodes carry a physical observation.  A node attached to the stereogenic centre is the
incoming ligand edge or a ring closure and is not a Rule-3 source.  `near` is the actual parent,
`far` the node atom, and `entry?` the predecessor recorded in `history`; no breadth-first index
is consulted. -/
def rule3SourceUnitOfNode? (mol : RawMolecule) (center : ℕ)
    (node : RawMolecule.CanonicalBranchNode) : Option Rule3SourceUnit :=
  if node.provenance == RawMolecule.CanonicalNodeProvenance.realAtom &&
      node.atom != center && node.parent != center &&
      mol.bondOrder node.parent node.atom == 2 then
    some { near := node.parent, far := node.atom, entry? := (node.history.drop 2).head? }
  else none

/-- Perceived absolute geometry of one physical unit, exactly as the flat layer reads it. -/
def rule3AbsoluteGeometry? (result : ChemistryNormalizationResult) (_mol : RawMolecule)
    (near far : ℕ) : Option OfficialRule3Geometry :=
  match Option.first (result.perceivedDoubleBondStereo? near far)
      (result.stereobonds.perceivedDoubleBondStereo? near far) with
  | some DoubleBondStereo.Z => some OfficialRule3Geometry.seqcis
  | some DoubleBondStereo.E => some OfficialRule3Geometry.seqtrans
  | _ => none

/-- Entry-relative geometry, using the recorded history predecessor instead of a proposed near
endpoint.  The far reference is the ranked senior substituent only: when `seniorSideAt?` cannot
determine it, the observation refuses instead of taking an arbitrary marked substituent. -/
def rule3EntryGeometry? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (near far entry : ℕ) : Option OfficialRule3Geometry :=
  -- `seniorSideAt?` also flips a uniquely determined partner marker; nothing else is justified.
  let farReferenceSide? := result.seniorSideAt? far near
  let entrySide? :=
    match result.stereobonds.substituentSideMarker? near entry with
    | some side => some side
    | none =>
        match (mol.alkeneSubstituents near far).filter fun atom => atom != entry with
        | [other] =>
            (result.stereobonds.substituentSideMarker? near other).map
              DirectionalBondMarker.flip
        | _ => none
  match farReferenceSide?, entrySide? with
  | some farSide, some entrySide =>
      if entrySide == farSide then some OfficialRule3Geometry.seqcis
      else some OfficialRule3Geometry.seqtrans
  | _, _ => none

/-- Whether the centre is a tetrahedral root, matching the flat applicability test. -/
def rule3CenterTetrahedral (mol : RawMolecule) (center : ℕ) : Bool :=
  (mol.atomAt? center).any fun spec => spec.tetrahedral?.isSome

/-- Source-bound geometry under the centre's applicability policy.

Absolute `E/Z` is retained unless the centre is tetrahedral and cyclic, where Rule 3 is the
branch-relative `seqcis/seqtrans` relation.  A missing entry frame in that mode is *unknown*
evidence, not a tie.  The non-cyclic transport convention is applied by the caller through
`Rule3CenterPolicy.flipped`. -/
def rule3CenterGeometry? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (_center : ℕ) (tetrahedral cyclic : Bool) (unit : Rule3SourceUnit) :
    Option OfficialRule3Geometry :=
  if tetrahedral && cyclic then
    match unit.entry? with
    | some entry => rule3EntryGeometry? result mol unit.near unit.far entry
    | none => none
  else rule3AbsoluteGeometry? result mol unit.near unit.far

/-- Number of substituent positions at one end of a double bond, excluding the double-bond partner.

Written neighbours are parsed atoms; `RawMolecule.hydrogenCountAt` adds the hydrogens that the
OpenSMILES valence model leaves implicit.  The two views compose without double counting: after
`withExplicitHydrogens` the hydrogens are real written neighbours and `hydrogenCountAt` returns zero
for the materialized heavy atom, while on raw parser output the written list contains no implicit
hydrogen. -/
def rule3EndpointSubstituentCount (mol : RawMolecule) (atom partner : ℕ) : ℕ :=
  ((mol.writtenNeighbors atom).filter fun other => other != partner).length +
    RawMolecule.hydrogenCountAt mol atom

/-- Whether one double-bond endpoint supplies a lone-pair side in place of a second atom
substituent.

This extends the repo's explicit-substituent test to the raw-parser case where the nitrogen's only
substituent is an implicit hydrogen: such an imine still carries the lone pair.  The extension can
only classify a unit as potentially applicable, never as absent. -/
def rule3EndpointHasLonePairSide (mol : RawMolecule) (atom partner : ℕ) : Bool :=
  let implicitHydrogenLonePair :=
    match mol.atomAt? atom with
    | some spec =>
        spec.element == Element.N && rule3EndpointSubstituentCount mol atom partner == 1
    | none => false
  mol.doubleBondEndpointHasLonePairSide atom partner || implicitHydrogenLonePair

/-- Whether one endpoint has exactly two substituent positions and both are hydrogens with the same
first-sphere label.

Hydrogen is monovalent and has no branch, so no later sequence rule can distinguish two hydrogens
with equal atomic number and mass.  This is the terminal `=CH₂` case.  A constitutional tie between
two heavier substituents is deliberately *not* treated as absence: Rules 4--6 may distinguish it. -/
def rule3EndpointHasTwoEqualHydrogens (mol : RawMolecule) (atom partner : ℕ) : Bool :=
  let written := (mol.writtenNeighbors atom).filter fun other => other != partner
  let hydrogenLabels := written.filterMap fun other =>
    match mol.atomAt? other with
    | some spec => if spec.element == Element.H then mol.firstSphereLabel? other else none
    | none => none
  let heavyCount := written.length - hydrogenLabels.length
  let implicit := RawMolecule.hydrogenCountAt mol atom
  let labels := hydrogenLabels ++ List.replicate implicit RawMolecule.implicitHydrogenLabel
  if heavyCount == 0 && labels.length == 2 then
    match labels with
    | [left, right] => left == right && !(RawMolecule.firstSphereUnknown left)
    | _ => false
  else false

/-- Whether the endpoint carries a second multiple bond besides the one to `partner`.

An adjacent multiple bond requires a separate assessment of the full cumulene or other
multiple-bond system, including chain parity; a per-edge frame alone is insufficient.  The narrow absence test must not classify it as
nonstereogenic, so a missing observation stays unknown. -/
def rule3EndpointHasAdjacentMultipleBond (mol : RawMolecule) (atom partner : ℕ) : Bool :=
  (mol.writtenNeighbors atom).any fun other =>
    other != partner && decide (2 ≤ mol.bondOrder atom other)

/-- Whether one endpoint is structurally unable to carry a second, distinguishable reference.

Fewer than two substituent positions is absence unless a lone-pair nitrogen supplies the second
position.  Exactly two positions is absence only when both are indistinguishable hydrogens.  Every
other shape is left potentially applicable, so a constitutional tie between heavier substituents is
never converted into a determinate absence. -/
def rule3EndpointStructurallyInapplicable (mol : RawMolecule) (atom partner : ℕ) : Bool :=
  if rule3EndpointHasAdjacentMultipleBond mol atom partner then
    -- A cumulene-adjacent unit can carry axial stereo; never prove it absent here.
    false
  else
    let count := rule3EndpointSubstituentCount mol atom partner
    if count < 2 then
      !(count == 1 && rule3EndpointHasLonePairSide mol atom partner)
    else
      rule3EndpointHasTwoEqualHydrogens mol atom partner

/-- Narrow structural inapplicability of one source unit.

Either endpoint lacking a second distinguishable reference makes `E/Z` impossible.  This is not the
full `doubleBondStereogenicity` classification: only proven structural absence and the two-equal-
hydrogen case are used, so an `unresolved` comparison or a constitutional tie between heavier
substituents remains unknown evidence. -/
def rule3UnitStructurallyInapplicable (mol : RawMolecule) (unit : Rule3SourceUnit) : Bool :=
  rule3EndpointStructurallyInapplicable mol unit.near unit.far ||
    rule3EndpointStructurallyInapplicable mol unit.far unit.near

/-- Addressed canonical occurrences of physical units with perceived geometry on one ligand branch.

The result is an occurrence enumeration, not a physical-unit enumeration: the same physical unit can
appear along more than one canonical occurrence path.  `rule3CenterPolicy` deduplicates by unordered
unit key before using the list for physical multiplicity, while the compiled hierarchy keeps every
addressed occurrence. -/
def rule3SourceEvidenceOnBranch (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (center : ℕ) (tetrahedral cyclic : Bool) (ligand : ℕ) : List Rule3SourceUnit :=
  (rule3SourceNodes mol center (2 * mol.atomCount + 2)
      [RawMolecule.canonicalRoot center ligand]).flatMap fun node =>
    match rule3SourceUnitOfNode? mol center node with
    | none => []
    | some unit =>
        if rule3UnitStructurallyInapplicable mol unit then []
        else
          match rule3CenterGeometry? result mol center tetrahedral cyclic unit with
          | some _ => [unit]
          | none => []

/-- Whether a unit has an independently ranked far reference, computed once. -/
def rule3UnitHasIndependentFarReference (mol : RawMolecule) (unit : Rule3SourceUnit) : Bool :=
  (mol.seniorAlkeneSubstituentAuthoritative? unit.far unit.near).isSome

/-- Whole-centre physical admission policy.

All addressed sources are collected once per centre, the physical exclusion tests are applied once
(shared same-entry unit, non-cyclic shared unit, circular unit without an independent far
reference), and only then is the observation reader rebuilt for the sibling sort.

Physical multiplicity is counted over unordered unit keys per ligand.  A canonical branch tree can
address the same physical unit at several occurrences (distinct simple paths through a ring); raw
occurrence counts would otherwise invent extra units, suppress the coupled perfect-matching shape,
and alter the physical admission decisions.  Multiplicity does not change the selected reference
frame, so generated policies do not request a geometry flip. -/
def rule3CenterPolicy (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (center : ℕ) : Rule3CenterPolicy :=
  let cyclic := mol.atomLiesInCycle (2 * mol.atomCount + 2) center
  let tetrahedral := rule3CenterTetrahedral mol center
  let ligands := mol.ligandsWithLonePair center
  let evidence : List (ℕ × Rule3SourceUnit) := ligands.flatMap fun ligand =>
    (rule3SourceEvidenceOnBranch result mol center tetrahedral cyclic ligand).map fun unit =>
      (ligand, unit)
  let unitsOfLigand : ℕ → List Rule3SourceUnit := fun ligand =>
    distinctRule3Units (evidence.filterMap fun entry =>
      if entry.1 == ligand then some entry.2 else none)
  let coupled :=
    if ligands.length != 4 then false
    else
      let positions := List.range ligands.length
      let tied := positions.all fun leftIndex =>
        positions.all fun rightIndex =>
          if leftIndex < rightIndex then
            mol.compareBranchesAuthoritativeStatus center
              (ligands.getD leftIndex 0) (ligands.getD rightIndex 0) ==
                RawMolecule.BranchComparisonStatus.tied
          else true
      let perLigand := ligands.map unitsOfLigand
      let singleton := perLigand.all fun units => units.length == 1
      let flattened := perLigand.flatten
      let units := (flattened.map Rule3SourceUnit.key).eraseDups
      let eachUnitOccursTwice := units.all fun unit =>
        (flattened.countP fun candidate => candidate.key == unit) == 2
      tied && singleton && units.length == 2 && eachUnitOccursTwice
  let excluded :=
    if coupled then []
    else
      evidence.filterMap fun entry =>
        let unit := entry.2
        let others := evidence.filter fun other => other.1 != entry.1
        let sharedThroughSameEntry := others.any fun other =>
          unit.sameEntryEndpoint other.2
        let sharedWithAnotherLigand := others.any fun other =>
          unit.sameUnit other.2
        let circularlyUnreferenced := others.any fun other =>
          unit.sameUnit other.2 &&
            !(unit.near == other.2.near && rule3UnitHasIndependentFarReference mol unit)
        if sharedThroughSameEntry ||
            (sharedWithAnotherLigand && !cyclic) ||
            circularlyUnreferenced then
          some (unit.addressedKey entry.1)
        else none
  { cyclic := cyclic, coupled := coupled, excluded := excluded, flipped := [] }

/-- Generated policies preserve the selected source-reference frame.  Physical unit counts
provide no reference-exchange witness and therefore never request a geometry flip. -/
@[simp] theorem rule3CenterPolicy_flipped
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (center : ℕ) :
    (rule3CenterPolicy result mol center).flipped = [] := rfl


/-- Source-bound observation reader for one ligand branch.

`some none` is a determinate absence (a non-source node, an excluded occurrence, or a double bond
proved structurally unable to carry `E/Z`); `none` is unknown evidence for an applicable unit and
must propagate as a refusal.

The structural test is deliberately narrow.  A carbonyl `C=O` is not an applicable unit at all: its
oxygen carries no second substituent, so no `seqcis/seqtrans` frame can exist.  Terminal `=CH₂` has
two indistinguishable hydrogens, which no later sequence rule can separate.  Both are proved from
actual written neighbours plus the implicit-hydrogen count, without consulting `E/Z` perception.
A constitutional tie between heavier substituents is *not* absence, because Rules 4--6 may
distinguish it.  Consequently a missing geometry for any other unit, in cyclic or non-cyclic mode,
is unknown evidence and refuses; it is never converted into `some none`. -/
def rule3BranchObserver (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (center : ℕ) (policy : Rule3CenterPolicy) (ligand : ℕ)
    (node : RawMolecule.CanonicalBranchNode) :
    Option (Option RawMolecule.CanonicalRule3Observation) :=
  match rule3SourceUnitOfNode? mol center node with
  | none => some none
  | some unit =>
      if policy.excluded.contains (unit.addressedKey ligand) then some none
      else if rule3UnitStructurallyInapplicable mol unit then some none
      else
        let tetrahedral := rule3CenterTetrahedral mol center
        match rule3CenterGeometry? result mol center tetrahedral policy.cyclic unit with
        | some geometry =>
            let geometry :=
              if policy.flipped.contains ligand && !policy.cyclic then
                flipRule3Geometry geometry
              else geometry
            some (some { unit := unit.key, near := unit.near, far := unit.far,
                         entry? := unit.entry?, geometry := geometry })
        | none => none

/-- Compile one ligand into the canonical Rule-3 key under the centre policy. -/
def compileRule3HierarchyKey? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (center ligand fuel : ℕ) (policy : Rule3CenterPolicy) :
    Option RawMolecule.CanonicalRule3Key :=
  RawMolecule.buildCanonicalRule3Key? mol (rule3BranchChildren mol center)
    (rule3BranchObserver result mol center policy ligand) fuel
    (RawMolecule.canonicalRoot center ligand)

/-- Compile one ligand and refuse any key the builder could not complete. -/
def compileRule3HierarchyKeyComplete? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (center ligand fuel : ℕ) (policy : Rule3CenterPolicy) :
    Option RawMolecule.CanonicalRule3Key :=
  (compileRule3HierarchyKey? result mol center ligand fuel policy).bind fun key =>
    if key.constitutional.complete then some key else none

/-- Rule-3 comparison of two already compiled keys under one centre policy. -/
def compareRule3GeometryWithPolicy? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel center left right : ℕ) (policy : Rule3CenterPolicy) : Option Ordering :=
  (compileRule3HierarchyKeyComplete? result mol center left fuel policy).bind fun leftKey =>
    (compileRule3HierarchyKeyComplete? result mol center right fuel policy).bind fun rightKey =>
      some (RawMolecule.compareSparseCanonicalLayers compare leftKey.rule3 rightKey.rule3)

/-- Optional source-bound Rule-3 comparison at one centre.

`none` means the canonical hierarchy could not be compiled to a complete key (fuel exhaustion,
unsupported labeling, or unknown entry-relative evidence); it is a refusal, never a tie.
`some Ordering.eq` is a genuine tie after complete evidence, so it is the only outcome that may
fall through to later sequence rules. -/
def compareRule3GeometryAtCenter? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel center left right : ℕ) : Option Ordering :=
  compareRule3GeometryWithPolicy? result mol fuel center left right
    (rule3CenterPolicy result mol center)

/-- Outcome class of one constitutionally tied ligand pair under Rule 3. -/
inductive Rule3PairStatus where
  | inapplicable
  | tied
  | decides
  | unavailable
  deriving DecidableEq, Repr

/-- Classify one ligand pair without confusing unknown evidence with a genuine tie.

A strict authoritative constitutional decision makes Rule 3 inapplicable.  An unresolved
constitutional comparison is unavailable (refusal), never inapplicable. -/
def rule3PairStatus (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel center left right : ℕ) : Rule3PairStatus :=
  match mol.compareBranchesAuthoritativeStatus center left right with
  | .lower => Rule3PairStatus.inapplicable
  | .higher => Rule3PairStatus.inapplicable
  | .unresolved => Rule3PairStatus.unavailable
  | .tied =>
      match result.compareRule3GeometryAtCenter? mol fuel center left right with
      | some Ordering.eq => Rule3PairStatus.tied
      | some _ => Rule3PairStatus.decides
      | none => Rule3PairStatus.unavailable

/-- Statuses of the strictly increasing ligand-position pairs at one centre. -/
def rule3CenterPairStatuses (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel center : ℕ) (ligands : List ℕ) : List Rule3PairStatus :=
  (List.range ligands.length).flatMap fun leftIndex =>
    (List.range ligands.length).filterMap fun rightIndex =>
      if leftIndex < rightIndex then
        some (rule3PairStatus result mol fuel center
          (ligands.getD leftIndex 0) (ligands.getD rightIndex 0))
      else none

/-- Compare constitution first and source-bound Rule 3 geometry only after a proved constitutional
tie.

The strict constitutional branches are unchanged.  In both tie branches the decision is the
canonical hierarchy comparison; `none` is a refusal (incomplete evidence), never an equality. -/
def compareBranchesThroughRule3? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel center left right : ℕ) : Option Ordering :=
  match mol.compareBranchesStatus fuel center left right with
  | .lower => some Ordering.lt
  | .higher => some Ordering.gt
  | .unresolved =>
      match mol.compareBranchesAuthoritativeStatus center left right with
      | .lower => some Ordering.lt
      | .higher => some Ordering.gt
      | .unresolved => none
      | .tied =>
          result.compareRule3GeometryAtCenter? mol fuel center left right
  | .tied =>
      -- Two entry paths to the same physical geometrical unit cannot use their different entry
      -- frames to rank each other; the compiled hierarchy has already applied the whole-centre
      -- cancellation policy.  A genuine constitutional tie is the only place Rule 3 may decide.
      result.compareRule3GeometryAtCenter? mol fuel center left right

end ChemistryNormalizationResult

/-- Rank ligand positions with the constitutional comparator followed by perceived Rule 3. -/
def rankBranchPositionsThroughRule3? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel center : ℕ) (branches : List ℕ) : Option (List ℕ) :=
  let atomOf : ℕ → ℕ := fun position => branches.getD position 0
  let compareAt : ℕ → ℕ → Option Ordering := fun a b =>
    result.compareBranchesThroughRule3? mol fuel center (atomOf a) (atomOf b)
  let before : ℕ → ℕ → Bool := fun a b => compareAt a b != some Ordering.lt
  let sorted := sortDescBy before (List.range branches.length)
  let strict :=
    (List.range (sorted.length - 1)).all fun index =>
      match sorted[index]?, sorted[index + 1]? with
      | some left, some right => compareAt left right == some Ordering.gt
      | _, _ => false
  if strict then some sorted else none

/-- Historical flat ranker over `compareBranchesThroughRule3Legacy?`, preserved so modules that
record exact old seed rankings can cite them under an explicit name. -/
def rankBranchPositionsThroughRule3Legacy? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel center : ℕ) (branches : List ℕ) : Option (List ℕ) :=
  let atomOf : ℕ → ℕ := fun position => branches.getD position 0
  let compareAt : ℕ → ℕ → Option Ordering := fun a b =>
    result.compareBranchesThroughRule3Legacy? mol fuel center (atomOf a) (atomOf b)
  let before : ℕ → ℕ → Bool := fun a b => compareAt a b != some Ordering.lt
  let sorted := sortDescBy before (List.range branches.length)
  let strict :=
    (List.range (sorted.length - 1)).all fun index =>
      match sorted[index]?, sorted[index + 1]? with
      | some left, some right => compareAt left right == some Ordering.gt
      | _, _ => false
  if strict then some sorted else none

/-- Tetrahedral assignment using Rules 1a/1b/2 and automatically perceived Rule 3 geometry. -/
def tetrahedralOutcomeThroughRule3 (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel idx : ℕ) : StereoOutcome :=
  match mol.tetrahedralOutcome fuel idx with
  | StereoOutcome.tetrahedral descriptor => StereoOutcome.tetrahedral descriptor
  | StereoOutcome.refused StereoRefusal.unsupportedCentreElement =>
      StereoOutcome.refused StereoRefusal.unsupportedCentreElement
  | StereoOutcome.refused (StereoRefusal.wrongLigandCount found) =>
      StereoOutcome.refused (StereoRefusal.wrongLigandCount found)
  | StereoOutcome.refused StereoRefusal.notSpecified =>
      StereoOutcome.refused StereoRefusal.notSpecified
  | StereoOutcome.alkene descriptor => StereoOutcome.alkene descriptor
  | StereoOutcome.enantiomorphicDoubleBond descriptor =>
      StereoOutcome.enantiomorphicDoubleBond descriptor
  | StereoOutcome.pseudoTetrahedral descriptor => StereoOutcome.pseudoTetrahedral descriptor
  | StereoOutcome.axial descriptor => StereoOutcome.axial descriptor
  | StereoOutcome.planar descriptor => StereoOutcome.planar descriptor
  | StereoOutcome.helical descriptor => StereoOutcome.helical descriptor
  | StereoOutcome.polyhedral descriptor => StereoOutcome.polyhedral descriptor
  | StereoOutcome.refused _ =>
      match mol.atomAt? idx with
      | some spec =>
          match spec.tetrahedral? with
          | some parity =>
              let ligands := mol.ligandsWithLonePair idx
              match rankBranchPositionsThroughRule3? result mol fuel idx ligands with
              | some positions =>
                  StereoOutcome.tetrahedral
                    (RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions))
              | none => mol.tetrahedralOutcome fuel idx
          | none => mol.tetrahedralOutcome fuel idx
      | none => mol.tetrahedralOutcome fuel idx

/-! ### Molecule-wide descriptor-dependent discovery -/

/-- One descriptor fact discovered during the raw-molecule fixed point. -/
structure RawDescriptorFact where
  atom : ℕ
  descriptor : RS
  /-- Whether the center is established as an uppercase chiral unit rather than a lowercase
  pseudoasymmetric unit. -/
  uppercase : Bool
  /-- Largest descriptor-source population consulted on any ligand of this center.  This records
  the width of the descriptor-dependent witness and lets the public assigner distinguish simple
  terminal-seed decisions from still-ambiguous broad hierarchy summaries. -/
  evidenceSize : ℕ := 0
  decisiveRule? : Option CIPRuleFamily := none
  descriptorDependentPairs : ℕ := 0
  /-- Final descending ligand positions used to assign this center.  Auxiliary re-rooting moves
  the incoming position to the front while retaining the other three in this established order. -/
  priorityPositions : List ℕ := []
  deriving DecidableEq, Repr

/-- Descriptor facts indexed by parsed atom. -/
abbrev RawDescriptorState := List RawDescriptorFact

namespace RawDescriptorState

/-- Descriptor currently known at an atom. -/
def factAt? (state : RawDescriptorState) (atom : ℕ) : Option RawDescriptorFact :=
  state.find? fun entry => entry.atom == atom

/-- Descriptor sense currently known at an atom. -/
def descriptorAt? (state : RawDescriptorState) (atom : ℕ) : Option RS :=
  (state.factAt? atom).map RawDescriptorFact.descriptor

/-- Semantic equality of descriptor states, ignoring the incidental list order in which facts were
discovered. -/
def AtomwiseEquivalent (left right : RawDescriptorState) : Prop :=
  ∀ atom, left.factAt? atom = right.factAt? atom

@[refl] theorem atomwiseEquivalent_refl (state : RawDescriptorState) :
    AtomwiseEquivalent state state := by
  intro atom
  rfl

@[symm] theorem atomwiseEquivalent_symm {left right : RawDescriptorState}
    (equivalent : AtomwiseEquivalent left right) : AtomwiseEquivalent right left := by
  intro atom
  exact (equivalent atom).symm

@[trans] theorem atomwiseEquivalent_trans {first second third : RawDescriptorState}
    (firstSecond : AtomwiseEquivalent first second)
    (secondThird : AtomwiseEquivalent second third) : AtomwiseEquivalent first third := by
  intro atom
  exact (firstSecond atom).trans (secondThird atom)

/-- Quotient of raw list representations by their atom-indexed descriptor semantics. -/
def atomwiseSetoid : Setoid RawDescriptorState where
  r := AtomwiseEquivalent
  iseqv :=
    ⟨atomwiseEquivalent_refl, atomwiseEquivalent_symm, atomwiseEquivalent_trans⟩

abbrev SemanticState := Quotient atomwiseSetoid

/-- Embed a concrete descriptor list into its atom-indexed semantic quotient. -/
def semanticMk (state : RawDescriptorState) : SemanticState :=
  Quotient.mk atomwiseSetoid state

/-- Add a newly discovered descriptor without replacing an earlier fixed-point fact. -/
def insertIfAbsent (state : RawDescriptorState) (fact : RawDescriptorFact) : RawDescriptorState :=
  if (state.factAt? fact.atom).isSome then state else state ++ [fact]

/-- Replace a provisional derived fact, or append it when the atom was not known yet. -/
def upsert (state : RawDescriptorState) (fact : RawDescriptorFact) : RawDescriptorState :=
  if (state.factAt? fact.atom).isSome then
    state.map fun existing => if existing.atom == fact.atom then fact else existing
  else
    state ++ [fact]

end RawDescriptorState

/-- Auxiliary local descriptor sense from input parity and deterministic constitutional ordering.

This is not emitted as an absolute descriptor.  It supplies the relative like/unlike evidence Rule
4b needs in fully symmetric systems where no center can be assigned before the others. -/
def tentativeAuxiliaryFactAtAuthoritative? (mol : RawMolecule) (atom : ℕ) :
    Option RawDescriptorFact :=
  match mol.atomAt? atom with
  | some spec =>
      match spec.tetrahedral? with
      | some parity =>
          let ligands := mol.ligandsWithLonePair atom
          if ligands.length != 4 then none else
            let atomOf : ℕ → ℕ := fun position => ligands.getD position 0
            let indices := List.range ligands.length
            let compareAt := fun left right =>
              mol.compareBranchesAuthoritative? atom (atomOf left) (atomOf right)
            let allResolved := indices.all fun left =>
              indices.all fun right => left == right || (compareAt left right).isSome
            if !allResolved then none else
              let positions := sortDescBy
                (fun left right => compareAt left right != some Ordering.lt) indices
              some
              { atom := atom
                descriptor := RawMolecule.descriptorOfParity parity
                  (RawMolecule.permutationIsEven positions)
                uppercase := true
                evidenceSize := 0
                priorityPositions := positions }
      | none => none
  | none => none

/-- Public provisional auxiliary sense routed through the width-unbounded comparator. -/
def tentativeAuxiliaryFactAt? (mol : RawMolecule) (_fuel atom : ℕ) : Option RawDescriptorFact :=
  tentativeAuxiliaryFactAtAuthoritative? mol atom

/-- The capped canonical hierarchy retained by its production-proof API. -/
def branchCanonicalKey? (mol : RawMolecule) (center ligand : ℕ) :
    Option RawMolecule.CanonicalBranchKey :=
  let fuel := 2 * mol.atomCount + 2
  mol.buildCanonicalBranchKey RawMolecule.defaultBranchWidthCap fuel
    (RawMolecule.canonicalRoot center ligand)

/-- Width- and matching-cap-free compiled hierarchy for chemistry-facing authoritative calls. -/
def branchCanonicalKeyAuthoritative? (mol : RawMolecule) (center ligand : ℕ) :
    Option RawMolecule.CanonicalBranchKey :=
  let fuel := 2 * mol.atomCount + 2
  mol.buildCanonicalBranchKeyAuthoritative fuel (RawMolecule.canonicalRoot center ligand)

/-- Width-unbounded hierarchy used by every public Rules 4a--5 branch observation. -/
def branchDescriptorCanonicalKey? (mol : RawMolecule) (center ligand : ℕ) :
    Option RawMolecule.CanonicalBranchKey :=
  branchCanonicalKeyAuthoritative? mol center ligand

/-- Descriptor-bearing centers on a branch in the compiled canonical digraph hierarchy.

`realAtoms` shares the exact sphere and parent-ranked positional paths used for Rules 1a/1b/2.
Reading descriptor facts through it prevents a later source on one child branch from sliding into
the slot of an earlier source on another child branch. -/
def branchDescriptorLayers (mol : RawMolecule) (state : RawDescriptorState)
    (center ligand : ℕ) : List (List RawDescriptorFact) :=
  match branchDescriptorCanonicalKey? mol center ligand with
  | none => []
  | some key =>
      key.realAtoms.map fun layer =>
        layer.filterMap fun entry => state.factAt? entry.2

/-- Descriptor-bearing centers flattened in canonical sphere order. -/
def branchDescriptorSequence (mol : RawMolecule) (state : RawDescriptorState)
    (center ligand : ℕ) : List RawDescriptorFact :=
  (branchDescriptorLayers mol state center ligand).flatten

/-- Whether all descriptor sources on a ligand lie on one root-to-leaf path.

For such a branch the priority walk cannot lose a parent/child pairing: every later source is below
every earlier source.  A source with later evidence still reachable from the ligand after that
source is removed exposes a side branch or ring bypass and is therefore not linear. -/
def branchDescriptorSequenceIsLinear (mol : RawMolecule) (ligand : ℕ)
    (descriptors : List RawDescriptorFact) : Bool :=
  (descriptors.zip (List.range descriptors.length)).all fun entry =>
    let source := entry.1.atom
    let later := (descriptors.drop (entry.2 + 1)).map RawDescriptorFact.atom
    if later.isEmpty || source == ligand then true else
      let rootSide := mol.reachableAvoiding (mol.atomCount + 1) source [ligand] [ligand]
      later.all fun atom => !(rootSide.contains atom)

/-- Lexicographically compare two equally populated hierarchy sequences.  A descriptor-dependent
rule may decide only when both branches expose corresponding evidence; a missing source therefore
remains a safe tie instead of being treated as a low-priority phantom descriptor. -/
def compareCorrespondingSequences {alpha : Type}
    (compare : alpha → alpha → Ordering) : List alpha → List alpha → Ordering
  | left, right =>
      if left.isEmpty || right.isEmpty then Ordering.eq else
        let decisions := (left.zip right).map fun pair => compare pair.1 pair.2
        (decisions.find? fun decision => decision != Ordering.eq).getD Ordering.eq

/-- Rule-4a hierarchy of descriptor-bearing units on a ligand. -/
def branchRule4aSequence (descriptors : List RawDescriptorFact) :
    List OfficialStereogenicUnitKind :=
  descriptors.map fun fact =>
    if fact.uppercase then OfficialStereogenicUnitKind.chiral
    else OfficialStereogenicUnitKind.pseudoasymmetric

/-- Rule-4a labels at every real canonical node, retaining nonstereogenic placeholders.

Rule 4a is sphere-major: a pseudoasymmetric unit at an earlier corresponding node precedes a
nonstereogenic node even if the latter branch reaches a chiral unit in a later sphere.  Filtering to
descriptor-bearing nodes loses exactly that decision. -/
def branchRule4aSparseLayers (mol : RawMolecule) (state : RawDescriptorState)
    (center ligand : ℕ) : Option (List (List (List ℕ × OfficialStereogenicUnitKind))) :=
  match branchDescriptorCanonicalKey? mol center ligand with
  | none => none
  | some key =>
      let hasPendingAnnotatedCenter := key.realAtoms.any fun layer =>
        layer.any fun entry =>
          match mol.atomAt? entry.2 with
          | some spec => spec.tetrahedral?.isSome && (state.factAt? entry.2).isNone
          | none => false
      if hasPendingAnnotatedCenter then none else
        some (key.realAtoms.map fun layer =>
          layer.map fun entry =>
            let kind := match state.factAt? entry.2 with
              | some fact =>
                  if fact.uppercase then OfficialStereogenicUnitKind.chiral
                  else OfficialStereogenicUnitKind.pseudoasymmetric
              | none => OfficialStereogenicUnitKind.nonstereogenic
            (entry.1, kind))

/-- Rule-4b like/unlike sequence for one ligand.

The reference descriptor is the descriptor on the highest-ranked chiral node.  It is paired with
every chiral-node descriptor in decreasing hierarchical order, including itself.  This is the
essential difference from merely comparing the first two descriptors: the first pair is always
like, and the first *later* unlike pair is often the actual decision in P-92.5.2 examples. -/
def branchRule4bSequence (descriptors : List RawDescriptorFact) :
    List OfficialDescriptorPairKind :=
  let chiral := descriptors.filter RawDescriptorFact.uppercase
  match chiral.head? with
  | none => []
  | some reference => chiral.map fun fact =>
      OfficialRule5Descriptor.pairKind
        (OfficialRule5Descriptor.ofRS reference.descriptor)
        (OfficialRule5Descriptor.ofRS fact.descriptor)

/-- Rule-4b reference senses selected from a descriptor population.

The reference is the majority sense in the first descriptor-bearing hierarchical population.  If
the two senses are equally represented, both possible references must be carried forward and the
resulting like/unlike lists compared in descending order.  Picking the first encountered descriptor
is enumeration-dependent and gives the wrong answer for branched and cyclic descriptor
hierarchies. -/
def branchRule4bReferences (descriptors : List RawDescriptorFact) : List RS :=
  let chiral := descriptors.filter RawDescriptorFact.uppercase
  let rCount := (chiral.filter fun fact => fact.descriptor == RS.R).length
  let sCount := (chiral.filter fun fact => fact.descriptor == RS.S).length
  if rCount == 0 && sCount == 0 then []
  else if sCount < rCount then [RS.R]
  else if rCount < sCount then [RS.S]
  else [RS.R, RS.S]

/-- Like/unlike list for an explicitly selected Rule-4b reference sense. -/
def branchRule4bSequenceFor (reference : RS) (descriptors : List RawDescriptorFact) :
    List OfficialDescriptorPairKind :=
  (descriptors.filter RawDescriptorFact.uppercase).map fun fact =>
    OfficialRule5Descriptor.pairKind
      (OfficialRule5Descriptor.ofRS reference)
      (OfficialRule5Descriptor.ofRS fact.descriptor)

/-- Rule-4b reference senses from the first descriptor-bearing canonical sphere. -/
def branchRule4bReferencesFromLayers (layers : List (List RawDescriptorFact)) : List RS :=
  match layers.find? fun layer => !(layer.filter RawDescriptorFact.uppercase).isEmpty with
  | some layer => branchRule4bReferences layer
  | none => []

/-- Like/unlike sequence for a selected reference, retaining the parent-ranked canonical order.

Pair kinds must not be independently sorted inside each sphere.  Doing so lets a descriptor under
one parent trade places with a descriptor under another and destroys the correspondence that Rule
4b compares (for example `S,R / R,S` versus `R,S / S,S`).  Child re-ranking is already represented
by the canonical parent paths; the descriptor projection must preserve those paths. -/
def branchRule4bSequenceForLayers (reference : RS) (layers : List (List RawDescriptorFact)) :
    List OfficialDescriptorPairKind :=
  layers.flatMap fun layer =>
    (layer.filter RawDescriptorFact.uppercase).map fun fact =>
      OfficialRule5Descriptor.pairKind
        (OfficialRule5Descriptor.ofRS reference)
        (OfficialRule5Descriptor.ofRS fact.descriptor)

/-- Single-reference criterion (b) re-ranks each tied population relative to that unique
reference.  In the two-reference criterion (c), by contrast, independently sorting each sphere
would destroy the pairing between the two alternative complete lists. -/
def branchRule4bSequenceForLayersUnique (reference : RS)
    (layers : List (List RawDescriptorFact)) : List OfficialDescriptorPairKind :=
  layers.flatMap fun layer =>
    sortDescBy (fun left right => OfficialDescriptorPairKind.compare left right != Ordering.lt)
      ((layer.filter RawDescriptorFact.uppercase).map fun fact =>
        OfficialRule5Descriptor.pairKind
          (OfficialRule5Descriptor.ofRS reference)
          (OfficialRule5Descriptor.ofRS fact.descriptor))

/-- Full Rule-4b comparison, including the two-reference case of criterion (c). -/
def compareRule4bHierarchies (left right : List RawDescriptorFact) : Ordering :=
  let sequences := fun descriptors =>
    (branchRule4bReferences descriptors).map fun reference =>
      branchRule4bSequenceFor reference descriptors
  let before := fun a b =>
    compareCorrespondingSequences OfficialDescriptorPairKind.compare a b != Ordering.lt
  let leftSequences := sortDescBy before (sequences left)
  let rightSequences := sortDescBy before (sequences right)
  compareCorrespondingSequences
    (compareCorrespondingSequences OfficialDescriptorPairKind.compare)
    leftSequences rightSequences

/-- Opponent-independent positional Rule-4b signature.

Each inner list is one complete like/unlike reading encoded by the official pair priority
(`like = 1`, `unlike = 0`).  A strict first-population majority contributes one reading; a tied
population contributes both complementary readings, sorted in descending lexicographic order.
Keeping signature construction separate from comparison makes traversal independence and the
order laws explicit: a ligand's key never depends on the ligand against which it is compared. -/
def rule4bCanonicalSignature (layers : List (List RawDescriptorFact)) : List (List ℕ) :=
  let sequences := fun layers =>
    let references := branchRule4bReferencesFromLayers layers
    references.map fun reference =>
      if references.length == 1 then branchRule4bSequenceForLayersUnique reference layers
      else branchRule4bSequenceForLayers reference layers
  let encoded := (sequences layers).map fun sequence =>
    sequence.map OfficialDescriptorPairKind.priority
  let before := fun a b =>
    compare a b != Ordering.lt
  sortDescBy before encoded

/-- Positional Rule-4b comparison over canonical descriptor spheres.

This is deliberately a pullback of Lean's lawful lexicographic list comparison along the canonical
signature.  Consequently its strict priority and induced tie are transitive for arbitrary inputs;
Rule-4a eligibility is needed for chemical relevance, not for the order law itself. -/
def compareRule4bLayerHierarchies (left right : List (List RawDescriptorFact)) : Ordering :=
  Ordering.byKey rule4bCanonicalSignature compare left right

/-- Number of Rule-4b reference descriptors selected by criterion (b)/(c): one for a strict
majority among the descriptor sources, two when `R` and `S` occur equally often. -/
def branchRule4bReferenceCount (descriptors : List RawDescriptorFact) : ℕ :=
  let chiral := descriptors.filter RawDescriptorFact.uppercase
  let rCount := (chiral.filter fun fact => fact.descriptor == RS.R).length
  let sCount := (chiral.filter fun fact => fact.descriptor == RS.S).length
  if rCount == 0 && sCount == 0 then 0
  else if rCount == sCount then 2
  else 1

/-- Two uppercase descriptor sequences are enantiomorphic when every corresponding sense is
opposite.  Their Rule-4b like/unlike patterns are identical after each ligand selects its own
reference, so Rule 4b must tie and allow Rule 5 to compare the mirror senses. -/
def rule4bSequencesEnantiomorphic (left right : List RawDescriptorFact) : Bool :=
  let leftSenses := (left.filter RawDescriptorFact.uppercase).map RawDescriptorFact.descriptor
  let rightSenses := (right.filter RawDescriptorFact.uppercase).map RawDescriptorFact.descriptor
  !leftSenses.isEmpty && leftSenses.length == rightSenses.length &&
    (leftSenses.zip rightSenses).all fun pair => pair.1 != pair.2

/-- Rule-4c hierarchy of lowercase pseudoasymmetric descriptors. -/
def branchRule4cSequence (descriptors : List RawDescriptorFact) :
    List OfficialPseudoasymmetricDescriptor :=
  descriptors.filterMap fun fact =>
    if fact.uppercase then none else
      some (match fact.descriptor with
        | RS.R => OfficialPseudoasymmetricDescriptor.r
        | RS.S => OfficialPseudoasymmetricDescriptor.s)

/-- Rule-5 hierarchy of uppercase tetrahedral descriptors. -/
def branchRule5Sequence (descriptors : List RawDescriptorFact) :
    List OfficialRule5Descriptor :=
  descriptors.filterMap fun fact =>
    if fact.uppercase then some (OfficialRule5Descriptor.ofRS fact.descriptor) else none

/-- Positional lowercase Rule-4c priorities (`r > s > absent`). -/
def branchRule4cSparseLayers (mol : RawMolecule) (state : RawDescriptorState)
    (center ligand : ℕ) : List (List (List ℕ × ℕ)) :=
  match branchDescriptorCanonicalKey? mol center ligand with
  | none => []
  | some key => key.realAtoms.map fun layer => layer.map fun entry =>
      let priority := match state.factAt? entry.2 with
        | some fact =>
            if fact.uppercase then 0 else if fact.descriptor == RS.R then 2 else 1
        | none => 0
      (entry.1, priority)

/-- Positional uppercase Rule-5 priorities (`R > S > absent`). -/
def branchRule5SparseLayers (mol : RawMolecule) (state : RawDescriptorState)
    (center ligand : ℕ) : List (List (List ℕ × ℕ)) :=
  match branchDescriptorCanonicalKey? mol center ligand with
  | none => []
  | some key => key.realAtoms.map fun layer => layer.map fun entry =>
      let priority := match state.factAt? entry.2 with
        | some fact =>
            if fact.uppercase then if fact.descriptor == RS.R then 2 else 1 else 0
        | none => 0
      (entry.1, priority)

/-- Descriptor rule used while recursively refining canonical sibling order.

Rules 4b and 5 carry distinct references for the left and right digraph.  This is necessary when
criterion (c) compares an `R`-reference list on one ligand with an `S`-reference list on the other. -/
inductive RawDescriptorRuleStage where
  | rule4a
  | rule4b (leftReference rightReference : RS)
  | rule4c
  | rule5 (leftReference rightReference : RS)
  deriving DecidableEq, Repr

/-- The same descriptor stage specialized to comparisons internal to the left digraph. -/
def RawDescriptorRuleStage.leftInternal : RawDescriptorRuleStage → RawDescriptorRuleStage
  | .rule4a => .rule4a
  | .rule4b reference _ => .rule4b reference reference
  | .rule4c => .rule4c
  | .rule5 reference _ => .rule5 reference reference

/-- The same descriptor stage specialized to comparisons internal to the right digraph. -/
def RawDescriptorRuleStage.rightInternal : RawDescriptorRuleStage → RawDescriptorRuleStage
  | .rule4a => .rule4a
  | .rule4b _ reference => .rule4b reference reference
  | .rule4c => .rule4c
  | .rule5 _ reference => .rule5 reference reference

/-- Auxiliary descriptor sense of one real-center occurrence after re-rooting at that node.

The incoming edge is the unique up edge and is ordered first by the reference algorithm.  Remaining
edges are constitutionally ranked in the re-rooted local environment.  This makes the two
occurrences of one configuration on opposite sides of a ring capable of carrying opposite
auxiliary senses, which a single molecule-global fact cannot represent. -/
def rawAuxiliaryOccurrenceSenseWithCap (mol : RawMolecule)
    (node : RawMolecule.CanonicalBranchNode)
    (fact : RawDescriptorFact) : RS :=
  match mol.atomAt? node.atom with
  | some spec =>
      match spec.tetrahedral? with
      | some parity =>
          let ligands := mol.ligandsWithLonePair node.atom
          match (ligands.zipIdx.find? fun entry => entry.1 == node.parent) with
          | some parentEntry =>
              let establishedOrder :=
                if fact.priorityPositions.length == ligands.length then fact.priorityPositions
                else
                  let atomOf := fun position => ligands.getD position 0
                  let before := fun left right =>
                    mol.compareBranches (2 * mol.atomCount + 2) node.atom
                      (atomOf left) (atomOf right) != Ordering.lt
                  sortDescBy before (List.range ligands.length)
              let occurrenceOrder := parentEntry.2 :: establishedOrder.erase parentEntry.2
              RawMolecule.descriptorOfParity parity
                (RawMolecule.permutationIsEven occurrenceOrder)
          | none => fact.descriptor
      | none => fact.descriptor
  | none => fact.descriptor

/-- Width-unbounded auxiliary descriptor sense for authoritative circular solvers.

This preserves the established complete-position behavior.  A defensive fallback rebuilds an
incomplete order only when every required authoritative comparison resolves; otherwise it retains
the stored descriptor instead of manufacturing parity from an arbitrary order. -/
def rawAuxiliaryOccurrenceSenseAuthoritative (mol : RawMolecule)
    (node : RawMolecule.CanonicalBranchNode) (fact : RawDescriptorFact) : RS :=
  match mol.atomAt? node.atom with
  | some spec =>
      match spec.tetrahedral? with
      | some parity =>
          let ligands := mol.ligandsWithLonePair node.atom
          match (ligands.zipIdx.find? fun entry => entry.1 == node.parent) with
          | some parentEntry =>
              let senseFromOrder := fun establishedOrder =>
                let occurrenceOrder := parentEntry.2 :: establishedOrder.erase parentEntry.2
                RawMolecule.descriptorOfParity parity
                  (RawMolecule.permutationIsEven occurrenceOrder)
              if fact.priorityPositions.length == ligands.length then
                senseFromOrder fact.priorityPositions
              else
                let atomOf := fun position => ligands.getD position 0
                let indices := List.range ligands.length
                let compareAt := fun left right =>
                  mol.compareBranchesAuthoritative? node.atom (atomOf left) (atomOf right)
                let allResolved := indices.all fun left =>
                  indices.all fun right => left == right || (compareAt left right).isSome
                if !allResolved then fact.descriptor else
                  senseFromOrder (sortDescBy
                    (fun left right => compareAt left right != some Ordering.lt) indices)
          | none => fact.descriptor
      | none => fact.descriptor
  | none => fact.descriptor

/-- Public occurrence sense routed through the width-unbounded comparator. -/
def rawAuxiliaryOccurrenceSense (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (fact : RawDescriptorFact) : RS :=
  rawAuxiliaryOccurrenceSenseAuthoritative mol node fact

/-- Node-local descriptor priority on one side of a paired hierarchical comparison. -/
def rawDescriptorNodePriority (mol : RawMolecule) (state : RawDescriptorState)
    (stage : RawDescriptorRuleStage)
    (leftSide : Bool) (node : RawMolecule.CanonicalBranchNode) : ℕ :=
  match node.provenance with
  | RawMolecule.CanonicalNodeProvenance.realAtom =>
      match state.factAt? node.atom with
      | none => 0
      | some fact =>
          let descriptor := rawAuxiliaryOccurrenceSense mol node fact
          match stage with
          | .rule4a => if fact.uppercase then 2 else 1
          | .rule4b leftReference rightReference =>
              let reference := if leftSide then leftReference else rightReference
              if fact.uppercase && descriptor == reference then 1 else 0
          | .rule4c =>
              if fact.uppercase then 0 else if descriptor == RS.R then 2 else 1
          | .rule5 leftReference rightReference =>
              let reference := if leftSide then leftReference else rightReference
              if fact.uppercase && descriptor == reference then 1 else 0
  | _ => 0

/-- Compare one full sphere under a descriptor rule without losing parent positions. -/
def compareRawDescriptorPairLabels (mol : RawMolecule) (state : RawDescriptorState)
    (stage : RawDescriptorRuleStage) :
    List (RawMolecule.CanonicalBranchNode × RawMolecule.CanonicalBranchNode) → Ordering
  | [] => Ordering.eq
  | pair :: pairs =>
      match compare (rawDescriptorNodePriority mol state stage true pair.1)
          (rawDescriptorNodePriority mol state stage false pair.2) with
      | Ordering.eq => compareRawDescriptorPairLabels mol state stage pairs
      | decision => decision

/-- Expand paired canonical nodes using independently refined sibling orders on the two sides. -/
def nextRawDescriptorPairs? (mol : RawMolecule)
    (beforeLeft beforeRight : RawMolecule.CanonicalBranchNode →
      RawMolecule.CanonicalBranchNode → Option Ordering) :
    List (RawMolecule.CanonicalBranchNode × RawMolecule.CanonicalBranchNode) →
      Option (List (RawMolecule.CanonicalBranchNode × RawMolecule.CanonicalBranchNode))
  | [] => some []
  | pair :: pairs => do
      let rest ← nextRawDescriptorPairs? mol beforeLeft beforeRight pairs
      if mol.canonicalTerminal pair.1 && mol.canonicalTerminal pair.2 then
        some rest
      else
        let left ← mol.rankedCanonicalChildren? beforeLeft pair.1
        let right ← mol.rankedCanonicalChildren? beforeRight pair.2
        some (left.zip right ++ rest)

/-- Apply one descriptor rule exhaustively, sphere before sphere. -/
def compareRawDescriptorRule (mol : RawMolecule) (state : RawDescriptorState)
    (beforeLeft beforeRight : RawMolecule.CanonicalBranchNode →
      RawMolecule.CanonicalBranchNode → Option Ordering)
    (stage : RawDescriptorRuleStage) :
    ℕ → List (RawMolecule.CanonicalBranchNode × RawMolecule.CanonicalBranchNode) →
      Option Ordering
  | 0, pairs =>
      if RawMolecule.defaultBranchWidthCap < pairs.length then none else
        match compareRawDescriptorPairLabels mol state stage pairs with
        | Ordering.eq =>
            match nextRawDescriptorPairs? mol beforeLeft beforeRight pairs with
            | some [] => some Ordering.eq
            | _ => none
        | decision => some decision
  | fuel + 1, pairs =>
      if RawMolecule.defaultBranchWidthCap < pairs.length then none else
        match compareRawDescriptorPairLabels mol state stage pairs with
        | Ordering.eq =>
            match nextRawDescriptorPairs? mol beforeLeft beforeRight pairs with
            | none => none
            | some [] => some Ordering.eq
            | some next => compareRawDescriptorRule mol state beforeLeft beforeRight stage fuel next
        | decision => some decision

/-- Recursively refined constitutional-plus-descriptor branch comparison.

The recursive comparison ranks siblings one level shallower; the outer walk then compares complete
spheres under each rule.  This is the same terminating refinement used by the canonical Rule-1/2
engine, extended with side-specific references for Rules 4b and 5. -/
def compareRawDescriptorBranchAt (mol : RawMolecule) (state : RawDescriptorState) :
    ℕ → RawDescriptorRuleStage → RawMolecule.CanonicalBranchNode →
      RawMolecule.CanonicalBranchNode → Option Ordering
  | 0, stage, left, right =>
      let decision :=
        match mol.compareCanonicalNodeThrough? RawMolecule.CanonicalRuleStage.rule2 left right with
      | none => none
      | some Ordering.eq =>
          match compare (rawDescriptorNodePriority mol state .rule4a true left)
              (rawDescriptorNodePriority mol state .rule4a false right) with
          | Ordering.eq =>
              match stage with
              | .rule4a => some Ordering.eq
              | .rule4b _ _ | .rule4c | .rule5 _ _ =>
                  some (compare (rawDescriptorNodePriority mol state stage true left)
                    (rawDescriptorNodePriority mol state stage false right))
          | decision => some decision
      | some decision => some decision
      match decision with
      | some Ordering.eq =>
          if mol.canonicalTerminal left && mol.canonicalTerminal right then decision else none
      | _ => decision
  | fuel + 1, stage, left, right =>
      match mol.compareCanonicalBranchAtSupported? (fuel + 1)
          RawMolecule.CanonicalRuleStage.rule2 left right with
      | none => none
      | some Ordering.lt => some Ordering.lt
      | some Ordering.gt => some Ordering.gt
      | some Ordering.eq =>
          let beforeLeft := compareRawDescriptorBranchAt mol state fuel stage.leftInternal
          let beforeRight := compareRawDescriptorBranchAt mol state fuel stage.rightInternal
          let compareStage := fun selected =>
            compareRawDescriptorRule mol state beforeLeft beforeRight selected (fuel + 1)
              [(left, right)]
          match compareStage .rule4a with
          | none => none
          | some Ordering.lt => some Ordering.lt
          | some Ordering.gt => some Ordering.gt
          | some Ordering.eq =>
              match stage with
              | .rule4a => some Ordering.eq
              | .rule4b leftReference rightReference =>
                  compareStage (.rule4b leftReference rightReference)
              | .rule4c =>
                  -- Rule 4c ranks lowercase auxiliary descriptors only.  Letting the recursive
                  -- sibling refinement run with an all-zero Rule-4c key can otherwise turn an
                  -- arbitrary canonical pairing of constitutionally equivalent branches into a
                  -- decision even though no `r/s` occurrence exists anywhere in the state.
                  if state.any fun fact => !fact.uppercase then compareStage .rule4c
                  else some Ordering.eq
              | .rule5 leftReference rightReference =>
                  let rule4c :=
                    if state.any fun fact => !fact.uppercase then compareStage .rule4c
                    else some Ordering.eq
                  match rule4c with
                  | some Ordering.eq => compareStage (.rule5 leftReference rightReference)
                  | decision => decision

/-- Dynamic descriptor comparison for two ligand roots, bounded to the molecule's graph depth. -/
def compareRawDescriptorBranches? (mol : RawMolecule) (state : RawDescriptorState)
    (stage : RawDescriptorRuleStage) (center left right : ℕ) : Option Ordering :=
  let leftRoot := RawMolecule.canonicalRoot center left
  let rightRoot := RawMolecule.canonicalRoot center right
  let fuel := mol.atomCount + 1
  -- This entry point is reached only after `compareBranchesStatus` (or an explicit molecular
  -- automorphism) has established a Rule-1/2 tie between the two ligand roots.  Re-running the
  -- lower-level canonical branch comparator at those roots can disagree merely because it chose
  -- a different pairing of equivalent cyclic children, and must not be allowed to masquerade as
  -- a descriptor-rule decision.  Constitutional comparisons still recursively refine sibling
  -- order below the already-tied roots.
  let beforeLeft := compareRawDescriptorBranchAt mol state fuel stage.leftInternal
  let beforeRight := compareRawDescriptorBranchAt mol state fuel stage.rightInternal
  let compareStage := fun selected =>
    compareRawDescriptorRule mol state beforeLeft beforeRight selected fuel [(leftRoot, rightRoot)]
  match compareStage .rule4a with
  | none => none
  | some Ordering.lt => some Ordering.lt
  | some Ordering.gt => some Ordering.gt
  | some Ordering.eq =>
      match stage with
      | .rule4a => some Ordering.eq
      | .rule4b leftReference rightReference =>
          compareStage (.rule4b leftReference rightReference)
      | .rule4c =>
          if state.any fun fact => !fact.uppercase then compareStage .rule4c
          else some Ordering.eq
      | .rule5 leftReference rightReference =>
          let rule4c :=
            if state.any fun fact => !fact.uppercase then compareStage .rule4c
            else some Ordering.eq
          match rule4c with
          | some Ordering.eq => compareStage (.rule5 leftReference rightReference)
          | decision => decision

/-! ### Authoritative descriptor-bearing branch comparison -/

/-- Expand descriptor-paired nodes with bonding-number-six child arity and no sphere-width cap. -/
def nextRawDescriptorPairsAuthoritative? (mol : RawMolecule)
    (beforeLeft beforeRight : RawMolecule.CanonicalBranchNode →
      RawMolecule.CanonicalBranchNode → Option Ordering) :
    List (RawMolecule.CanonicalBranchNode × RawMolecule.CanonicalBranchNode) →
      Option (List (RawMolecule.CanonicalBranchNode × RawMolecule.CanonicalBranchNode))
  | [] => some []
  | pair :: pairs => do
      let rest ← nextRawDescriptorPairsAuthoritative? mol beforeLeft beforeRight pairs
      if mol.canonicalTerminal pair.1 && mol.canonicalTerminal pair.2 then some rest else
        let left ← mol.rankedCanonicalChildrenAuthoritative? beforeLeft pair.1
        let right ← mol.rankedCanonicalChildrenAuthoritative? beforeRight pair.2
        some (left.zip right ++ rest)

/-- Apply one descriptor rule to complete finite spheres without an operational width limit. -/
def compareRawDescriptorRuleAuthoritative (mol : RawMolecule) (state : RawDescriptorState)
    (beforeLeft beforeRight : RawMolecule.CanonicalBranchNode →
      RawMolecule.CanonicalBranchNode → Option Ordering)
    (stage : RawDescriptorRuleStage) :
    ℕ → List (RawMolecule.CanonicalBranchNode × RawMolecule.CanonicalBranchNode) → Option Ordering
  | 0, pairs =>
      match compareRawDescriptorPairLabels mol state stage pairs with
      | Ordering.eq =>
          match nextRawDescriptorPairsAuthoritative? mol beforeLeft beforeRight pairs with
          | some [] => some Ordering.eq
          | _ => none
      | decision => some decision
  | fuel + 1, pairs =>
      match compareRawDescriptorPairLabels mol state stage pairs with
      | Ordering.eq =>
          match nextRawDescriptorPairsAuthoritative? mol beforeLeft beforeRight pairs with
          | none => none
          | some [] => some Ordering.eq
          | some next =>
              compareRawDescriptorRuleAuthoritative mol state beforeLeft beforeRight stage fuel next
      | decision => some decision

/-- Recursively refined Rules 1a--5 comparison using authoritative constitutional labels and
bonding-number-six descriptor spheres. -/
def compareRawDescriptorBranchAtAuthoritative (mol : RawMolecule) (state : RawDescriptorState) :
    ℕ → RawDescriptorRuleStage → RawMolecule.CanonicalBranchNode →
      RawMolecule.CanonicalBranchNode → Option Ordering
  | 0, stage, left, right =>
      let decision :=
        match mol.compareCanonicalNodeThroughAuthoritative?
            RawMolecule.CanonicalRuleStage.rule2 left right with
        | none => none
        | some Ordering.eq =>
            match compare (rawDescriptorNodePriority mol state .rule4a true left)
                (rawDescriptorNodePriority mol state .rule4a false right) with
            | Ordering.eq =>
                match stage with
                | .rule4a => some Ordering.eq
                | .rule4b _ _ | .rule4c | .rule5 _ _ =>
                    some (compare (rawDescriptorNodePriority mol state stage true left)
                      (rawDescriptorNodePriority mol state stage false right))
            | decision => some decision
        | some decision => some decision
      match decision with
      | some Ordering.eq =>
          if mol.canonicalTerminal left && mol.canonicalTerminal right then decision else none
      | _ => decision
  | fuel + 1, stage, left, right =>
      match mol.compareCanonicalBranchAuthoritativeAt? (fuel + 1)
          RawMolecule.CanonicalRuleStage.rule2 left right with
      | none => none
      | some Ordering.lt => some Ordering.lt
      | some Ordering.gt => some Ordering.gt
      | some Ordering.eq =>
          let beforeLeft := compareRawDescriptorBranchAtAuthoritative mol state fuel stage.leftInternal
          let beforeRight := compareRawDescriptorBranchAtAuthoritative mol state fuel stage.rightInternal
          let compareStage := fun selected =>
            compareRawDescriptorRuleAuthoritative mol state beforeLeft beforeRight selected
              (fuel + 1) [(left, right)]
          match compareStage .rule4a with
          | none => none
          | some Ordering.lt => some Ordering.lt
          | some Ordering.gt => some Ordering.gt
          | some Ordering.eq =>
              match stage with
              | .rule4a => some Ordering.eq
              | .rule4b leftReference rightReference =>
                  compareStage (.rule4b leftReference rightReference)
              | .rule4c =>
                  if state.any fun fact => !fact.uppercase then compareStage .rule4c
                  else some Ordering.eq
              | .rule5 leftReference rightReference =>
                  let rule4c :=
                    if state.any fun fact => !fact.uppercase then compareStage .rule4c
                    else some Ordering.eq
                  match rule4c with
                  | some Ordering.eq => compareStage (.rule5 leftReference rightReference)
                  | decision => decision

/-- Descriptor comparison at a constitutionally tied ligand root on the authoritative path. -/
def compareRawDescriptorBranchesAuthoritative? (mol : RawMolecule) (state : RawDescriptorState)
    (stage : RawDescriptorRuleStage) (center left right : ℕ) : Option Ordering :=
  let leftRoot := RawMolecule.canonicalRoot center left
  let rightRoot := RawMolecule.canonicalRoot center right
  let fuel := mol.atomCount + 1
  let beforeLeft := compareRawDescriptorBranchAtAuthoritative mol state fuel stage.leftInternal
  let beforeRight := compareRawDescriptorBranchAtAuthoritative mol state fuel stage.rightInternal
  let compareStage := fun selected =>
    compareRawDescriptorRuleAuthoritative mol state beforeLeft beforeRight selected fuel
      [(leftRoot, rightRoot)]
  match compareStage .rule4a with
  | none => none
  | some Ordering.lt => some Ordering.lt
  | some Ordering.gt => some Ordering.gt
  | some Ordering.eq =>
      match stage with
      | .rule4a => some Ordering.eq
      | .rule4b leftReference rightReference =>
          compareStage (.rule4b leftReference rightReference)
      | .rule4c =>
          if state.any fun fact => !fact.uppercase then compareStage .rule4c else some Ordering.eq
      | .rule5 leftReference rightReference =>
          let rule4c :=
            if state.any fun fact => !fact.uppercase then compareStage .rule4c else some Ordering.eq
          match rule4c with
          | some Ordering.eq => compareStage (.rule5 leftReference rightReference)
          | decision => decision

/-- Fast proved comparison followed by the exact authoritative fallback only on exhaustion. -/
def compareRawDescriptorBranchesComplete? (mol : RawMolecule) (state : RawDescriptorState)
    (stage : RawDescriptorRuleStage) (center left right : ℕ) : Option Ordering :=
  match compareRawDescriptorBranches? mol state stage center left right with
  | some decision => some decision
  | none => compareRawDescriptorBranchesAuthoritative? mol state stage center left right

/-- Rule-4b references from the first descriptor-bearing sphere using occurrence-local senses. -/
def branchRule4bOccurrenceReferences (mol : RawMolecule) (state : RawDescriptorState)
    (center ligand : ℕ) : List RS :=
  let rec search : ℕ → List RawMolecule.CanonicalBranchNode → List RS
    | 0, _ => []
    | _ + 1, [] => []
    | fuel + 1, frontier =>
        let facts := frontier.filterMap fun node =>
          match node.provenance, state.factAt? node.atom with
          | RawMolecule.CanonicalNodeProvenance.realAtom, some fact =>
              if fact.uppercase then
                some { fact with
                  descriptor := rawAuxiliaryOccurrenceSense mol node fact }
              else none
          | _, _ => none
        if facts.isEmpty then
          search fuel (frontier.flatMap mol.canonicalChildren)
        else
          branchRule4bReferences facts
  search (mol.atomCount + 1) [RawMolecule.canonicalRoot center ligand]

/-- Sort the two criterion-(c) reference lists for one ligand by their complete pair patterns. -/
def rankRule4bReferences? (mol : RawMolecule) (state : RawDescriptorState)
    (center ligand : ℕ) : List RS → Option (List RS)
  | [first, second] => do
      let decision ← compareRawDescriptorBranchesComplete? mol state (.rule4b first second)
        center ligand ligand
      if decision == Ordering.lt then some [second, first] else some [first, second]
  | references => some references

/-- Dynamic Rule-4b comparison for both single-reference criterion (b) and two-list criterion (c). -/
def compareRule4bRecursive? (mol : RawMolecule) (state : RawDescriptorState)
    (center left right : ℕ) : Option Ordering :=
  let leftReferences := branchRule4bOccurrenceReferences mol state center left
  let rightReferences := branchRule4bOccurrenceReferences mol state center right
  match leftReferences, rightReferences with
  -- IUPAC P-92.5.2.1 criterion (c)(i): when the number of reference descriptors differs,
  -- the ligand with one reference descriptor precedes the ligand with two.
  | [_], [_, _] => some Ordering.gt
  | [_, _], [_] => some Ordering.lt
  | [leftReference], [rightReference] =>
      compareRawDescriptorBranchesComplete? mol state (.rule4b leftReference rightReference)
        center left right
  | [_, _], [_, _] => do
      let rankedLeft ← rankRule4bReferences? mol state center left leftReferences
      let rankedRight ← rankRule4bReferences? mol state center right rightReferences
      let first ← compareRawDescriptorBranchesComplete? mol state
        (.rule4b (rankedLeft.getD 0 RS.R) (rankedRight.getD 0 RS.R)) center left right
      if first != Ordering.eq then some first else
        compareRawDescriptorBranchesComplete? mol state
          (.rule4b (rankedLeft.getD 1 RS.S) (rankedRight.getD 1 RS.S)) center left right
  | _, _ => none

/-- Revised Rule-5 result, including whether it is the enantiomorphic `±2` case. -/
structure RawRule5Comparison where
  ordering : Ordering
  pseudo : Bool
  deriving DecidableEq, Repr

/-! ### Occurrence-local auxiliary descriptors

Centres on a cyclic digraph are auxiliary-labelled at each occurrence, not by projecting the
molecule-global descriptor.  Re-rooting flips the existing canonical tree: all four incident edges
at the auxiliary centre are re-ranked, while the edge back toward that temporary root is skipped
below it.  The cursor below is a zipper over the already-cut tree and therefore preserves ring
closure topology without rebuilding an enumeration-dependent second digraph. -/

structure CanonicalRerootCursor where
  node : RawMolecule.CanonicalBranchNode
  previous? : Option RawMolecule.CanonicalBranchNode := none
  deriving DecidableEq, Repr

def canonicalOriginalParent? (node : RawMolecule.CanonicalBranchNode) :
    Option RawMolecule.CanonicalBranchNode :=
  match node.history with
  | _ :: parent :: grandparent :: rest =>
      some { atom := parent, parent := grandparent,
             history := parent :: grandparent :: rest,
             provenance := RawMolecule.CanonicalNodeProvenance.realAtom }
  | _ :: parent :: [] =>
      some { atom := parent, parent := parent, history := [parent],
             provenance := RawMolecule.CanonicalNodeProvenance.realAtom }
  | _ => none

def CanonicalRerootCursor.neighbors (mol : RawMolecule) (cursor : CanonicalRerootCursor) :
    List RawMolecule.CanonicalBranchNode :=
  (canonicalOriginalParent? cursor.node).toList ++ mol.canonicalChildren cursor.node

def CanonicalRerootCursor.children (mol : RawMolecule) (cursor : CanonicalRerootCursor) :
    List CanonicalRerootCursor :=
  if cursor.node.forcedLeaf then [] else
    (cursor.neighbors mol).filterMap fun neighbor =>
      match cursor.previous? with
      | some previous =>
          if neighbor == previous then none
          else some { node := neighbor, previous? := some cursor.node }
      | none => some { node := neighbor, previous? := some cursor.node }

def occurrenceLigandCursors (mol : RawMolecule)
    (occurrence : RawMolecule.CanonicalBranchNode) : List CanonicalRerootCursor :=
  ({ node := occurrence } : CanonicalRerootCursor).children mol

structure CanonicalOccurrenceKey where
  history : List ℕ
  provenance : RawMolecule.CanonicalNodeProvenance
  deriving DecidableEq, Repr

def canonicalOccurrenceKey (node : RawMolecule.CanonicalBranchNode) : CanonicalOccurrenceKey :=
  { history := node.history, provenance := node.provenance }

structure OccurrenceAuxFact where
  key : CanonicalOccurrenceKey
  atom : ℕ
  descriptor : RS
  uppercase : Bool
  priorityPositions : List ℕ := []
  deriving DecidableEq, Repr

abbrev OccurrenceAuxState := List OccurrenceAuxFact

def OccurrenceAuxState.factAt? (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) : Option OccurrenceAuxFact :=
  state.find? fun fact => fact.key == canonicalOccurrenceKey node

def occurrenceNodePriority (state : OccurrenceAuxState) (stage : RawDescriptorRuleStage)
    (leftSide : Bool) (cursor : CanonicalRerootCursor) : ℕ :=
  match cursor.node.provenance, state.factAt? cursor.node with
  | RawMolecule.CanonicalNodeProvenance.realAtom, some fact =>
      match stage with
      | .rule4a => if fact.uppercase then 2 else 1
      | .rule4b leftReference rightReference =>
          let reference := if leftSide then leftReference else rightReference
          if fact.uppercase && fact.descriptor == reference then 1 else 0
      | .rule4c =>
          if fact.uppercase then 0 else if fact.descriptor == RS.R then 2 else 1
      | .rule5 leftReference rightReference =>
          let reference := if leftSide then leftReference else rightReference
          if fact.uppercase && fact.descriptor == reference then 1 else 0
  | _, _ => 0

def insertCursorBy? (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (node : CanonicalRerootCursor) :
    List CanonicalRerootCursor → Option (List CanonicalRerootCursor)
  | [] => some [node]
  | head :: tail =>
      match before node head with
      | none => none
      | some Ordering.gt | some Ordering.eq => some (node :: head :: tail)
      | some Ordering.lt => (insertCursorBy? before node tail).map fun sorted => head :: sorted

def sortCursorsBy? (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    List CanonicalRerootCursor → Option (List CanonicalRerootCursor)
  | [] => some []
  | node :: nodes => do
      let sorted ← sortCursorsBy? before nodes
      insertCursorBy? before node sorted

def rankedCursorChildren? (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (cursor : CanonicalRerootCursor) : Option (List CanonicalRerootCursor) := do
  let children := cursor.children mol
  if 3 < children.length then none else
    let sorted ← sortCursorsBy? before children
    let phantom := mol.canonicalPhantom cursor.node.atom
      (cursor.node.rule1bRootDistance + 1)
    some (sorted ++ List.replicate (3 - sorted.length) { node := phantom })

def cursorTerminal (mol : RawMolecule) (cursor : CanonicalRerootCursor) : Bool :=
  cursor.node.forcedLeaf || (cursor.children mol).isEmpty

def compareCursorPairLabels (mol : RawMolecule) (rule : RawMolecule.CanonicalRuleStage) :
    List (CanonicalRerootCursor × CanonicalRerootCursor) → Option Ordering
  | [] => some Ordering.eq
  | pair :: pairs =>
      match mol.compareCanonicalNodeRule? rule pair.1.node pair.2.node with
      | none => none
      | some Ordering.eq => compareCursorPairLabels mol rule pairs
      | some decision => some decision

def nextCursorPairs? (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    List (CanonicalRerootCursor × CanonicalRerootCursor) →
      Option (List (CanonicalRerootCursor × CanonicalRerootCursor))
  | [] => some []
  | pair :: pairs => do
      let rest ← nextCursorPairs? mol before pairs
      if cursorTerminal mol pair.1 && cursorTerminal mol pair.2 then some rest else
        let left ← rankedCursorChildren? mol before pair.1
        let right ← rankedCursorChildren? mol before pair.2
        some (left.zip right ++ rest)

def compareCursorRule (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (rule : RawMolecule.CanonicalRuleStage) :
    ℕ → List (CanonicalRerootCursor × CanonicalRerootCursor) → Option Ordering
  | 0, pairs =>
      if RawMolecule.defaultBranchWidthCap < pairs.length then none else
        match compareCursorPairLabels mol rule pairs with
        | none => none
        | some Ordering.eq => match nextCursorPairs? mol before pairs with
          | some [] => some Ordering.eq
          | _ => none
        | some decision => some decision
  | fuel + 1, pairs =>
      if RawMolecule.defaultBranchWidthCap < pairs.length then none else
        match compareCursorPairLabels mol rule pairs with
        | none => none
        | some Ordering.eq => match nextCursorPairs? mol before pairs with
          | none => none
          | some [] => some Ordering.eq
          | some next => compareCursorRule mol before rule fuel next
        | some decision => some decision

def compareCursorBranchAt (mol : RawMolecule) :
    ℕ → RawMolecule.CanonicalRuleStage → CanonicalRerootCursor →
      CanonicalRerootCursor → Option Ordering
  | 0, stage, left, right =>
      mol.compareCanonicalNodeThrough? stage left.node right.node
  | fuel + 1, stage, left, right =>
      let before := compareCursorBranchAt mol fuel stage
      let compareRule := fun rule => compareCursorRule mol before rule (fuel + 1) [(left, right)]
      match compareRule RawMolecule.CanonicalRuleStage.rule1a with
      | none => none
      | some Ordering.lt => some Ordering.lt
      | some Ordering.gt => some Ordering.gt
      | some Ordering.eq => match stage with
        | RawMolecule.CanonicalRuleStage.rule1a => some Ordering.eq
        | RawMolecule.CanonicalRuleStage.rule1b =>
            compareRule RawMolecule.CanonicalRuleStage.rule1b
        | RawMolecule.CanonicalRuleStage.rule2 =>
            match compareRule RawMolecule.CanonicalRuleStage.rule1b with
            | some Ordering.eq => compareRule RawMolecule.CanonicalRuleStage.rule2
            | decision => decision

def compareOccurrenceDescriptorPairLabels (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) :
    List (CanonicalRerootCursor × CanonicalRerootCursor) → Ordering
  | [] => Ordering.eq
  | pair :: pairs =>
      match compare (occurrenceNodePriority state stage true pair.1)
          (occurrenceNodePriority state stage false pair.2) with
      | Ordering.eq => compareOccurrenceDescriptorPairLabels state stage pairs
      | decision => decision

structure OccurrenceRule4cDecision where
  ordering : Ordering
  carrier? : Option (CanonicalRerootCursor × OccurrenceAuxFact) := none
  deriving DecidableEq, Repr

def occurrenceRule4cCarrierAt? (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) : Option (CanonicalRerootCursor × OccurrenceAuxFact) :=
  match cursor.node.provenance, state.factAt? cursor.node with
  | RawMolecule.CanonicalNodeProvenance.realAtom, some fact =>
      if fact.uppercase then none else some (cursor, fact)
  | _, _ => none

/-- Rule-4c comparison of one paired sphere, retaining the exact senior descriptor occurrence. -/
def compareOccurrenceRule4cPairLabelsWithWitness (state : OccurrenceAuxState) :
    List (CanonicalRerootCursor × CanonicalRerootCursor) → OccurrenceRule4cDecision
  | [] => { ordering := Ordering.eq }
  | pair :: pairs =>
      let leftPriority := occurrenceNodePriority state .rule4c true pair.1
      let rightPriority := occurrenceNodePriority state .rule4c false pair.2
      match compare leftPriority rightPriority with
      | Ordering.eq => compareOccurrenceRule4cPairLabelsWithWitness state pairs
      | Ordering.gt =>
          { ordering := Ordering.gt, carrier? := occurrenceRule4cCarrierAt? state pair.1 }
      | Ordering.lt =>
          { ordering := Ordering.lt, carrier? := occurrenceRule4cCarrierAt? state pair.2 }

def nextOccurrenceDescriptorPairs? (mol : RawMolecule)
    (beforeLeft beforeRight : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    List (CanonicalRerootCursor × CanonicalRerootCursor) →
      Option (List (CanonicalRerootCursor × CanonicalRerootCursor))
  | [] => some []
  | pair :: pairs => do
      let rest ← nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight pairs
      if cursorTerminal mol pair.1 && cursorTerminal mol pair.2 then some rest else
        let left ← rankedCursorChildren? mol beforeLeft pair.1
        let right ← rankedCursorChildren? mol beforeRight pair.2
        some (left.zip right ++ rest)

def compareOccurrenceDescriptorRule (mol : RawMolecule) (state : OccurrenceAuxState)
    (beforeLeft beforeRight : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (stage : RawDescriptorRuleStage) :
    ℕ → List (CanonicalRerootCursor × CanonicalRerootCursor) → Option Ordering
  | 0, pairs =>
      if RawMolecule.defaultBranchWidthCap < pairs.length then none else
        match compareOccurrenceDescriptorPairLabels state stage pairs with
        | Ordering.eq => match nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight pairs with
          | some [] => some Ordering.eq
          | _ => none
        | decision => some decision
  | fuel + 1, pairs =>
      if RawMolecule.defaultBranchWidthCap < pairs.length then none else
        match compareOccurrenceDescriptorPairLabels state stage pairs with
        | Ordering.eq => match nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight pairs with
          | none => none
          | some [] => some Ordering.eq
          | some next =>
              compareOccurrenceDescriptorRule mol state beforeLeft beforeRight stage fuel next
        | decision => some decision

/-- Apply Rule 4c sphere-by-sphere and return the occurrence that supplied its first decision. -/
def compareOccurrenceRule4cWithWitness (mol : RawMolecule) (state : OccurrenceAuxState)
    (beforeLeft beforeRight : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    ℕ → List (CanonicalRerootCursor × CanonicalRerootCursor) → Option OccurrenceRule4cDecision
  | 0, pairs =>
      if RawMolecule.defaultBranchWidthCap < pairs.length then none else
        match compareOccurrenceRule4cPairLabelsWithWitness state pairs with
        | { ordering := Ordering.eq, .. } =>
            match nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight pairs with
            | some [] => some { ordering := Ordering.eq }
            | _ => none
        | decision => some decision
  | fuel + 1, pairs =>
      if RawMolecule.defaultBranchWidthCap < pairs.length then none else
        match compareOccurrenceRule4cPairLabelsWithWitness state pairs with
        | { ordering := Ordering.eq, .. } =>
            match nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight pairs with
            | none => none
            | some [] => some { ordering := Ordering.eq }
            | some next =>
                compareOccurrenceRule4cWithWitness mol state beforeLeft beforeRight fuel next
        | decision => some decision
def compareOccurrenceDescriptorBranchAt (mol : RawMolecule) (state : OccurrenceAuxState) :
    ℕ → RawDescriptorRuleStage → CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering
  | 0, stage, left, right =>
      match mol.compareCanonicalNodeThrough? RawMolecule.CanonicalRuleStage.rule2
          left.node right.node with
      | none => none
      | some Ordering.eq =>
          match compare (occurrenceNodePriority state .rule4a true left)
              (occurrenceNodePriority state .rule4a false right) with
          | Ordering.eq => match stage with
            | .rule4a => some Ordering.eq
            | .rule4b _ _ | .rule4c | .rule5 _ _ =>
                some (compare (occurrenceNodePriority state stage true left)
                  (occurrenceNodePriority state stage false right))
          | decision => some decision
      | some decision => some decision
  | fuel + 1, stage, left, right =>
      match compareCursorBranchAt mol (fuel + 1) RawMolecule.CanonicalRuleStage.rule2 left right with
      | none => none
      | some Ordering.lt => some Ordering.lt
      | some Ordering.gt => some Ordering.gt
      | some Ordering.eq =>
          let beforeLeft := compareOccurrenceDescriptorBranchAt mol state fuel stage.leftInternal
          let beforeRight := compareOccurrenceDescriptorBranchAt mol state fuel stage.rightInternal
          let compareStage := fun selected =>
            compareOccurrenceDescriptorRule mol state beforeLeft beforeRight selected (fuel + 1)
              [(left, right)]
          match compareStage .rule4a with
          | none => none
          | some Ordering.lt => some Ordering.lt
          | some Ordering.gt => some Ordering.gt
          | some Ordering.eq => match stage with
            | .rule4a => some Ordering.eq
            | .rule4b leftReference rightReference =>
                compareStage (.rule4b leftReference rightReference)
            | .rule4c => compareStage .rule4c
            | .rule5 leftReference rightReference =>
                match compareStage .rule4c with
                | some Ordering.eq => compareStage (.rule5 leftReference rightReference)
                | decision => decision

/-- Descriptor comparison after the caller has already established a constitutional tie between
the two ligand roots.  Re-running the constitutional comparator at that boundary can select a
different pairing of equivalent cyclic children and turn that pairing artifact into a Rule-4/5
decision.  Recursive child ordering still uses the full constitutional-plus-descriptor ranking. -/
def compareOccurrenceDescriptorAtTiedRoot? (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) (stage : RawDescriptorRuleStage)
    (left right : CanonicalRerootCursor) : Option Ordering :=
  let beforeLeft := compareOccurrenceDescriptorBranchAt mol state fuel stage.leftInternal
  let beforeRight := compareOccurrenceDescriptorBranchAt mol state fuel stage.rightInternal
  let compareStage := fun selected =>
    compareOccurrenceDescriptorRule mol state beforeLeft beforeRight selected fuel [(left, right)]
  match compareStage .rule4a with
  | none => none
  | some Ordering.lt => some Ordering.lt
  | some Ordering.gt => some Ordering.gt
  | some Ordering.eq =>
      match stage with
      | .rule4a => some Ordering.eq
      | .rule4b leftReference rightReference =>
          compareStage (.rule4b leftReference rightReference)
      | .rule4c =>
          if state.any fun fact => !fact.uppercase then compareStage .rule4c
          else some Ordering.eq
      | .rule5 leftReference rightReference =>
          let rule4c :=
            if state.any fun fact => !fact.uppercase then compareStage .rule4c
            else some Ordering.eq
          match rule4c with
          | some Ordering.eq => compareStage (.rule5 leftReference rightReference)
          | decision => decision

/-- Rule-4c branch comparison with the exact occurrence-local descriptor carrier. -/
def compareOccurrenceRule4cBranchWithWitness? (mol : RawMolecule) (state : OccurrenceAuxState) :
    ℕ → CanonicalRerootCursor → CanonicalRerootCursor → Option OccurrenceRule4cDecision
  | 0, left, right =>
      match mol.compareCanonicalNodeThrough? RawMolecule.CanonicalRuleStage.rule2
          left.node right.node with
      | none => none
      | some Ordering.lt => some { ordering := Ordering.lt }
      | some Ordering.gt => some { ordering := Ordering.gt }
      | some Ordering.eq =>
          match compare (occurrenceNodePriority state .rule4a true left)
              (occurrenceNodePriority state .rule4a false right) with
          | Ordering.lt => some { ordering := Ordering.lt }
          | Ordering.gt => some { ordering := Ordering.gt }
          | Ordering.eq =>
              some (compareOccurrenceRule4cPairLabelsWithWitness state [(left, right)])
  | fuel + 1, left, right =>
      match compareCursorBranchAt mol (fuel + 1) RawMolecule.CanonicalRuleStage.rule2 left right with
      | none => none
      | some Ordering.lt => some { ordering := Ordering.lt }
      | some Ordering.gt => some { ordering := Ordering.gt }
      | some Ordering.eq =>
          let before := compareOccurrenceDescriptorBranchAt mol state fuel .rule4c
          match compareOccurrenceDescriptorRule mol state before before .rule4a (fuel + 1)
              [(left, right)] with
          | none => none
          | some Ordering.lt => some { ordering := Ordering.lt }
          | some Ordering.gt => some { ordering := Ordering.gt }
          | some Ordering.eq =>
              compareOccurrenceRule4cWithWitness mol state before before (fuel + 1)
                [(left, right)]

def occurrenceRule4bReferences (mol : RawMolecule) (state : OccurrenceAuxState) :
    ℕ → List CanonicalRerootCursor → List RS
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, frontier =>
      let senses := frontier.filterMap fun cursor =>
        match cursor.node.provenance, state.factAt? cursor.node with
        | RawMolecule.CanonicalNodeProvenance.realAtom, some fact =>
            if fact.uppercase then some fact.descriptor else none
        | _, _ => none
      let rCount := (senses.filter fun sense => sense == RS.R).length
      let sCount := (senses.filter fun sense => sense == RS.S).length
      if rCount + sCount != 0 then
        if sCount < rCount then [RS.R]
        else if rCount < sCount then [RS.S]
        else [RS.R, RS.S]
      else occurrenceRule4bReferences mol state fuel
        (frontier.flatMap fun cursor => cursor.children mol)

def rankOccurrenceRule4bReferences? (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) (root : CanonicalRerootCursor) : List RS → Option (List RS)
  | [first, second] => do
      let decision ← compareOccurrenceDescriptorAtTiedRoot? mol state fuel (.rule4b first second)
        root root
      if decision == Ordering.lt then some [second, first] else some [first, second]
  | references => some references

def compareOccurrenceRule4b? (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    (left right : CanonicalRerootCursor) : Option Ordering :=
  let leftReferences := occurrenceRule4bReferences mol state fuel [left]
  let rightReferences := occurrenceRule4bReferences mol state fuel [right]
  match leftReferences, rightReferences with
  | [], [] => some Ordering.eq
  -- IUPAC P-92.5.2.1 criterion (c)(i): one reference descriptor has priority over two.
  | [_], [_, _] => some Ordering.gt
  | [_, _], [_] => some Ordering.lt
  | [leftReference], [rightReference] =>
      compareOccurrenceDescriptorAtTiedRoot? mol state fuel
        (.rule4b leftReference rightReference) left right
  | [_, _], [_, _] => do
      let rankedLeft ← rankOccurrenceRule4bReferences? mol state fuel left leftReferences
      let rankedRight ← rankOccurrenceRule4bReferences? mol state fuel right rightReferences
      let first ← compareOccurrenceDescriptorAtTiedRoot? mol state fuel
        (.rule4b (rankedLeft.getD 0 RS.R) (rankedRight.getD 0 RS.R)) left right
      if first != Ordering.eq then some first else
        compareOccurrenceDescriptorAtTiedRoot? mol state fuel
          (.rule4b (rankedLeft.getD 1 RS.S) (rankedRight.getD 1 RS.S)) left right
  | _, _ => none

def compareOccurrenceRule5? (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    (left right : CanonicalRerootCursor) : Option RawRule5Comparison := do
  let cmpR ← compareOccurrenceDescriptorAtTiedRoot? mol state fuel (.rule5 RS.R RS.R) left right
  let cmpS ← compareOccurrenceDescriptorAtTiedRoot? mol state fuel (.rule5 RS.S RS.S) left right
  match cmpR with
  | Ordering.lt => some { ordering := Ordering.lt, pseudo := cmpS != Ordering.lt }
  | Ordering.gt => some { ordering := Ordering.gt, pseudo := cmpS != Ordering.gt }
  | Ordering.eq => some { ordering := Ordering.eq, pseudo := false }

structure OccurrenceComparison where
  ordering : Ordering
  pseudo : Bool := false
  rule4cCarrier? : Option (CanonicalRerootCursor × OccurrenceAuxFact) := none
  deriving DecidableEq, Repr

/-- Detect the legacy condition that would have overridden a non-tied constitutional comparison
using a pairwise atom-automorphism query.  Production now treats this condition as a conflict and
fails closed: reroot cursors carry histories that an atom-level automorphism alone does not prove
interchangeable. -/
def occurrenceRootsProvedAutomorphic (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor) (compiledConstitutional : Ordering) : Bool :=
  compiledConstitutional != Ordering.eq &&
    mol.atomLiesInCycle fuel left.node.atom && mol.atomLiesInCycle fuel right.node.atom &&
    match left.previous?, right.previous? with
    | some leftRoot, some rightRoot =>
        leftRoot == rightRoot &&
          left.node.provenance == RawMolecule.CanonicalNodeProvenance.realAtom &&
          right.node.provenance == RawMolecule.CanonicalNodeProvenance.realAtom &&
          (({ node := leftRoot } : CanonicalRerootCursor).neighbors mol).contains left.node &&
          (({ node := leftRoot } : CanonicalRerootCursor).neighbors mol).contains right.node &&
          !mol.atomLiesInCycle fuel leftRoot.atom &&
          mol.hasConstitutionAutomorphismSwapping leftRoot.atom left.node.atom right.node.atom
    | _, _ => false

/-- When the disputed pairwise query is accepted, both cursors carry one exact incoming reference
node rather than merely two nodes whose legacy occurrence keys collide. -/
theorem occurrenceRootsProvedAutomorphic_common_reference_frame
    (mol : RawMolecule) (fuel : ℕ) (left right : CanonicalRerootCursor)
    (compiledConstitutional : Ordering)
    (accepted : occurrenceRootsProvedAutomorphic mol fuel left right
      compiledConstitutional = true) :
    ∃ root, left.previous? = some root ∧ right.previous? = some root := by
  unfold occurrenceRootsProvedAutomorphic at accepted
  cases leftEq : left.previous? with
  | none => simp [leftEq] at accepted
  | some leftRoot =>
      cases rightEq : right.previous? with
      | none => simp [leftEq, rightEq] at accepted
      | some rightRoot =>
          have rootEq : leftRoot = rightRoot := by
            simp only [leftEq, rightEq, Bool.and_eq_true, beq_iff_eq] at accepted
            exact accepted.2.1.1.1.1.1.1
          subst rightRoot
          exact ⟨leftRoot, rfl, rfl⟩

/-- The shared incoming node is not merely equal on both sides: both compared nodes must be exact
members of the canonical neighbor family generated from it.  This rejects forged histories and
provenances which happen to carry physically incident atom numbers. -/
theorem occurrenceRootsProvedAutomorphic_common_generated_reference_frame
    (mol : RawMolecule) (fuel : ℕ) (left right : CanonicalRerootCursor)
    (compiledConstitutional : Ordering)
    (accepted : occurrenceRootsProvedAutomorphic mol fuel left right
      compiledConstitutional = true) :
    ∃ root,
      left.previous? = some root ∧ right.previous? = some root ∧
      left.node ∈ (({ node := root } : CanonicalRerootCursor).neighbors mol) ∧
      right.node ∈ (({ node := root } : CanonicalRerootCursor).neighbors mol) := by
  unfold occurrenceRootsProvedAutomorphic at accepted
  cases leftEq : left.previous? with
  | none => simp [leftEq] at accepted
  | some leftRoot =>
      cases rightEq : right.previous? with
      | none => simp [leftEq, rightEq] at accepted
      | some rightRoot =>
          simp only [leftEq, rightEq, Bool.and_eq_true, beq_iff_eq] at accepted
          have rootEq : leftRoot = rightRoot := accepted.2.1.1.1.1.1.1
          have leftMember := List.contains_iff_mem.mp accepted.2.1.1.1.2
          have rightMember := List.contains_iff_mem.mp accepted.2.1.1.2
          subst rightRoot
          exact ⟨leftRoot, rfl, rfl, leftMember, rightMember⟩

/-- The atom-level automorphism query is admitted only for physical real-atom ligand nodes.
Canonical multiple-bond/ring duplicates are exact generated neighbors too, but the atom query does
not certify their occurrence provenance. -/
theorem occurrenceRootsProvedAutomorphic_real_nodes
    (mol : RawMolecule) (fuel : ℕ) (left right : CanonicalRerootCursor)
    (compiledConstitutional : Ordering)
    (accepted : occurrenceRootsProvedAutomorphic mol fuel left right
      compiledConstitutional = true) :
    left.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
      right.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom := by
  unfold occurrenceRootsProvedAutomorphic at accepted
  cases leftEq : left.previous? with
  | none => simp [leftEq] at accepted
  | some leftRoot =>
      cases rightEq : right.previous? with
      | none => simp [leftEq, rightEq] at accepted
      | some rightRoot =>
          simp only [leftEq, rightEq, Bool.and_eq_true, beq_iff_eq] at accepted
          exact ⟨accepted.2.1.1.1.1.1.2, accepted.2.1.1.1.1.2⟩

/-- Distinct incoming cursor frames can never trigger the constitutional conflict gate, even when
their history/provenance occurrence keys collide. -/
theorem occurrenceRootsProvedAutomorphic_eq_false_of_previous_ne
    (mol : RawMolecule) (fuel : ℕ) (left right : CanonicalRerootCursor)
    (compiledConstitutional : Ordering) (different : left.previous? ≠ right.previous?) :
    occurrenceRootsProvedAutomorphic mol fuel left right compiledConstitutional = false := by
  cases gateEq : occurrenceRootsProvedAutomorphic mol fuel left right compiledConstitutional with
  | false => rfl
  | true =>
      exfalso
      rcases occurrenceRootsProvedAutomorphic_common_reference_frame mol fuel left right
        compiledConstitutional gateEq with ⟨root, leftEq, rightEq⟩
      exact different (leftEq.trans rightEq.symm)

/-- Conservative constitutional stage.  It returns the raw Rule-2 result unless the legacy
pairwise automorphism gate conflicts with that result; conflicts are withheld rather than being
converted to an unproved tie.  Thus every successful result remains the comparison of the two
actual reroot cursors. -/
def certifiedConstitutionalStage? (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor) : Option Ordering := do
  let constitutional ←
    compareCursorBranchAt mol fuel RawMolecule.CanonicalRuleStage.rule2 left right
  if occurrenceRootsProvedAutomorphic mol fuel left right constitutional then none
  else some constitutional

def compareOccurrenceBranches? (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    (left right : CanonicalRerootCursor) : Option OccurrenceComparison := do
  let constitutional ← certifiedConstitutionalStage? mol fuel left right
  if constitutional != Ordering.eq then return { ordering := constitutional }
  let rule4a ← compareOccurrenceDescriptorAtTiedRoot? mol state fuel .rule4a left right
  if rule4a != Ordering.eq then return { ordering := rule4a }
  let rule4b ← compareOccurrenceRule4b? mol state fuel left right
  if rule4b != Ordering.eq then return { ordering := rule4b }
  let rule4c ←
    if state.any fun fact => !fact.uppercase then
      let before := compareOccurrenceDescriptorBranchAt mol state fuel .rule4c
      compareOccurrenceRule4cWithWitness mol state before before fuel [(left, right)]
    else some { ordering := Ordering.eq }
  if rule4c.ordering != Ordering.eq then
    -- Rule 4c establishes ordinary priority between unlike pseudoasymmetric descriptors.  The
    -- root is not thereby pseudoasymmetric: lowercase is introduced only by an enantiomorphic
    -- Rule-5 comparison.  Retain the carrier as evidence, but do not count it as a `±2` decision.
    return { ordering := rule4c.ordering, rule4cCarrier? := rule4c.carrier? }
  let rule5 ← compareOccurrenceRule5? mol state fuel left right
  some { ordering := rule5.ordering, pseudo := rule5.pseudo }

def insertOccurrenceTracked (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    (candidate : CanonicalRerootCursor) :
    List CanonicalRerootCursor → Option (List CanonicalRerootCursor × ℕ)
  | [] => some ([candidate], 0)
  | head :: tail => do
      let decision ← compareOccurrenceBranches? mol state fuel candidate head
      let observed := if decision.pseudo then 1 else 0
      if decision.ordering == Ordering.lt then
        let inserted ← insertOccurrenceTracked mol state fuel candidate tail
        some (head :: inserted.1, observed + inserted.2)
      else
        some (candidate :: head :: tail, observed)

def sortOccurrencesTracked? (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ) :
    List CanonicalRerootCursor → Option (List CanonicalRerootCursor × ℕ)
  | [] => some ([], 0)
  | cursor :: cursors => do
      let sorted ← sortOccurrencesTracked? mol state fuel cursors
      let inserted ← insertOccurrenceTracked mol state fuel cursor sorted.1
      some (inserted.1, sorted.2 + inserted.2)

/-- Complete four-ligand occurrence frame.  A production lone pair is represented by the same
`atomCount` phantom used by `ligandsWithLonePair`; every cursor retains the incoming occurrence as
its `previous?` reference frame. -/
def occurrenceLigandFrame? (mol : RawMolecule)
    (node : RawMolecule.CanonicalBranchNode) : Option (List CanonicalRerootCursor) :=
  let ligands := mol.ligandsWithLonePair node.atom
  if ligands.length != 4 then none else
  let physical := occurrenceLigandCursors mol node
  if physical.length == 4 then some physical
  else if physical.length == 3 && ligands.contains mol.atomCount then
    some (physical ++
      [{ node := mol.canonicalPhantom node.atom (node.depth + 1)
         previous? := some node }])
  else none

/-- One adjacent comparison actually consumed by the occurrence ranking. -/
structure OccurrenceComparedPair (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    where
  left : CanonicalRerootCursor
  right : CanonicalRerootCursor
  decision : OccurrenceComparison

/-- Structural adjacent traversal used by production `occurrenceFact?`.  Retaining cursor pairs
connects every final ranking decision to the exact Rules 4b and 5 calls inside
`compareOccurrenceBranches?`. -/
def compareOccurrenceAdjacentPairs? (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ) :
    List CanonicalRerootCursor → Option (List (OccurrenceComparedPair mol state fuel))
  | [] | [_] => some []
  | left :: right :: remaining => do
      let decision ← compareOccurrenceBranches? mol state fuel left right
      let deeper ← compareOccurrenceAdjacentPairs? mol state fuel (right :: remaining)
      some ({ left := left, right := right, decision := decision } :: deeper)

/-- Every retained adjacent decision is the literal production comparison at those two framed
cursors. -/
theorem compareOccurrenceAdjacentPairs?_sound (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (sorted : List CanonicalRerootCursor)
    (compared : List (OccurrenceComparedPair mol state fuel))
    (computed : compareOccurrenceAdjacentPairs? mol state fuel sorted = some compared) :
    ∀ comparison, comparison ∈ compared →
      compareOccurrenceBranches? mol state fuel comparison.left comparison.right =
        some comparison.decision := by
  induction sorted generalizing compared with
  | nil =>
      simp [compareOccurrenceAdjacentPairs?] at computed
      subst compared
      simp
  | cons left tail inductionHypothesis =>
      cases tail with
      | nil =>
          simp [compareOccurrenceAdjacentPairs?] at computed
          subst compared
          simp
      | cons right remaining =>
          simp only [compareOccurrenceAdjacentPairs?] at computed
          cases comparisonEq : compareOccurrenceBranches? mol state fuel left right with
          | none => simp [comparisonEq] at computed
          | some decision =>
              cases deeperEq : compareOccurrenceAdjacentPairs? mol state fuel
                (right :: remaining) with
              | none => simp [deeperEq] at computed
              | some deeper =>
                  simp [comparisonEq, deeperEq] at computed
                  subst compared
                  intro comparison member
                  rcases List.mem_cons.mp member with head | tailMember
                  · subst comparison
                    exact comparisonEq
                  · exact inductionHypothesis deeper deeperEq comparison tailMember

/- Conservative generated-real-tree runtime. Discovery coordinates remain unchanged. -/
namespace FrameRuntime

open RawMolecule

abbrev Profile := CanonicalTreeProfile.Profile

inductive Cursor where
  | actual (original : CanonicalRerootCursor)
  | padding (parent : Cursor)
  deriving DecidableEq, Repr

/-- Original production padding is recomputed exactly from its retained original parent. -/
def Cursor.original (mol : RawMolecule) : Cursor → CanonicalRerootCursor
  | .actual cursor => cursor
  | .padding parent =>
      { node := mol.canonicalPhantom (parent.original mol).node.atom
          ((parent.original mol).node.rule1bRootDistance + 1) }

/-- Shared executable collector; original discovery history and caller protocols are unchanged. -/
abbrev collect := CanonicalTreeProfile.collect

/-- The runtime observes the accepted shared profile definition directly. -/
abbrev profile? := CanonicalTreeProfile.profile?

def cursor? (mol : RawMolecule) (profile : Profile) : Cursor → Option Nat
  | .actual cursor =>
      if !profile.generated.contains cursor.node then none else
      if !(cursor.previous?.all fun previous =>
          profile.generated.contains previous && (cursor.neighbors mol).contains previous)
        then none else
      CanonicalComparisonFrame.observeNode profile.frame cursor.node
  | .padding parent => (cursor? mol profile parent).map (fun distance => distance + 1)

def terminal (mol : RawMolecule) (cursor : Cursor) : Bool := cursorTerminal mol (cursor.original mol)

def label? (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (rule : CanonicalRuleStage) (left right : Cursor) : Option Ordering := do
  let ld ← cursor? mol profile left
  let rd ← cursor? mol profile right
  match rule with
  | .rule1b => some (if ld < rd then .gt else if rd < ld then .lt else .eq)
  | _ =>
      if authoritative then
        mol.compareCanonicalNodeRuleAuthoritative? rule (left.original mol).node (right.original mol).node
      else mol.compareCanonicalNodeRule? rule (left.original mol).node (right.original mol).node

def insert? (before : Cursor → Cursor → Option Ordering) (candidate : Cursor) :
    List Cursor → Option (List Cursor)
  | [] => some [candidate]
  | head :: tail => do
      let cmp ← before candidate head
      if cmp == .lt then (insert? before candidate tail).map (head :: ·)
      else some (candidate :: head :: tail)

def sort? (before : Cursor → Cursor → Option Ordering) : List Cursor → Option (List Cursor)
  | [] => some []
  | head :: tail => do
      let sorted ← sort? before tail
      insert? before head sorted

def ranked? (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (before : Cursor → Cursor → Option Ordering) (parent : Cursor) : Option (List Cursor) := do
  let _ ← cursor? mol profile parent
  let children := ((parent.original mol).children mol).map Cursor.actual
  let slots := if authoritative then authoritativeChildSlots else 3
  if slots < children.length then none else
  let _ ← children.mapM (cursor? mol profile)
  let sorted ← sort? before children
  let phantom : Cursor := .padding parent
  some (sorted ++ List.replicate (slots - sorted.length) phantom)

def pairLabels? (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (rule : CanonicalRuleStage) : List (Cursor × Cursor) → Option Ordering
  | [] => some .eq
  | (left, right) :: pairs => do
      let cmp ← label? mol profile authoritative rule left right
      if cmp == .eq then pairLabels? mol profile authoritative rule pairs else some cmp

def nextPairs? (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (before : Cursor → Cursor → Option Ordering) :
    List (Cursor × Cursor) → Option (List (Cursor × Cursor))
  | [] => some []
  | (left, right) :: pairs => do
      let rest ← nextPairs? mol profile authoritative before pairs
      if terminal mol left && terminal mol right then some rest else
      let lc ← ranked? mol profile authoritative before left
      let rc ← ranked? mol profile authoritative before right
      some (lc.zip rc ++ rest)

def compareRule? (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (before : Cursor → Cursor → Option Ordering) (rule : CanonicalRuleStage) :
    Nat → List (Cursor × Cursor) → Option Ordering
  | fuel, pairs =>
      if !authoritative && defaultBranchWidthCap < pairs.length then none else do
      let cmp ← pairLabels? mol profile authoritative rule pairs
      if cmp != .eq then some cmp else
      let next ← nextPairs? mol profile authoritative before pairs
      if next.isEmpty then some .eq else
      match fuel with
      | 0 => none
      | fuel + 1 => compareRule? mol profile authoritative before rule fuel next

def throughLabels? (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (stage : CanonicalRuleStage) (left right : Cursor) : Option Ordering := do
  let first ← label? mol profile authoritative .rule1a left right
  if first != .eq || stage == .rule1a then some first else
  let distance ← label? mol profile authoritative .rule1b left right
  if distance != .eq || stage == .rule1b then some distance else
  label? mol profile authoritative .rule2 left right

/-- Both zero fuel and every recursive sphere read the same center-owned profile. -/
def compareBranch? (mol : RawMolecule) (profile : Profile) (authoritative : Bool) :
    Nat → CanonicalRuleStage → Cursor → Cursor → Option Ordering
  | 0, stage, left, right => do
      let cmp ← throughLabels? mol profile authoritative stage left right
      if cmp == .eq && !(terminal mol left && terminal mol right) then none else some cmp
  | fuel + 1, stage, left, right => do
      let before := compareBranch? mol profile authoritative fuel stage
      let first ← compareRule? mol profile authoritative before .rule1a (fuel + 1) [(left,right)]
      if first != .eq || stage == .rule1a then some first else
      let distance ← compareRule? mol profile authoritative before .rule1b (fuel + 1) [(left,right)]
      if distance != .eq || stage == .rule1b then some distance else
      compareRule? mol profile authoritative before .rule2 (fuel + 1) [(left,right)]

/-! ### Shared-profile validation helpers -/

/-- Validate every cursor of a frontier against the shared profile; `none` on any refusal. -/
def validateCursors? (mol : RawMolecule) (profile : Profile) :
    List Cursor → Option (List Cursor)
  | [] => some []
  | cursor :: rest => do
      let _ ← cursor? mol profile cursor
      let rest ← validateCursors? mol profile rest
      some (cursor :: rest)

/-- Validate every cursor of both sides of a paired sphere before any projection. -/
def validatePairs? (mol : RawMolecule) (profile : Profile) :
    List (Cursor × Cursor) → Option (List (Cursor × Cursor))
  | [] => some []
  | (left, right) :: pairs => do
      let _ ← cursor? mol profile left
      let _ ← cursor? mol profile right
      let rest ← validatePairs? mol profile pairs
      some ((left, right) :: rest)

/-! ### Framed descriptor pair labels, expansion, and exhaustive rules -/

/-- Pure node-local descriptor priority comparison of one paired sphere.  Callers must validate
the cursors first; `compareDescriptorPairLabels?` is the checked entry point. -/
def compareDescriptorPairLabels (mol : RawMolecule) (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) :
    List (Cursor × Cursor) → Ordering
  | [] => Ordering.eq
  | pair :: pairs =>
      match compare (occurrenceNodePriority state stage true (pair.1.original mol))
          (occurrenceNodePriority state stage false (pair.2.original mol)) with
      | Ordering.eq => compareDescriptorPairLabels mol state stage pairs
      | decision => decision

/-- Pure Rule-4c witness projection of one paired sphere.  Callers must validate first. -/
def compareRule4cPairLabelsWithWitness (mol : RawMolecule) (state : OccurrenceAuxState) :
    List (Cursor × Cursor) → OccurrenceRule4cDecision
  | [] => { ordering := Ordering.eq }
  | pair :: pairs =>
      let leftPriority := occurrenceNodePriority state .rule4c true (pair.1.original mol)
      let rightPriority := occurrenceNodePriority state .rule4c false (pair.2.original mol)
      match compare leftPriority rightPriority with
      | Ordering.eq => compareRule4cPairLabelsWithWitness mol state pairs
      | Ordering.gt =>
          { ordering := Ordering.gt, carrier? := occurrenceRule4cCarrierAt? state (pair.1.original mol) }
      | Ordering.lt =>
          { ordering := Ordering.lt, carrier? := occurrenceRule4cCarrierAt? state (pair.2.original mol) }

/-- Checked descriptor pair-label comparison: validates the whole sphere before projecting. -/
def compareDescriptorPairLabels? (mol : RawMolecule) (profile : Profile)
    (state : OccurrenceAuxState) (stage : RawDescriptorRuleStage) :
    List (Cursor × Cursor) → Option Ordering :=
  fun pairs => do
    let _ ← validatePairs? mol profile pairs
    some (compareDescriptorPairLabels mol state stage pairs)

/-- Checked Rule-4c witness projection: validates the whole sphere before projecting. -/
def compareRule4cPairLabelsWithWitness? (mol : RawMolecule) (profile : Profile)
    (state : OccurrenceAuxState) :
    List (Cursor × Cursor) → Option OccurrenceRule4cDecision :=
  fun pairs => do
    let _ ← validatePairs? mol profile pairs
    some (compareRule4cPairLabelsWithWitness mol state pairs)

/-- Expand paired descriptor cursors with independently refined sibling orders on the two sides.
Each cursor is validated before its terminal/empty-success short-circuit; padding remains
terminal and is never flattened and re-expanded. -/
def nextDescriptorPairs? (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering) :
    List (Cursor × Cursor) → Option (List (Cursor × Cursor))
  | [] => some []
  | pair :: pairs => do
      let _ ← cursor? mol profile pair.1
      let _ ← cursor? mol profile pair.2
      let rest ← nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs
      if terminal mol pair.1 && terminal mol pair.2 then some rest else
        let left ← ranked? mol profile authoritative beforeLeft pair.1
        let right ← ranked? mol profile authoritative beforeRight pair.2
        some (left.zip right ++ rest)

/-- Apply one descriptor rule exhaustively, sphere before sphere, validating every sphere.  The
fast mode honours `defaultBranchWidthCap`; the authoritative mode does not. -/
def compareDescriptorRule? (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering)
    (stage : RawDescriptorRuleStage) :
    Nat → List (Cursor × Cursor) → Option Ordering
  | 0, pairs =>
      if !authoritative && defaultBranchWidthCap < pairs.length then none else do
        let cmp ← compareDescriptorPairLabels? mol profile state stage pairs
        if cmp != .eq then some cmp else
        let next ← nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs
        if next.isEmpty then some .eq else none
  | fuel + 1, pairs =>
      if !authoritative && defaultBranchWidthCap < pairs.length then none else do
        let cmp ← compareDescriptorPairLabels? mol profile state stage pairs
        if cmp != .eq then some cmp else
        let next ← nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs
        if next.isEmpty then some .eq else
          compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight stage fuel next

/-- Apply Rule 4c sphere-by-sphere, validating every sphere, and return the occurrence that
supplied its first decision. -/
def compareRule4cWithWitness? (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering) :
    Nat → List (Cursor × Cursor) → Option OccurrenceRule4cDecision
  | 0, pairs =>
      if !authoritative && defaultBranchWidthCap < pairs.length then none else do
        let decision ← compareRule4cPairLabelsWithWitness? mol profile state pairs
        if decision.ordering != .eq then some decision else
        let next ← nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs
        if next.isEmpty then some { ordering := .eq } else none
  | fuel + 1, pairs =>
      if !authoritative && defaultBranchWidthCap < pairs.length then none else do
        let decision ← compareRule4cPairLabelsWithWitness? mol profile state pairs
        if decision.ordering != .eq then some decision else
        let next ← nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs
        if next.isEmpty then some { ordering := .eq } else
          compareRule4cWithWitness? mol profile authoritative state beforeLeft beforeRight fuel next

/-! ### Framed recursively-refined descriptor branch comparison -/

/-- The fuel-0 descriptor tie after a constitutional rule-2 equality: compare the Rule-4a priority
first, then (for a non-`rule4a` stage) the stage-specific priority.  The caller has already
validated `left`/`right` via `compareBranch?`. -/
def descriptorNodeTie (mol : RawMolecule) (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) (left right : Cursor) : Option Ordering :=
  match compare (occurrenceNodePriority state .rule4a true (left.original mol))
      (occurrenceNodePriority state .rule4a false (right.original mol)) with
  | Ordering.eq =>
      match stage with
      | .rule4a => some Ordering.eq
      | .rule4b _ _ | .rule4c | .rule5 _ _ =>
          some (compare (occurrenceNodePriority state stage true (left.original mol))
            (occurrenceNodePriority state stage false (right.original mol)))
  | decision => some decision

/-- Recursively refined constitutional-plus-descriptor branch comparison on the shared profile.
The constitutional recursion is `compareBranch?` (which validates every cursor); child ranking is
`compareDescriptorRule?` with side-specific `.leftInternal` / `.rightInternal` callbacks. -/
def compareDescriptorBranchAt? (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) :
    Nat → RawDescriptorRuleStage → Cursor → Cursor → Option Ordering
  | 0, stage, left, right => do
      let constitutional ← compareBranch? mol profile authoritative 0 .rule2 left right
      match constitutional with
      | Ordering.eq => descriptorNodeTie mol state stage left right
      | decision => some decision
  | fuel + 1, stage, left, right => do
      let constitutional ← compareBranch? mol profile authoritative (fuel + 1) .rule2 left right
      match constitutional with
      | Ordering.lt => some Ordering.lt
      | Ordering.gt => some Ordering.gt
      | Ordering.eq =>
          let beforeLeft :=
            compareDescriptorBranchAt? mol profile authoritative state fuel stage.leftInternal
          let beforeRight :=
            compareDescriptorBranchAt? mol profile authoritative state fuel stage.rightInternal
          let compareStage := fun selected =>
            compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight selected
              (fuel + 1) [(left, right)]
          match compareStage .rule4a with
          | none => none
          | some Ordering.lt => some Ordering.lt
          | some Ordering.gt => some Ordering.gt
          | some Ordering.eq =>
              match stage with
              | .rule4a => some Ordering.eq
              | .rule4b leftReference rightReference =>
                  compareStage (.rule4b leftReference rightReference)
              | .rule4c => compareStage .rule4c
              | .rule5 leftReference rightReference =>
                  match compareStage .rule4c with
                  | some Ordering.eq => compareStage (.rule5 leftReference rightReference)
                  | decision => decision

/-- Descriptor comparison after the caller has already established a constitutional tie between the
two ligand roots; the redundant constitutional root comparison is skipped.  Recursive child ordering
still uses the full constitutional-plus-descriptor ranking. -/
def compareDescriptorAtTiedRoot? (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (stage : RawDescriptorRuleStage)
    (left right : Cursor) : Option Ordering :=
  let beforeLeft :=
    compareDescriptorBranchAt? mol profile authoritative state fuel stage.leftInternal
  let beforeRight :=
    compareDescriptorBranchAt? mol profile authoritative state fuel stage.rightInternal
  let compareStage := fun selected =>
    compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight selected fuel
      [(left, right)]
  match compareStage .rule4a with
  | none => none
  | some Ordering.lt => some Ordering.lt
  | some Ordering.gt => some Ordering.gt
  | some Ordering.eq =>
      match stage with
      | .rule4a => some Ordering.eq
      | .rule4b leftReference rightReference =>
          compareStage (.rule4b leftReference rightReference)
      | .rule4c =>
          if state.any (fun fact => !fact.uppercase) then compareStage .rule4c else some Ordering.eq
      | .rule5 leftReference rightReference =>
          let rule4c :=
            if state.any (fun fact => !fact.uppercase) then compareStage .rule4c else some Ordering.eq
          match rule4c with
          | some Ordering.eq => compareStage (.rule5 leftReference rightReference)
          | decision => decision

/-! ### Rule-4b references, Rule 4b, and Rule 5 -/

/-- Profile-validated descendants for the Rule-4b reference BFS.  Padding is terminal (no
descendants); an actual cursor contributes its reroot children, each validated by `cursor?`. -/
def rule4bDescendants? (mol : RawMolecule) (profile : Profile) :
    List Cursor → Option (List Cursor)
  | [] => some []
  | cursor :: rest => do
      let rest ← rule4bDescendants? mol profile rest
      match cursor with
      | .padding _ => some rest
      | .actual c => do
          let children := (c.children mol).map Cursor.actual
          let _ ← validateCursors? mol profile children
          some (children ++ rest)

/-- Shared-profile Rule-4b reference collection as an Option BFS.  Every frontier layer is validated
before consuming `state.factAt?`; generated child cursors and incidence are checked by `cursor?`;
padding stays terminal; multiplicity, the first uppercase-bearing sphere, mode-independent
reference counts, and fuel-zero semantics are all preserved. -/
def rule4bReferences? (mol : RawMolecule) (profile : Profile) (state : OccurrenceAuxState) :
    Nat → List Cursor → Option (List RS)
  | 0, _ => some []
  | _ + 1, [] => some []
  | fuel + 1, frontier => do
      let _ ← validateCursors? mol profile frontier
      let senses := frontier.filterMap fun cursor =>
        match (cursor.original mol).node.provenance, state.factAt? (cursor.original mol).node with
        | RawMolecule.CanonicalNodeProvenance.realAtom, some fact =>
            if fact.uppercase then some fact.descriptor else none
        | _, _ => none
      let rCount := (senses.filter fun sense => sense == RS.R).length
      let sCount := (senses.filter fun sense => sense == RS.S).length
      if rCount + sCount != 0 then
        some (if sCount < rCount then [RS.R] else if rCount < sCount then [RS.S] else [RS.R, RS.S])
      else do
        let children ← rule4bDescendants? mol profile frontier
        rule4bReferences? mol profile state fuel children

/-- Sort the two criterion-(c) reference lists for one ligand by their complete pair pattern. -/
def rankRule4bReferences? (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (root : Cursor) : List RS → Option (List RS)
  | [first, second] => do
      let decision ← compareDescriptorAtTiedRoot? mol profile authoritative state fuel
        (.rule4b first second) root root
      if decision == Ordering.lt then some [second, first] else some [first, second]
  | references => some references

/-- Dynamic Rule-4b comparison for both single-reference criterion (b) and two-list criterion (c).
The `authoritative` flag selects the mixed empty/nonempty shape policy: unrestricted ordering for
authoritative, conservative refusal for fast. -/
def compareRule4b? (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : Cursor) : Option Ordering := do
  let leftReferences ← rule4bReferences? mol profile state fuel [left]
  let rightReferences ← rule4bReferences? mol profile state fuel [right]
  match leftReferences, rightReferences with
  | [], [] => some Ordering.eq
  -- IUPAC P-92.5.2.1 criterion (c)(i): one reference descriptor has priority over two.
  | [], [_] | [], [_, _] => if authoritative then some Ordering.lt else none
  | [_], [] | [_, _], [] => if authoritative then some Ordering.gt else none
  | [_], [_, _] => some Ordering.gt
  | [_, _], [_] => some Ordering.lt
  | [leftReference], [rightReference] =>
      compareDescriptorAtTiedRoot? mol profile authoritative state fuel
        (.rule4b leftReference rightReference) left right
  | [_, _], [_, _] => do
      let rankedLeft ← rankRule4bReferences? mol profile authoritative state fuel left leftReferences
      let rankedRight ← rankRule4bReferences? mol profile authoritative state fuel right rightReferences
      let first ← compareDescriptorAtTiedRoot? mol profile authoritative state fuel
        (.rule4b (rankedLeft.getD 0 RS.R) (rankedRight.getD 0 RS.R)) left right
      if first != Ordering.eq then some first else
        compareDescriptorAtTiedRoot? mol profile authoritative state fuel
          (.rule4b (rankedLeft.getD 1 RS.S) (rankedRight.getD 1 RS.S)) left right
  | _, _ => none

/-- Revised Rule-5 result, including whether it is the enantiomorphic `±2` case. -/
def compareRule5? (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : Cursor) : Option RawRule5Comparison := do
  let cmpR ← compareDescriptorAtTiedRoot? mol profile authoritative state fuel
    (.rule5 RS.R RS.R) left right
  let cmpS ← compareDescriptorAtTiedRoot? mol profile authoritative state fuel
    (.rule5 RS.S RS.S) left right
  match cmpR with
  | Ordering.lt => some { ordering := Ordering.lt, pseudo := cmpS != Ordering.lt }
  | Ordering.gt => some { ordering := Ordering.gt, pseudo := cmpS != Ordering.gt }
  | Ordering.eq => some { ordering := Ordering.eq, pseudo := false }

/-! ### Complete decision -/

/-- Complete Rules 1a--5 comparison of two descriptor-bearing occurrences, threading the single
center-owned profile through every recursive constitutional comparison and descriptor child sort.

The constitutional stage is the shared-profile `compareBranch?` Rule-2 result directly: no
automorphism gate, so strict results and empty-state ties are preserved unconditionally.  A
*nonempty* constitutional tie runs the full framed descriptor pipeline. -/
def decisionComplete? (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : CanonicalRerootCursor) :
    Option OccurrenceComparison := do
  let constitutional ← compareBranch? mol profile authoritative fuel .rule2 (.actual left) (.actual right)
  if constitutional != Ordering.eq then return { ordering := constitutional }
  if state.isEmpty then return { ordering := Ordering.eq }
  let rule4a ← compareDescriptorAtTiedRoot? mol profile authoritative state fuel .rule4a
    (.actual left) (.actual right)
  if rule4a != Ordering.eq then return { ordering := rule4a }
  let rule4b ← compareRule4b? mol profile authoritative state fuel (.actual left) (.actual right)
  if rule4b != Ordering.eq then return { ordering := rule4b }
  let rule4c ←
    if state.any (fun fact => !fact.uppercase) then
      compareRule4cWithWitness? mol profile authoritative state
        (compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c)
        (compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c)
        fuel [(.actual left, .actual right)]
    else some { ordering := Ordering.eq }
  if rule4c.ordering != Ordering.eq then
    -- Rule 4c establishes ordinary priority between unlike pseudoasymmetric descriptors.  The
    -- root is not thereby pseudoasymmetric: lowercase is introduced only by an enantiomorphic
    -- Rule-5 comparison.  Retain the carrier as evidence, but keep `pseudo` false.
    return { ordering := rule4c.ordering, rule4cCarrier? := rule4c.carrier? }
  let rule5 ← compareRule5? mol profile authoritative state fuel (.actual left) (.actual right)
  some { ordering := rule5.ordering, pseudo := rule5.pseudo }



def historicalRestrictedDecision? (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : CanonicalRerootCursor) :
    Option OccurrenceComparison := do
  let cmp ← compareBranch? mol profile authoritative fuel .rule2 (.actual left) (.actual right)
  if cmp != .eq then some { ordering := cmp }
  else if state.isEmpty then some { ordering := .eq } else none


def decision? := decisionComplete?

end FrameRuntime

namespace FramedCompleteRuntime
open RawMolecule

/-- Complete insertion: nil validates the original cursor; every comparison is the actual
shared-profile decision. The count retains every observed Rule5 pseudo flag, including a boundary
that did not move the candidate. -/
def trackedInsertComplete? (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat)
    (candidate : CanonicalRerootCursor) :
    List CanonicalRerootCursor → Option (List CanonicalRerootCursor × Nat)
  | [] => do
      let _ ← FrameRuntime.cursor? mol profile (.actual candidate)
      some ([candidate], 0)
  | head :: tail => do
      let decision ← FrameRuntime.decisionComplete? mol profile authoritative state fuel candidate head
      let observed := if decision.pseudo then 1 else 0
      if decision.ordering == Ordering.lt then do
        let inserted ← trackedInsertComplete? mol profile authoritative state fuel candidate tail
        some (head :: inserted.1, observed + inserted.2)
      else some (candidate :: head :: tail, observed)

/-- Add tail-sort and insertion counters exactly as the legacy tracked sorter does, while all
actual decisions use the passed frame. -/
def trackedSortComplete? (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat) :
    List CanonicalRerootCursor → Option (List CanonicalRerootCursor × Nat)
  | [] => some ([], 0)
  | head :: tail => do
      let sorted ← trackedSortComplete? mol profile authoritative state fuel tail
      let inserted ← trackedInsertComplete? mol profile authoritative state fuel head sorted.1
      some (inserted.1, sorted.2 + inserted.2)

/-- Exact final cursor pairs and full decisions, retaining Rule4c carrier and Rule5 pseudo. -/
def adjacentComplete? (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat) :
    List CanonicalRerootCursor → Option (List (OccurrenceComparedPair mol state fuel))
  | [] | [_] => some []
  | left :: right :: tail => do
      let decision ← FrameRuntime.decisionComplete? mol profile authoritative state fuel left right
      let rest ← adjacentComplete? mol profile authoritative state fuel (right :: tail)
      some ({ left := left, right := right, decision := decision } :: rest)

/-- New ordinary entry point in either mode, preserving the maintained actual parser/model fact
formula. No supplied profile, ranking, positions or desired fact equation is an input. -/
def occurrenceFactComplete? (mol : RawMolecule) (authoritative : Bool) (fuel : Nat)
    (state : OccurrenceAuxState) (node : CanonicalBranchNode) : Option OccurrenceAuxFact := do
  let profile ← FrameRuntime.profile? mol node
  let spec ← mol.atomAt? node.atom
  let parity ← spec.tetrahedral?
  let ligands := mol.ligandsWithLonePair node.atom
  let roots ← occurrenceLigandFrame? mol node
  let sorted ← trackedSortComplete? mol profile authoritative state fuel roots
  let positions ← sorted.1.mapM fun cursor =>
    (ligands.zipIdx.find? fun entry => entry.1 == cursor.node.atom).map Prod.snd
  let compared ← adjacentComplete? mol profile authoritative state fuel sorted.1
  let finalDecisions := compared.map fun comparison => comparison.decision
  let strict := finalDecisions.all fun decision => decision.ordering != Ordering.eq
  let pseudoPairCount := (finalDecisions.filter fun decision => decision.pseudo).length
  if !strict then none else
    let rawDescriptor := RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven positions)
    some { key := canonicalOccurrenceKey node
           atom := node.atom
           descriptor := rawDescriptor
           uppercase := pseudoPairCount % 2 == 0
           priorityPositions := positions }

end FramedCompleteRuntime

namespace FrameRuntime

def trackedInsert? := FramedCompleteRuntime.trackedInsertComplete?


def trackedSort? := FramedCompleteRuntime.trackedSortComplete?


def adjacent? := FramedCompleteRuntime.adjacentComplete?

end FrameRuntime

/-- Original occurrence evaluator retained for domains outside the generated-real-tree profile.
Its body is unchanged from the main integration baseline. -/
def legacyOccurrenceFact? (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) : Option OccurrenceAuxFact := do
  let spec ← mol.atomAt? node.atom
  let parity ← spec.tetrahedral?
  let ligands := mol.ligandsWithLonePair node.atom
  let roots ← occurrenceLigandFrame? mol node
  let sorted ← sortOccurrencesTracked? mol state fuel roots
  let positions ← sorted.1.mapM fun cursor =>
    (ligands.zipIdx.find? fun entry => entry.1 == cursor.node.atom).map Prod.snd
  let compared ← compareOccurrenceAdjacentPairs? mol state fuel sorted.1
  let finalDecisions := compared.map fun comparison => comparison.decision
  let strict := finalDecisions.all fun decision => decision.ordering != Ordering.eq
  let pseudoPairCount := (finalDecisions.filter fun decision => decision.pseudo).length
  if !strict then none else
    let rawDescriptor := RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven positions)
    some { key := canonicalOccurrenceKey node
           atom := node.atom
           -- Rule 4c has already changed `positions`; applying the winning carrier's descriptor
           -- sense once more would double-count that priority decision.
           descriptor := rawDescriptor
           -- Pseudoasymmetry is a property of the final adjacent enantiomorphic ligand pair,
           -- not of the transient comparisons made by insertion sort.  Counting insertion calls
           -- changes with input order and can count the same decisive boundary more than once.
           uppercase := pseudoPairCount % 2 == 0
           priorityPositions := positions }

/-- Accepted generated-real-tree evaluator, including its original refusal behavior. -/
def framedOccurrenceFact? (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) : Option OccurrenceAuxFact := do
  let profile ← FrameRuntime.profile? mol node
  let spec ← mol.atomAt? node.atom
  let parity ← spec.tetrahedral?
  let ligands := mol.ligandsWithLonePair node.atom
  let roots ← occurrenceLigandFrame? mol node
  let sorted ← FrameRuntime.trackedSort? mol profile false state fuel roots
  let positions ← sorted.1.mapM fun cursor =>
    (ligands.zipIdx.find? fun entry => entry.1 == cursor.node.atom).map Prod.snd
  let compared ← FrameRuntime.adjacent? mol profile false state fuel sorted.1
  let finalDecisions := compared.map fun comparison => comparison.decision
  let strict := finalDecisions.all fun decision => decision.ordering != Ordering.eq
  let pseudoPairCount := (finalDecisions.filter fun decision => decision.pseudo).length
  if !strict then none else
    let rawDescriptor := RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven positions)
    some { key := canonicalOccurrenceKey node
           atom := node.atom
           -- Rule 4c has already changed `positions`; applying the winning carrier's descriptor
           -- sense once more would double-count that priority decision.
           descriptor := rawDescriptor
           -- Pseudoasymmetry is a property of the final adjacent enantiomorphic ligand pair,
           -- not of the transient comparisons made by insertion sort.  Counting insertion calls
           -- changes with input order and can count the same decisive boundary more than once.
           uppercase := pseudoPairCount % 2 == 0
           priorityPositions := positions }

/-- Select the repaired evaluator only when its profile exists. A refusal from that
evaluator is final; only profile unavailability selects the legacy evaluator. -/
def occurrenceFact? (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) : Option OccurrenceAuxFact :=
  match FrameRuntime.profile? mol node with
  | none => legacyOccurrenceFact? mol fuel state node
  | some _ => framedOccurrenceFact? mol fuel state node

theorem framedOccurrenceFact?_eq_complete (mol : RawMolecule) (fuel : Nat)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) :
    framedOccurrenceFact? mol fuel state node =
      FramedCompleteRuntime.occurrenceFactComplete? mol false fuel state node := rfl

theorem occurrenceFact?_eq_legacy_of_profile_none (mol : RawMolecule) (fuel : Nat)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (unavailable : FrameRuntime.profile? mol node = none) :
    occurrenceFact? mol fuel state node = legacyOccurrenceFact? mol fuel state node := by
  simp only [occurrenceFact?, unavailable]

theorem occurrenceFact?_eq_framed_of_profile_some (mol : RawMolecule) (fuel : Nat)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (profile : FrameRuntime.Profile) (available : FrameRuntime.profile? mol node = some profile) :
    occurrenceFact? mol fuel state node = framedOccurrenceFact? mol fuel state node := by
  simp only [occurrenceFact?, available]

def canonicalCenterRoot (center : ℕ) : RawMolecule.CanonicalBranchNode :=
  { atom := center, parent := center, history := [center],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

def collectCanonicalTree (mol : RawMolecule) :
    ℕ → ℕ → List RawMolecule.CanonicalBranchNode →
      Option (List RawMolecule.CanonicalBranchNode)
  | 0, _, _ => none
  | _ + 1, _, [] => some []
  | fuel + 1, cap, frontier =>
      if cap < frontier.length then none else do
        let next := frontier.flatMap mol.canonicalChildren
        let tail ← collectCanonicalTree mol fuel (cap - frontier.length) next
        some (frontier ++ tail)

/-- Complete finite canonical occurrence tree without an arbitrary total-occurrence budget. -/
def collectCanonicalTreeAuthoritative (mol : RawMolecule) :
    ℕ → List RawMolecule.CanonicalBranchNode →
      Option (List RawMolecule.CanonicalBranchNode)
  | 0, [] => some []
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, frontier => do
      let next := frontier.flatMap mol.canonicalChildren
      let tail ← collectCanonicalTreeAuthoritative mol fuel next
      some (frontier ++ tail)

def discoverOccurrenceAuxBatches
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact) :
    ℕ → List RawMolecule.CanonicalBranchNode → OccurrenceAuxState → OccurrenceAuxState
  | 0, _, state => state
  | remaining + 1, nodes, state =>
      match nodes with
      | [] => state
      | first :: _ =>
          let depth := first.depth
          let batchNodes := nodes.takeWhile fun node => node.depth == depth
          let rest := nodes.dropWhile fun node => node.depth == depth
          let batch := batchNodes.filterMap (label? state)
          discoverOccurrenceAuxBatches label? remaining rest (state ++ batch)

/-- Fail-closed authoritative batch discovery.

Every node in the supplied list is an expected annotated occurrence.  Labels within one depth
batch are computed against the same deeper state; if any expected label is unavailable, the whole
authoritative environment is unavailable rather than silently treating that occurrence as absent. -/
def discoverOccurrenceAuxBatchesAuthoritative?
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact) :
    ℕ → List RawMolecule.CanonicalBranchNode → OccurrenceAuxState → Option OccurrenceAuxState
  | 0, [], state => some state
  | 0, _ :: _, _ => none
  | _ + 1, [], state => some state
  | remaining + 1, nodes, state => do
      let first ← nodes.head?
      let depth := first.depth
      let batchNodes := nodes.takeWhile fun node => node.depth == depth
      let rest := nodes.dropWhile fun node => node.depth == depth
      let batch ← batchNodes.mapM (label? state)
      discoverOccurrenceAuxBatchesAuthoritative? label? remaining rest (state ++ batch)

/-! ### Width-unbounded descriptor-bearing occurrence comparison -/

/-- Priority-ranked re-rooted children padded to the official bonding-number-six arity. -/
def rankedCursorChildrenAuthoritative? (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (cursor : CanonicalRerootCursor) : Option (List CanonicalRerootCursor) := do
  let children := cursor.children mol
  if RawMolecule.authoritativeChildSlots < children.length then none else
    let sorted ← sortCursorsBy? before children
    let phantom := mol.canonicalPhantom cursor.node.atom (cursor.node.rule1bRootDistance + 1)
    some (sorted ++ List.replicate
      (RawMolecule.authoritativeChildSlots - sorted.length) { node := phantom })

/-- Compare a complete re-rooted sphere with authoritative constitutional node labels. -/
def compareCursorPairLabelsAuthoritative? (mol : RawMolecule)
    (rule : RawMolecule.CanonicalRuleStage) :
    List (CanonicalRerootCursor × CanonicalRerootCursor) → Option Ordering
  | [] => some Ordering.eq
  | pair :: pairs =>
      match mol.compareCanonicalNodeRuleAuthoritative? rule pair.1.node pair.2.node with
      | none => none
      | some Ordering.eq => compareCursorPairLabelsAuthoritative? mol rule pairs
      | some decision => some decision

/-- Expand a paired occurrence sphere without a global frontier limit. -/
def nextCursorPairsAuthoritative? (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    List (CanonicalRerootCursor × CanonicalRerootCursor) →
      Option (List (CanonicalRerootCursor × CanonicalRerootCursor))
  | [] => some []
  | pair :: pairs => do
      let rest ← nextCursorPairsAuthoritative? mol before pairs
      if cursorTerminal mol pair.1 && cursorTerminal mol pair.2 then some rest else
        let left ← rankedCursorChildrenAuthoritative? mol before pair.1
        let right ← rankedCursorChildrenAuthoritative? mol before pair.2
        some (left.zip right ++ rest)

/-- Exhaust one constitutional rule over complete re-rooted spheres. -/
def compareCursorRuleAuthoritative? (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (rule : RawMolecule.CanonicalRuleStage) :
    ℕ → List (CanonicalRerootCursor × CanonicalRerootCursor) → Option Ordering
  | 0, pairs =>
      match compareCursorPairLabelsAuthoritative? mol rule pairs with
      | none => none
      | some Ordering.eq =>
          match nextCursorPairsAuthoritative? mol before pairs with
          | some [] => some Ordering.eq
          | _ => none
      | some decision => some decision
  | fuel + 1, pairs =>
      match compareCursorPairLabelsAuthoritative? mol rule pairs with
      | none => none
      | some Ordering.eq =>
          match nextCursorPairsAuthoritative? mol before pairs with
          | none => none
          | some [] => some Ordering.eq
          | some next => compareCursorRuleAuthoritative? mol before rule fuel next
      | some decision => some decision

/-- Complete re-rooted constitutional comparison through Rules 1a, 1b, and 2. -/
def compareCursorBranchAtAuthoritative? (mol : RawMolecule) :
    ℕ → RawMolecule.CanonicalRuleStage → CanonicalRerootCursor →
      CanonicalRerootCursor → Option Ordering
  | 0, stage, left, right =>
      mol.compareCanonicalNodeThroughAuthoritative? stage left.node right.node
  | fuel + 1, stage, left, right =>
      let before := compareCursorBranchAtAuthoritative? mol fuel stage
      let compareRule := fun rule =>
        compareCursorRuleAuthoritative? mol before rule (fuel + 1) [(left, right)]
      match compareRule RawMolecule.CanonicalRuleStage.rule1a with
      | none => none
      | some Ordering.lt => some Ordering.lt
      | some Ordering.gt => some Ordering.gt
      | some Ordering.eq =>
          match stage with
          | RawMolecule.CanonicalRuleStage.rule1a => some Ordering.eq
          | RawMolecule.CanonicalRuleStage.rule1b =>
              compareRule RawMolecule.CanonicalRuleStage.rule1b
          | RawMolecule.CanonicalRuleStage.rule2 =>
              match compareRule RawMolecule.CanonicalRuleStage.rule1b with
              | some Ordering.eq => compareRule RawMolecule.CanonicalRuleStage.rule2
              | decision => decision

/-- Expand descriptor-paired occurrence spheres through the authoritative child ranker. -/
def nextOccurrenceDescriptorPairsAuthoritative? (mol : RawMolecule)
    (beforeLeft beforeRight : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    List (CanonicalRerootCursor × CanonicalRerootCursor) →
      Option (List (CanonicalRerootCursor × CanonicalRerootCursor))
  | [] => some []
  | pair :: pairs => do
      let rest ← nextOccurrenceDescriptorPairsAuthoritative? mol beforeLeft beforeRight pairs
      if cursorTerminal mol pair.1 && cursorTerminal mol pair.2 then some rest else
        let left ← rankedCursorChildrenAuthoritative? mol beforeLeft pair.1
        let right ← rankedCursorChildrenAuthoritative? mol beforeRight pair.2
        some (left.zip right ++ rest)

/-- Exhaust one Rules-4a--5 descriptor stage without a sphere-width cap. -/
def compareOccurrenceDescriptorRuleAuthoritative? (mol : RawMolecule)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (stage : RawDescriptorRuleStage) :
    ℕ → List (CanonicalRerootCursor × CanonicalRerootCursor) → Option Ordering
  | 0, pairs =>
      match compareOccurrenceDescriptorPairLabels state stage pairs with
      | Ordering.eq =>
          match nextOccurrenceDescriptorPairsAuthoritative? mol beforeLeft beforeRight pairs with
          | some [] => some Ordering.eq
          | _ => none
      | decision => some decision
  | fuel + 1, pairs =>
      match compareOccurrenceDescriptorPairLabels state stage pairs with
      | Ordering.eq =>
          match nextOccurrenceDescriptorPairsAuthoritative? mol beforeLeft beforeRight pairs with
          | none => none
          | some [] => some Ordering.eq
          | some next => compareOccurrenceDescriptorRuleAuthoritative? mol state beforeLeft
              beforeRight stage fuel next
      | decision => some decision

/-- Authoritative Rule-4c comparison retaining its exact occurrence carrier. -/
def compareOccurrenceRule4cWithWitnessAuthoritative? (mol : RawMolecule)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    ℕ → List (CanonicalRerootCursor × CanonicalRerootCursor) → Option OccurrenceRule4cDecision
  | 0, pairs =>
      match compareOccurrenceRule4cPairLabelsWithWitness state pairs with
      | { ordering := Ordering.eq, .. } =>
          match nextOccurrenceDescriptorPairsAuthoritative? mol beforeLeft beforeRight pairs with
          | some [] => some { ordering := Ordering.eq }
          | _ => none
      | decision => some decision
  | fuel + 1, pairs =>
      match compareOccurrenceRule4cPairLabelsWithWitness state pairs with
      | { ordering := Ordering.eq, .. } =>
          match nextOccurrenceDescriptorPairsAuthoritative? mol beforeLeft beforeRight pairs with
          | none => none
          | some [] => some { ordering := Ordering.eq }
          | some next => compareOccurrenceRule4cWithWitnessAuthoritative? mol state beforeLeft
              beforeRight fuel next
      | decision => some decision

/-- Recursively refined occurrence comparison through the requested descriptor stage. -/
def compareOccurrenceDescriptorBranchAtAuthoritative? (mol : RawMolecule)
    (state : OccurrenceAuxState) :
    ℕ → RawDescriptorRuleStage → CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering
  | 0, stage, left, right =>
      match mol.compareCanonicalNodeThroughAuthoritative? RawMolecule.CanonicalRuleStage.rule2
          left.node right.node with
      | none => none
      | some Ordering.eq =>
          match compare (occurrenceNodePriority state .rule4a true left)
              (occurrenceNodePriority state .rule4a false right) with
          | Ordering.eq =>
              match stage with
              | .rule4a => some Ordering.eq
              | .rule4b _ _ | .rule4c | .rule5 _ _ =>
                  some (compare (occurrenceNodePriority state stage true left)
                    (occurrenceNodePriority state stage false right))
          | decision => some decision
      | some decision => some decision
  | fuel + 1, stage, left, right =>
      match compareCursorBranchAtAuthoritative? mol (fuel + 1)
          RawMolecule.CanonicalRuleStage.rule2 left right with
      | none => none
      | some Ordering.lt => some Ordering.lt
      | some Ordering.gt => some Ordering.gt
      | some Ordering.eq =>
          let beforeLeft :=
            compareOccurrenceDescriptorBranchAtAuthoritative? mol state fuel stage.leftInternal
          let beforeRight :=
            compareOccurrenceDescriptorBranchAtAuthoritative? mol state fuel stage.rightInternal
          let compareStage := fun selected =>
            compareOccurrenceDescriptorRuleAuthoritative? mol state beforeLeft beforeRight selected
              (fuel + 1) [(left, right)]
          match compareStage .rule4a with
          | none => none
          | some Ordering.lt => some Ordering.lt
          | some Ordering.gt => some Ordering.gt
          | some Ordering.eq =>
              match stage with
              | .rule4a => some Ordering.eq
              | .rule4b leftReference rightReference =>
                  compareStage (.rule4b leftReference rightReference)
              | .rule4c => compareStage .rule4c
              | .rule5 leftReference rightReference =>
                  match compareStage .rule4c with
                  | some Ordering.eq => compareStage (.rule5 leftReference rightReference)
                  | decision => decision

/-- Authoritative descriptor comparison after the constitutional ligand roots are known to tie. -/
def compareOccurrenceDescriptorAtTiedRootAuthoritative? (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (stage : RawDescriptorRuleStage)
    (left right : CanonicalRerootCursor) : Option Ordering :=
  let beforeLeft :=
    compareOccurrenceDescriptorBranchAtAuthoritative? mol state fuel stage.leftInternal
  let beforeRight :=
    compareOccurrenceDescriptorBranchAtAuthoritative? mol state fuel stage.rightInternal
  let compareStage := fun selected =>
    compareOccurrenceDescriptorRuleAuthoritative? mol state beforeLeft beforeRight selected fuel
      [(left, right)]
  match compareStage .rule4a with
  | none => none
  | some Ordering.lt => some Ordering.lt
  | some Ordering.gt => some Ordering.gt
  | some Ordering.eq =>
      match stage with
      | .rule4a => some Ordering.eq
      | .rule4b leftReference rightReference =>
          compareStage (.rule4b leftReference rightReference)
      | .rule4c =>
          if state.any fun fact => !fact.uppercase then compareStage .rule4c else some Ordering.eq
      | .rule5 leftReference rightReference =>
          let rule4c :=
            if state.any fun fact => !fact.uppercase then compareStage .rule4c else some Ordering.eq
          match rule4c with
          | some Ordering.eq => compareStage (.rule5 leftReference rightReference)
          | decision => decision

def rankOccurrenceRule4bReferencesAuthoritative? (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) (root : CanonicalRerootCursor) : List RS → Option (List RS)
  | [first, second] => do
      let decision ← compareOccurrenceDescriptorAtTiedRootAuthoritative? mol state fuel
        (.rule4b first second) root root
      if decision == Ordering.lt then some [second, first] else some [first, second]
  | references => some references

def compareOccurrenceRule4bAuthoritative? (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) (left right : CanonicalRerootCursor) : Option Ordering :=
  let leftReferences := occurrenceRule4bReferences mol state fuel [left]
  let rightReferences := occurrenceRule4bReferences mol state fuel [right]
  match leftReferences, rightReferences with
  | [], [] => some Ordering.eq
  | [_], [_, _] => some Ordering.gt
  | [_, _], [_] => some Ordering.lt
  | [leftReference], [rightReference] =>
      compareOccurrenceDescriptorAtTiedRootAuthoritative? mol state fuel
        (.rule4b leftReference rightReference) left right
  | [_, _], [_, _] => do
      let rankedLeft ← rankOccurrenceRule4bReferencesAuthoritative? mol state fuel left leftReferences
      let rankedRight ← rankOccurrenceRule4bReferencesAuthoritative? mol state fuel right rightReferences
      let first ← compareOccurrenceDescriptorAtTiedRootAuthoritative? mol state fuel
        (.rule4b (rankedLeft.getD 0 RS.R) (rankedRight.getD 0 RS.R)) left right
      if first != Ordering.eq then some first else
        compareOccurrenceDescriptorAtTiedRootAuthoritative? mol state fuel
          (.rule4b (rankedLeft.getD 1 RS.S) (rankedRight.getD 1 RS.S)) left right
  | _, _ => none

/-- Total shape extension of authoritative Rule 4b.

The legacy definition refuses only the empty/nonempty reference-shape combinations before it can
reach an inner descriptor comparison. The complete unary Rule-4b key already assigns absence the
zero reference-count class, below both supported nonempty classes; these two clauses expose that
ordering. All one/two-reference comparisons and all genuine inner failures are unchanged. -/
def compareOccurrenceRule4bUnrestrictedAuthoritative? (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ)
    (left right : CanonicalRerootCursor) : Option Ordering :=
  let leftReferences := occurrenceRule4bReferences mol state fuel [left]
  let rightReferences := occurrenceRule4bReferences mol state fuel [right]
  match leftReferences, rightReferences with
  | [], [] => some Ordering.eq
  | [], [_] | [], [_, _] => some Ordering.lt
  | [_], [] | [_, _], [] => some Ordering.gt
  | [_], [_, _] => some Ordering.gt
  | [_, _], [_] => some Ordering.lt
  | [leftReference], [rightReference] =>
      compareOccurrenceDescriptorAtTiedRootAuthoritative? mol state fuel
        (.rule4b leftReference rightReference) left right
  | [_, _], [_, _] => do
      let rankedLeft ← rankOccurrenceRule4bReferencesAuthoritative? mol state fuel left
        leftReferences
      let rankedRight ← rankOccurrenceRule4bReferencesAuthoritative? mol state fuel right
        rightReferences
      let first ← compareOccurrenceDescriptorAtTiedRootAuthoritative? mol state fuel
        (.rule4b (rankedLeft.getD 0 RS.R) (rankedRight.getD 0 RS.R)) left right
      if first != Ordering.eq then some first else
        compareOccurrenceDescriptorAtTiedRootAuthoritative? mol state fuel
          (.rule4b (rankedLeft.getD 1 RS.S) (rankedRight.getD 1 RS.S)) left right
  | _, _ => none

def compareOccurrenceRule5Authoritative? (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) (left right : CanonicalRerootCursor) : Option RawRule5Comparison := do
  let cmpR ← compareOccurrenceDescriptorAtTiedRootAuthoritative? mol state fuel
    (.rule5 RS.R RS.R) left right
  let cmpS ← compareOccurrenceDescriptorAtTiedRootAuthoritative? mol state fuel
    (.rule5 RS.S RS.S) left right
  match cmpR with
  | Ordering.lt => some { ordering := Ordering.lt, pseudo := cmpS != Ordering.lt }
  | Ordering.gt => some { ordering := Ordering.gt, pseudo := cmpS != Ordering.gt }
  | Ordering.eq => some { ordering := Ordering.eq, pseudo := false }

/-- Conservative authoritative constitutional stage for two exact re-rooted cursors. -/
def certifiedConstitutionalStageAuthoritative? (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor) : Option Ordering := do
  let constitutional ← compareCursorBranchAtAuthoritative? mol fuel
    RawMolecule.CanonicalRuleStage.rule2 left right
  if occurrenceRootsProvedAutomorphic mol fuel left right constitutional then none
  else some constitutional

/-- Complete Rules 1a--5 comparison of two descriptor-bearing occurrences. -/
def compareOccurrenceBranchesAuthoritative? (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) (left right : CanonicalRerootCursor) : Option OccurrenceComparison := do
  let constitutional ← certifiedConstitutionalStageAuthoritative? mol fuel left right
  if constitutional != Ordering.eq then return { ordering := constitutional }
  let rule4a ← compareOccurrenceDescriptorAtTiedRootAuthoritative? mol state fuel .rule4a left right
  if rule4a != Ordering.eq then return { ordering := rule4a }
  let rule4b ← compareOccurrenceRule4bAuthoritative? mol state fuel left right
  if rule4b != Ordering.eq then return { ordering := rule4b }
  let rule4c ←
    if state.any fun fact => !fact.uppercase then
      let before := compareOccurrenceDescriptorBranchAtAuthoritative? mol state fuel .rule4c
      compareOccurrenceRule4cWithWitnessAuthoritative? mol state before before fuel [(left, right)]
    else some { ordering := Ordering.eq }
  if rule4c.ordering != Ordering.eq then
    return { ordering := rule4c.ordering, rule4cCarrier? := rule4c.carrier? }
  let rule5 ← compareOccurrenceRule5Authoritative? mol state fuel left right
  some { ordering := rule5.ordering, pseudo := rule5.pseudo }

/-- Chemically complete authoritative Rules-1a--5 comparison.

The older `compareOccurrenceBranchesAuthoritative?` deliberately retained the production
automorphism-conflict gate as a conservative migration safeguard. That gate is not a CIP sequence
rule and can refuse after the exact constitutional comparator has already produced a result. This
entry point uses the proved width-unbounded constitutional comparison directly and therefore has
no heuristic gate. -/
def compareOccurrenceBranchesUnrestrictedAuthoritative? (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ)
    (left right : CanonicalRerootCursor) : Option OccurrenceComparison := do
  let constitutional ←
    compareCursorBranchAtAuthoritative? mol fuel RawMolecule.CanonicalRuleStage.rule2 left right
  if constitutional != Ordering.eq then return { ordering := constitutional }
  let rule4a ← compareOccurrenceDescriptorAtTiedRootAuthoritative? mol state fuel .rule4a
    left right
  if rule4a != Ordering.eq then return { ordering := rule4a }
  let rule4b ← compareOccurrenceRule4bUnrestrictedAuthoritative? mol state fuel left right
  if rule4b != Ordering.eq then return { ordering := rule4b }
  let rule4c ←
    if state.any fun fact => !fact.uppercase then
      let before := compareOccurrenceDescriptorBranchAtAuthoritative? mol state fuel .rule4c
      compareOccurrenceRule4cWithWitnessAuthoritative? mol state before before fuel [(left, right)]
    else some { ordering := Ordering.eq }
  if rule4c.ordering != Ordering.eq then
    return { ordering := rule4c.ordering, rule4cCarrier? := rule4c.carrier? }
  let rule5 ← compareOccurrenceRule5Authoritative? mol state fuel left right
  some { ordering := rule5.ordering, pseudo := rule5.pseudo }

/-- Fast proved occurrence comparison followed by the authoritative path only on exhaustion. -/
def compareOccurrenceBranchesComplete? (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) (left right : CanonicalRerootCursor) : Option OccurrenceComparison :=
  match compareOccurrenceBranches? mol state fuel left right with
  | some decision => some decision
  | none => compareOccurrenceBranchesAuthoritative? mol state fuel left right

/-- Authoritative insertion sort retaining the Rule-5 pseudoasymmetric decision count. -/
def insertOccurrenceTrackedAuthoritative? (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) (candidate : CanonicalRerootCursor) :
    List CanonicalRerootCursor → Option (List CanonicalRerootCursor × ℕ)
  | [] => some ([candidate], 0)
  | head :: tail => do
      let decision ← compareOccurrenceBranchesComplete? mol state fuel candidate head
      let observed := if decision.pseudo then 1 else 0
      if decision.ordering == Ordering.lt then
        let inserted ← insertOccurrenceTrackedAuthoritative? mol state fuel candidate tail
        some (head :: inserted.1, observed + inserted.2)
      else some (candidate :: head :: tail, observed)

def sortOccurrencesTrackedAuthoritative? (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) : List CanonicalRerootCursor → Option (List CanonicalRerootCursor × ℕ)
  | [] => some ([], 0)
  | cursor :: cursors => do
      let sorted ← sortOccurrencesTrackedAuthoritative? mol state fuel cursors
      let inserted ← insertOccurrenceTrackedAuthoritative? mol state fuel cursor sorted.1
      some (inserted.1, sorted.2 + inserted.2)

def compareOccurrenceAdjacentPairsAuthoritative? (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) :
    List CanonicalRerootCursor → Option (List OccurrenceComparison)
  | [] | [_] => some []
  | left :: right :: remaining => do
      let decision ← compareOccurrenceBranchesComplete? mol state fuel left right
      let deeper ← compareOccurrenceAdjacentPairsAuthoritative? mol state fuel (right :: remaining)
      some (decision :: deeper)

/-- Original occurrence evaluator retained for domains outside the generated-real-tree profile.
Its body is unchanged from the main integration baseline. -/
def legacyOccurrenceFactAuthoritative? (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) : Option OccurrenceAuxFact := do
  let spec ← mol.atomAt? node.atom
  let parity ← spec.tetrahedral?
  let ligands := mol.ligandsWithLonePair node.atom
  let roots ← occurrenceLigandFrame? mol node
  let sorted ← sortOccurrencesTrackedAuthoritative? mol state fuel roots
  let positions ← sorted.1.mapM fun cursor =>
    (ligands.zipIdx.find? fun entry => entry.1 == cursor.node.atom).map Prod.snd
  let decisions ← compareOccurrenceAdjacentPairsAuthoritative? mol state fuel sorted.1
  if !(decisions.all fun decision => decision.ordering != Ordering.eq) then none else
    let pseudoPairCount := (decisions.filter fun decision => decision.pseudo).length
    some { key := canonicalOccurrenceKey node
           atom := node.atom
           descriptor := RawMolecule.descriptorOfParity parity
             (RawMolecule.permutationIsEven positions)
           uppercase := pseudoPairCount % 2 == 0
           priorityPositions := positions }

/-- Accepted generated-real-tree evaluator, including its original refusal behavior. -/
def framedOccurrenceFactAuthoritative? (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) : Option OccurrenceAuxFact := do
  let profile ← FrameRuntime.profile? mol node
  let spec ← mol.atomAt? node.atom
  let parity ← spec.tetrahedral?
  let ligands := mol.ligandsWithLonePair node.atom
  let roots ← occurrenceLigandFrame? mol node
  let sorted ← FrameRuntime.trackedSort? mol profile true state fuel roots
  let positions ← sorted.1.mapM fun cursor =>
    (ligands.zipIdx.find? fun entry => entry.1 == cursor.node.atom).map Prod.snd
  let decisions ← (FrameRuntime.adjacent? mol profile true state fuel sorted.1).map (fun pairs => pairs.map OccurrenceComparedPair.decision)
  if !(decisions.all fun decision => decision.ordering != Ordering.eq) then none else
    let pseudoPairCount := (decisions.filter fun decision => decision.pseudo).length
    some { key := canonicalOccurrenceKey node
           atom := node.atom
           descriptor := RawMolecule.descriptorOfParity parity
             (RawMolecule.permutationIsEven positions)
           uppercase := pseudoPairCount % 2 == 0
           priorityPositions := positions }

/-- Select the repaired evaluator only when its profile exists. A refusal from that
evaluator is final; only profile unavailability selects the legacy evaluator. -/
def occurrenceFactAuthoritative? (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) : Option OccurrenceAuxFact :=
  match FrameRuntime.profile? mol node with
  | none => legacyOccurrenceFactAuthoritative? mol fuel state node
  | some _ => framedOccurrenceFactAuthoritative? mol fuel state node

theorem framedOccurrenceFactAuthoritative?_eq_complete (mol : RawMolecule) (fuel : Nat)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) :
    framedOccurrenceFactAuthoritative? mol fuel state node =
      FramedCompleteRuntime.occurrenceFactComplete? mol true fuel state node := by
  unfold framedOccurrenceFactAuthoritative? FramedCompleteRuntime.occurrenceFactComplete?
  dsimp only [FrameRuntime.trackedSort?, FrameRuntime.adjacent?, Bind.bind]
  simp only [Option.bind_map]
  rfl

theorem occurrenceFactAuthoritative?_eq_legacy_of_profile_none
    (mol : RawMolecule) (fuel : Nat) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (unavailable : FrameRuntime.profile? mol node = none) :
    occurrenceFactAuthoritative? mol fuel state node =
      legacyOccurrenceFactAuthoritative? mol fuel state node := by
  simp only [occurrenceFactAuthoritative?, unavailable]

theorem occurrenceFactAuthoritative?_eq_framed_of_profile_some
    (mol : RawMolecule) (fuel : Nat) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (profile : FrameRuntime.Profile)
    (available : FrameRuntime.profile? mol node = some profile) :
    occurrenceFactAuthoritative? mol fuel state node =
      framedOccurrenceFactAuthoritative? mol fuel state node := by
  simp only [occurrenceFactAuthoritative?, available]

/-- Complete auxiliary environment over every finite occurrence in the center-rooted CIP digraph. -/
def buildOccurrenceAuxStateFullyAuthoritative? (mol : RawMolecule) (fuel center : ℕ) :
    Option OccurrenceAuxState := do
  let nodes ← collectCanonicalTreeAuthoritative mol fuel [canonicalCenterRoot center]
  let occurrences := nodes.filter fun node =>
    node.provenance == RawMolecule.CanonicalNodeProvenance.realAtom && node.atom != center &&
      (mol.atomAt? node.atom).any fun spec => spec.tetrahedral?.isSome
  let ordered := sortDescBy (fun left right => left.depth ≥ right.depth) occurrences
  discoverOccurrenceAuxBatchesAuthoritative? (occurrenceFactAuthoritative? mol fuel)
    (ordered.length + 1) ordered []

/-- Exact final descriptor fact from the complete occurrence-local Rules-4a--5 environment. -/
def tetrahedralOccurrenceFactAuthoritative? (mol : RawMolecule) (fuel center : ℕ) :
    Option RawDescriptorFact := do
  let state ← buildOccurrenceAuxStateFullyAuthoritative? mol fuel center
  let fact ← occurrenceFactAuthoritative? mol fuel state (canonicalCenterRoot center)
  some { atom := center
         descriptor := fact.descriptor
         uppercase := fact.uppercase
         evidenceSize := max 1 state.length
         decisiveRule? := none
         descriptorDependentPairs := state.length
         priorityPositions := fact.priorityPositions }

def buildOccurrenceAuxStateWithCap? (mol : RawMolecule) (fuel center occurrenceCap : ℕ) :
    Option OccurrenceAuxState := do
  let nodes ← collectCanonicalTree mol fuel occurrenceCap
    [canonicalCenterRoot center]
  let occurrences := nodes.filter fun node =>
    node.provenance == RawMolecule.CanonicalNodeProvenance.realAtom && node.atom != center &&
      (mol.atomAt? node.atom).any fun spec => spec.tetrahedral?.isSome
  let ordered := sortDescBy (fun left right => left.depth ≥ right.depth) occurrences
  some (discoverOccurrenceAuxBatches (occurrenceFact? mol fuel)
    (ordered.length + 1) ordered [])

/-- Complete occurrence-local auxiliary environment over every finite canonical occurrence. -/
def buildOccurrenceAuxStateAuthoritative? (mol : RawMolecule) (fuel center : ℕ) :
    Option OccurrenceAuxState := do
  let nodes ← collectCanonicalTreeAuthoritative mol fuel [canonicalCenterRoot center]
  let occurrences := nodes.filter fun node =>
    node.provenance == RawMolecule.CanonicalNodeProvenance.realAtom && node.atom != center &&
      (mol.atomAt? node.atom).any fun spec => spec.tetrahedral?.isSome
  let ordered := sortDescBy (fun left right => left.depth ≥ right.depth) occurrences
  some (discoverOccurrenceAuxBatches (occurrenceFact? mol fuel)
    (ordered.length + 1) ordered [])

/-- Complete auxiliary environment for ordinary Rules 4a--5 refinement. -/
def buildOccurrenceAuxState? (mol : RawMolecule) (fuel center : ℕ) : Option OccurrenceAuxState :=
  buildOccurrenceAuxStateAuthoritative? mol fuel center

/-- Descriptor assignment at the primary root after all deeper occurrence-local auxiliary labels
have been committed.  Global facts are not seeds: the written configuration and the fixed digraph
determine each occurrence anew, including its uppercase/lowercase class. -/
def tetrahedralOccurrenceFactWithCap? (mol : RawMolecule) (fuel center cap : ℕ) :
    Option RawDescriptorFact := do
  let state ← buildOccurrenceAuxStateWithCap? mol fuel center cap
  let fact ← occurrenceFact? mol fuel state (canonicalCenterRoot center)
  some { atom := center
         descriptor := fact.descriptor
         uppercase := fact.uppercase
         evidenceSize := max 1 state.length
         decisiveRule? := none
         descriptorDependentPairs := state.length
         priorityPositions := fact.priorityPositions }

/-- Descriptor fact over every finite center-rooted occurrence, without a total-node budget. -/
def tetrahedralOccurrenceFactTreeCapFree? (mol : RawMolecule) (fuel center : ℕ) :
    Option RawDescriptorFact := do
  let state ← buildOccurrenceAuxStateAuthoritative? mol fuel center
  let fact ← occurrenceFact? mol fuel state (canonicalCenterRoot center)
  some { atom := center
         descriptor := fact.descriptor
         uppercase := fact.uppercase
         evidenceSize := max 1 state.length
         decisiveRule? := none
         descriptorDependentPairs := state.length
         priorityPositions := fact.priorityPositions }

/-- Public occurrence fact routed through fully authoritative occurrence comparison and collection. -/
def tetrahedralOccurrenceFact? (mol : RawMolecule) (fuel center : ℕ) : Option RawDescriptorFact :=
  tetrahedralOccurrenceFactAuthoritative? mol fuel center

/-- Revised Rule 5 compares complete lists under both possible reference descriptors.

Equal directions under the two references are an ordinary priority (`±1`); opposite directions
are the enantiomorphic pseudoasymmetric priority (`±2`). -/
def compareRule5Recursive? (mol : RawMolecule) (state : RawDescriptorState)
    (center left right : ℕ) : Option RawRule5Comparison := do
  let cmpR ← compareRawDescriptorBranchesComplete? mol state (.rule5 RS.R RS.R) center left right
  let cmpS ← compareRawDescriptorBranchesComplete? mol state (.rule5 RS.S RS.S) center left right
  match cmpR with
  | Ordering.lt => some { ordering := Ordering.lt, pseudo := cmpS != Ordering.lt }
  | Ordering.gt => some { ordering := Ordering.gt, pseudo := cmpS != Ordering.gt }
  | Ordering.eq => some { ordering := Ordering.eq, pseudo := false }

/-- Full Rules 3–5 comparison over corresponding descriptor positions in a ligand hierarchy.

The trace is refused when either Rule-4a hierarchy is unavailable.  Rule 4a precedes Rules 4b--5,
so converting an unavailable earlier observation to a tie and falling through could let a later
rule manufacture a priority that the current evidence does not justify. -/
def compareRawOfficialSequences (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center left right : ℕ) : Option (List CIPRuleDecision) := do
  let leftDescriptorLayers := branchDescriptorLayers mol state center left
  let rightDescriptorLayers := branchDescriptorLayers mol state center right
  let leftRule4a ← branchRule4aSparseLayers mol state center left
  let rightRule4a ← branchRule4aSparseLayers mol state center right
  let rule3 ← result.compareRule3GeometryAtCenter? mol (2 * mol.atomCount + 2) center left right
  return (
    [ { rule := CIPRuleFamily.doubleBondGeometry
        outcome := rule3 }
    , { rule := CIPRuleFamily.stereogenicUnitKind
        outcome := RawMolecule.compareSparseCanonicalLayers OfficialStereogenicUnitKind.compare
          leftRule4a rightRule4a }
    , { rule := CIPRuleFamily.likeUnlikeDescriptorPair
        outcome := compareRule4bLayerHierarchies leftDescriptorLayers rightDescriptorLayers }
    , { rule := CIPRuleFamily.pseudoasymmetricDescriptor
        outcome := RawMolecule.compareSparseCanonicalLayers compare
          (branchRule4cSparseLayers mol state center left)
          (branchRule4cSparseLayers mol state center right) }
    , { rule := CIPRuleFamily.pseudoasymmetricTiebreak
        outcome := RawMolecule.compareSparseCanonicalLayers compare
          (branchRule5SparseLayers mol state center left)
          (branchRule5SparseLayers mol state center right) }
    ])

/-- Official Rules 3–5 context perceived along one raw-molecule ligand branch. -/
def branchOfficialContext (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center ligand : ℕ) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  let geometries := result.rule3GeometrySequenceOnBranch mol center ligand
  let descriptors := branchDescriptorSequence mol state center ligand
  let rule3? := match geometries with | [geometry] => some geometry | _ => none
  let rule4a? :=
    descriptors.head?.map fun fact =>
      if fact.uppercase then OfficialStereogenicUnitKind.chiral
      else OfficialStereogenicUnitKind.pseudoasymmetric
  let rule4b? :=
    if state.any fun fact => !fact.uppercase then none else match descriptors with
    | left :: right :: _ =>
        if left.uppercase && right.uppercase then
        some (OfficialRule5Descriptor.pairKind
          (OfficialRule5Descriptor.ofRS left.descriptor)
          (OfficialRule5Descriptor.ofRS right.descriptor))
        else none
    | _ => none
  let rule4c? := descriptors.head?.bind fun fact =>
    if fact.uppercase then none
    else
      some (match fact.descriptor with
        | RS.R => OfficialPseudoasymmetricDescriptor.r
        | RS.S => OfficialPseudoasymmetricDescriptor.s)
  let rule5? := descriptors.head?.bind fun fact =>
    if fact.uppercase then some (OfficialRule5Descriptor.ofRS fact.descriptor) else none
  { rule3Geometry? := rule3?
    rule4aKind? := rule4a?
    rule4bPair? := rule4b?
    rule4cDescriptor? := rule4c?
    rule5Descriptor? := rule5? }

/-- Width-unbounded constitutional Rules 1a--2 followed by automatically perceived Rules 3, 4a,
4b, 4c, and 5 context.

The normative path does not accept a strict result merely because the legacy bounded sphere
comparator produced one: every constitutional result comes from the authoritative finite-digraph
comparator.  An explicit constitutional automorphism remains an independent sufficient tie
witness when that comparator cannot construct a result. -/
def compareBranchesThroughOfficialContext? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (_fuel center left right : ℕ) :
    Option Ordering :=
  let laterRules := fun _ =>
    (compareRawOfficialSequences result mol state center left right).map cipTraceOutcome
  match mol.compareBranchesAuthoritativeStatus center left right with
  | .lower => some Ordering.lt
  | .higher => some Ordering.gt
  | .tied => laterRules ()
  | .unresolved =>
      if mol.hasConstitutionAutomorphismSwapping center left right then laterRules () else none

/-- First decisive official context family for a branch pair, when constitution tied. -/
def decisiveOfficialFamilyForBranches? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (_fuel center left right : ℕ) :
    Option CIPRuleFamily :=
  let constitutionTied :=
    match mol.compareBranchesAuthoritativeStatus center left right with
    | .tied => true
    | .unresolved => mol.hasConstitutionAutomorphismSwapping center left right
    | _ => false
  if !constitutionTied then none else
    (compareRawOfficialSequences result mol state center left right).bind fun trace =>
      trace.find? (fun decision => decision.outcome != Ordering.eq) |>.map CIPRuleDecision.rule

/-- Rank ligand positions through the full perceived official-context fallthrough. -/
def rankBranchPositionsThroughOfficialContext? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel center : ℕ)
    (branches : List ℕ) : Option (List ℕ) :=
  let atomOf : ℕ → ℕ := fun position => branches.getD position 0
  let compareAt : ℕ → ℕ → Option Ordering := fun a b =>
    compareBranchesThroughOfficialContext? result mol state fuel center (atomOf a) (atomOf b)
  let before : ℕ → ℕ → Bool := fun a b => compareAt a b != some Ordering.lt
  let sorted := sortDescBy before (List.range branches.length)
  let strict :=
    (List.range (sorted.length - 1)).all fun index =>
      match sorted[index]?, sorted[index + 1]? with
      | some left, some right => compareAt left right == some Ordering.gt
      | _, _ => false
  if strict then some sorted else none

/-! ### Proposed Sequence Rule 6: reference-node promotion -/

/-- Rules 1--5 context with an explicit secondary constitutional witness for Rule 6.

The production compiled key can exceed its whole-tree budget even when the synchronized rooted
digraph comparison completes.  Rule 6 needs a proved pre-existing tie, not the former heuristic
"same element and both cyclic".  On primary failure, run the bounded option-valued cursor comparator:
a strict result remains strict, equality admits the later rules, and exhaustion remains `none`.
A checked whole-molecule automorphism is retained as an independent sufficient tie witness. -/
def compareBranchesBeforeRule6Context? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center left right : ℕ) : Option Ordering :=
  match compareBranchesThroughOfficialContext? result mol state fuel center left right with
  | some decision => some decision
  | none =>
      let laterRules := fun _ =>
        (compareRawOfficialSequences result mol state center left right).map cipTraceOutcome
      let leftCursor : CanonicalRerootCursor := { node := RawMolecule.canonicalRoot center left }
      let rightCursor : CanonicalRerootCursor := { node := RawMolecule.canonicalRoot center right }
      match compareCursorBranchAt mol (mol.atomCount + 1)
          RawMolecule.CanonicalRuleStage.rule2 leftCursor rightCursor with
      | some Ordering.lt => some Ordering.lt
      | some Ordering.gt => some Ordering.gt
      | some Ordering.eq => laterRules ()
      | none =>
          if mol.hasConstitutionAutomorphismSwapping center left right then laterRules () else none

/-- Cache every unordered comparison in one small ligand-position set.

Tetrahedral Rule-6 callers reuse the same six pre-Rule-6 decisions during sorting, adjacency checks,
and complete automorphism enumeration.  Re-running a completed cyclic digraph comparison inside the
automorphism predicate can multiply one bounded comparison hundreds of times. -/
def cachePositionComparisons (count : ℕ) (compareAt : ℕ → ℕ → Option Ordering) :
    List (ℕ × ℕ × Option Ordering) :=
  (List.range count).flatMap fun left =>
    (List.range count).filterMap fun right =>
      if left < right then some (left, right, compareAt left right) else none

/-- Read an oriented comparison from an unordered position-pair cache. -/
def cachedPositionComparison? (cache : List (ℕ × ℕ × Option Ordering))
    (left right : ℕ) : Option Ordering :=
  if left == right then some Ordering.eq
  else if left < right then
    (cache.find? fun entry => entry.1 == left && entry.2.1 == right).bind fun entry => entry.2.2
  else
    ((cache.find? fun entry => entry.1 == right && entry.2.1 == left).bind fun entry =>
      entry.2.2).map Ordering.swap

/-- Sparse Rule-6 promotion layers for one branch.

Every occurrence of the selected atom identity is promoted, including ring-closure duplicates.
The canonical paths retain the parent-ranked hierarchy, so a promotion reached through one return
path cannot slide into a different sibling slot. -/
def rule6PromotionLayersAuthoritative? (mol : RawMolecule) (center ligand reference : ℕ) :
    Option (List (List RawMolecule.CanonicalNatEntry)) := do
  let key ← branchCanonicalKeyAuthoritative? mol center ligand
  some (key.allAtoms.map fun layer =>
    layer.map fun entry => (entry.1, if entry.2 == reference then 1 else 0))

/-- Public Rule-6 promotion layers routed through width-unbounded key construction. -/
def rule6PromotionLayers? (mol : RawMolecule) (_fuel center ligand reference : ℕ) :
    Option (List (List RawMolecule.CanonicalNatEntry)) :=
  rule6PromotionLayersAuthoritative? mol center ligand reference

/-- Shortest root-avoiding distance from a ligand to the promoted reference atom. -/
def RawMolecule.rule6ReferenceDistance? (mol : RawMolecule) (blocked reference : ℕ) :
    ℕ → ℕ → List ℕ → List ℕ → Option ℕ
  | 0, _, _, _ => none
  | fuel + 1, distance, frontier, seen =>
      if frontier.contains reference then some distance else
        let next := (frontier.flatMap fun atom =>
          (mol.incidentAtoms atom).filter fun neighbor =>
            neighbor != blocked && !(seen.contains neighbor)).eraseDups
        if next.isEmpty then none else
          mol.rule6ReferenceDistance? blocked reference fuel (distance + 1) next (seen ++ next)

/-- Compare two branches by the promoted reference, with graph distance as a topology-only fallback
when constitutional key compilation is unavailable for a large mancude system. -/
def compareRule6Promotion? (mol : RawMolecule) (fuel center reference left right : ℕ) :
    Option Ordering :=
  let byDistance := fun _ =>
    match mol.rule6ReferenceDistance? center reference (mol.atomCount + 1) 0 [left] [left],
        mol.rule6ReferenceDistance? center reference (mol.atomCount + 1) 0 [right] [right] with
    | some leftDistance, some rightDistance =>
        if leftDistance < rightDistance then some Ordering.gt
        else if rightDistance < leftDistance then some Ordering.lt
        else some Ordering.eq
    | some _, none => some Ordering.gt
    | none, some _ => some Ordering.lt
    | none, none => none
  match rule6PromotionLayers? mol fuel center left reference,
      rule6PromotionLayers? mol fuel center right reference with
  | some leftLayers, some rightLayers =>
      match RawMolecule.compareSparseCanonicalLayers compare leftLayers rightLayers with
      | Ordering.eq => byDistance ()
      | decision => some decision
  | _, _ => byDistance ()

/-- Compare constitution and Rules 3–5, then promote one undifferentiated Rule-6 reference node. -/
def compareBranchesThroughRule6? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center reference left right : ℕ) : Option Ordering :=
  match compareBranchesBeforeRule6Context? result mol state fuel center left right with
  | some Ordering.lt => some Ordering.lt
  | some Ordering.gt => some Ordering.gt
  | some Ordering.eq => compareRule6Promotion? mol fuel center reference left right
  | none => none

/-- Strict ligand order after one Rule-6 promotion, starting from the in-place order established by
the preceding sort. -/
def rankBranchPositionsThroughRule6From? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center reference : ℕ) (branches : List ℕ) :
    List ℕ → Option (List ℕ) := fun initialPositions =>
  let atomOf := fun position => branches.getD position 0
  let compareAt := fun left right =>
    compareBranchesThroughRule6? result mol state fuel center reference
      (atomOf left) (atomOf right)
  let before := fun left right => compareAt left right != some Ordering.lt
  let sorted := sortDescBy before initialPositions
  let strict := (List.range (sorted.length - 1)).all fun index =>
    match sorted[index]?, sorted[index + 1]? with
    | some left, some right => compareAt left right == some Ordering.gt
    | _, _ => false
  if strict then some sorted else none

/-- Strict ligand order after one Rule-6 promotion from parser position order. -/
def rankBranchPositionsThroughRule6? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center reference : ℕ) (branches : List ℕ) :
    Option (List ℕ) :=
  rankBranchPositionsThroughRule6From? result mol state fuel center reference branches
    (List.range branches.length)

/-- A branch decision plus whether it was decided by Rule 6's `±2` comparison. -/
structure Rule6TrackedDecision where
  ordering : Ordering
  pseudo : Bool
  deriving DecidableEq, Repr

/-- Compare Rule-6 reference labels at corresponding cursor positions. -/
def compareOccurrenceRule6PairLabels (reference : ℕ) :
    List (CanonicalRerootCursor × CanonicalRerootCursor) → Ordering
  | [] => Ordering.eq
  | pair :: pairs =>
      match compare (if pair.1.node.atom == reference then 1 else 0)
          (if pair.2.node.atom == reference then 1 else 0) with
      | Ordering.eq => compareOccurrenceRule6PairLabels reference pairs
      | decision => decision

/-- Exhaust Rule 6 over a cursor sphere while preserving recursively ranked parent positions. -/
def compareOccurrenceRule6 (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (reference : ℕ) :
    ℕ → List (CanonicalRerootCursor × CanonicalRerootCursor) → Option Ordering
  | 0, pairs =>
      if RawMolecule.defaultBranchWidthCap < pairs.length then none else
        match compareOccurrenceRule6PairLabels reference pairs with
        | Ordering.eq =>
            match nextOccurrenceDescriptorPairs? mol before before pairs with
            | some [] => some Ordering.eq
            | _ => none
        | decision => some decision
  | fuel + 1, pairs =>
      if RawMolecule.defaultBranchWidthCap < pairs.length then none else
        match compareOccurrenceRule6PairLabels reference pairs with
        | Ordering.eq =>
            match nextOccurrenceDescriptorPairs? mol before before pairs with
            | none => none
            | some [] => some Ordering.eq
            | some next => compareOccurrenceRule6 mol before reference fuel next
        | decision => some decision

/-- Rules 1--5 followed by dynamically reranked Rule-6 reference promotion. -/
def compareOccurrenceBranchesThroughRule6At? (mol : RawMolecule)
    (aux : OccurrenceAuxState) (reference : ℕ) :
    ℕ → CanonicalRerootCursor → CanonicalRerootCursor → Option Rule6TrackedDecision
  | 0, left, right =>
      let rule6 :=
        let ordering := compare
          (if left.node.atom == reference then 1 else 0)
          (if right.node.atom == reference then 1 else 0)
        some { ordering := ordering, pseudo := ordering != Ordering.eq }
      match compareOccurrenceBranches? mol aux 0 left right with
      | some prior =>
          if prior.ordering != Ordering.eq then
            some { ordering := prior.ordering, pseudo := false }
          else rule6
      | none => none
  | fuel + 1, left, right =>
      let rule6 := do
        let before := fun a b =>
          (compareOccurrenceBranchesThroughRule6At? mol aux reference fuel a b).map
            Rule6TrackedDecision.ordering
        let ordering ← compareOccurrenceRule6 mol before reference (fuel + 1) [(left, right)]
        some { ordering := ordering, pseudo := ordering != Ordering.eq }
      match compareOccurrenceBranches? mol aux (fuel + 1) left right with
      | some prior =>
          if prior.ordering != Ordering.eq then
            some { ordering := prior.ordering, pseudo := false }
          else rule6
      | none => none

/-! ### Width-unbounded promoted Rule-6 occurrence comparison -/

/-- Exhaust reference-node promotion over complete re-rooted spheres without a global frontier
width cutoff. Child occurrences are ranked recursively by the supplied complete earlier-stage
comparison. -/
def compareOccurrenceRule6Authoritative (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (reference : ℕ) :
    ℕ → List (CanonicalRerootCursor × CanonicalRerootCursor) → Option Ordering
  | 0, pairs =>
      match compareOccurrenceRule6PairLabels reference pairs with
      | Ordering.eq =>
          match nextOccurrenceDescriptorPairsAuthoritative? mol before before pairs with
          | some [] => some Ordering.eq
          | _ => none
      | decision => some decision
  | fuel + 1, pairs =>
      match compareOccurrenceRule6PairLabels reference pairs with
      | Ordering.eq =>
          match nextOccurrenceDescriptorPairsAuthoritative? mol before before pairs with
          | none => none
          | some [] => some Ordering.eq
          | some next => compareOccurrenceRule6Authoritative mol before reference fuel next
      | decision => some decision

/-- Width-unbounded Rules-1a--5 comparison followed by dynamically reranked Rule-6 reference
promotion. An unsupported earlier authoritative stage remains an explicit failure; Rule 6 is
consulted exactly after a proved Rules-1--5 tie. -/
def compareOccurrenceBranchesThroughRule6AtAuthoritative? (mol : RawMolecule)
    (state : OccurrenceAuxState) (reference : ℕ) :
    ℕ → CanonicalRerootCursor → CanonicalRerootCursor → Option Rule6TrackedDecision
  | 0, left, right =>
      let rule6 :=
        let ordering := compare
          (if left.node.atom == reference then 1 else 0)
          (if right.node.atom == reference then 1 else 0)
        some { ordering := ordering, pseudo := ordering != Ordering.eq }
      match compareOccurrenceBranchesAuthoritative? mol state 0 left right with
      | some prior =>
          if prior.ordering != Ordering.eq then
            some { ordering := prior.ordering, pseudo := false }
          else rule6
      | none => none
  | fuel + 1, left, right =>
      let rule6 := do
        let before := fun a b =>
          (compareOccurrenceBranchesThroughRule6AtAuthoritative? mol state reference fuel a b).map
            Rule6TrackedDecision.ordering
        let ordering ← compareOccurrenceRule6Authoritative mol before reference (fuel + 1)
          [(left, right)]
        some { ordering := ordering, pseudo := ordering != Ordering.eq }
      match compareOccurrenceBranchesAuthoritative? mol state (fuel + 1) left right with
      | some prior =>
          if prior.ordering != Ordering.eq then
            some { ordering := prior.ordering, pseudo := false }
          else rule6
      | none => none

/-- Fully unrestricted Rules-1a--6 comparison. This is the completeness path: it combines the
uncapped promoted traversal with `compareOccurrenceBranchesUnrestrictedAuthoritative?`, whose
constitutional stage has no legacy automorphism refusal gate. -/
def compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? (mol : RawMolecule)
    (state : OccurrenceAuxState) (reference : ℕ) :
    ℕ → CanonicalRerootCursor → CanonicalRerootCursor → Option Rule6TrackedDecision
  | 0, left, right =>
      let rule6 :=
        let ordering := compare
          (if left.node.atom == reference then 1 else 0)
          (if right.node.atom == reference then 1 else 0)
        some { ordering := ordering, pseudo := ordering != Ordering.eq }
      match compareOccurrenceBranchesUnrestrictedAuthoritative? mol state 0 left right with
      | some prior =>
          if prior.ordering != Ordering.eq then
            some { ordering := prior.ordering, pseudo := false }
          else rule6
      | none => none
  | fuel + 1, left, right =>
      let rule6 := do
        let before := fun a b =>
          (compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference
            fuel a b).map Rule6TrackedDecision.ordering
        let ordering ← compareOccurrenceRule6Authoritative mol before reference (fuel + 1)
          [(left, right)]
        some { ordering := ordering, pseudo := ordering != Ordering.eq }
      match compareOccurrenceBranchesUnrestrictedAuthoritative? mol state (fuel + 1) left right with
      | some prior =>
          if prior.ordering != Ordering.eq then
            some { ordering := prior.ordering, pseudo := false }
          else rule6
      | none => none

/-- Preserve the proved bounded fast path, but remove its frontier cutoff whenever it exhausts.
Both branches remain fail-closed on genuinely unsupported chemistry. -/
def compareOccurrenceBranchesThroughRule6Complete? (mol : RawMolecule)
    (state : OccurrenceAuxState) (reference fuel : ℕ)
    (left right : CanonicalRerootCursor) : Option Rule6TrackedDecision :=
  match compareOccurrenceBranchesThroughRule6At? mol state reference fuel left right with
  | some decision => some decision
  | none =>
      compareOccurrenceBranchesThroughRule6AtAuthoritative? mol state reference fuel left right

/-- Rule-6 occurrence comparison with cap-free auxiliary-tree collection. -/
def compareOccurrenceBranchesThroughRule6TreeCapFree? (mol : RawMolecule)
    (fuel center reference left right : ℕ) :
    Option Rule6TrackedDecision :=
  match buildOccurrenceAuxStateAuthoritative? mol fuel center with
  | none => none
  | some aux =>
      compareOccurrenceBranchesThroughRule6At? mol aux reference (mol.atomCount + 1)
        { node := RawMolecule.canonicalRoot center left }
        { node := RawMolecule.canonicalRoot center right }

/-- Complete Rule-6 occurrence comparison with a fully authoritative auxiliary environment. -/
def compareOccurrenceBranchesThroughRule6FullyAuthoritative? (mol : RawMolecule)
    (fuel center reference left right : ℕ) : Option Rule6TrackedDecision :=
  match buildOccurrenceAuxStateFullyAuthoritative? mol fuel center with
  | none => none
  | some aux =>
      compareOccurrenceBranchesThroughRule6Complete? mol aux reference (mol.atomCount + 1)
        { node := RawMolecule.canonicalRoot center left }
        { node := RawMolecule.canonicalRoot center right }

/-- Public Rule-6 occurrence comparison routed through fully authoritative occurrence semantics. -/
def compareOccurrenceBranchesThroughRule6? (mol : RawMolecule)
    (fuel center reference left right : ℕ) : Option Rule6TrackedDecision :=
  compareOccurrenceBranchesThroughRule6FullyAuthoritative? mol fuel center reference left right

/-- Rules 1--5 decide normally. Only a non-equal reference promotion is Rule-6 `±2`. -/
def compareBranchesThroughRule6Tracked?
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center reference left right : ℕ) :
    Option Rule6TrackedDecision :=
  let projected :=
    match compareBranchesBeforeRule6Context? result mol state fuel center left right with
    | some Ordering.lt => some { ordering := Ordering.lt, pseudo := false }
    | some Ordering.gt => some { ordering := Ordering.gt, pseudo := false }
    | some Ordering.eq =>
        (compareRule6Promotion? mol fuel center reference left right).map fun ordering =>
          { ordering := ordering, pseudo := ordering != Ordering.eq }
    | none => none
  match compareOccurrenceBranchesThroughRule6? mol fuel center reference left right with
  | some decision => if decision.ordering == Ordering.eq then projected else some decision
  | none => projected

/-- Insert one ligand while tracking top-level Rule-6 `±2` comparisons. -/
def insertBranchPositionRule6Tracked
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center reference : ℕ) (ligands : List ℕ)
    (candidate : ℕ) : List ℕ → Option (List ℕ × ℕ × Bool)
  | [] => some ([candidate], 0, true)
  | low :: remaining => do
      let decision ← compareBranchesThroughRule6Tracked? result mol state fuel center reference
        (ligands.getD low 0) (ligands.getD candidate 0)
      let observed := if decision.pseudo then 1 else 0
      match decision.ordering with
      | Ordering.lt =>
          let deeper ← insertBranchPositionRule6Tracked result mol state fuel center reference
            ligands candidate remaining
          some (low :: deeper.1, observed + deeper.2.1, deeper.2.2)
      | Ordering.eq => some (candidate :: low :: remaining, observed, false)
      | Ordering.gt => some (candidate :: low :: remaining, observed, true)

/-- Result of one fresh stable Rule-6 sort. -/
structure Rule6TrackedRanking where
  positions : List ℕ
  unique : Bool
  pseudoComparisons : ℕ
  deriving DecidableEq, Repr

/-- Stable Rule-6 insertion sort from the order established by the preceding sort. -/
def rankBranchPositionsThroughRule6Tracked?
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center reference : ℕ) (ligands start : List ℕ) :
    Option Rule6TrackedRanking := do
  let tracked ← start.foldlM (fun accumulator candidate => do
    let inserted ← insertBranchPositionRule6Tracked result mol state fuel center reference
      ligands candidate accumulator.1
    some (inserted.1, accumulator.2.1 + inserted.2.1,
      accumulator.2.2 && inserted.2.2)) ([], 0, true)
  some { positions := tracked.1.reverse
         pseudoComparisons := tracked.2.1
         unique := tracked.2.2 }

/-- Rule-6 references in the undifferentiated group selected by edge 1.

For the only admitted two-group partitions this is the complete first group in `aaa|b` and
`aa|bb`, or the complete second group in `a|bbb`.  Edge 1 is tested first to preserve the
reference algorithm's carrier order; the remaining symmetry-equivalent choices are consistency
witnesses. -/
def rule6EquivalentReferencePositions (sorted : List ℕ)
    (adjacent : List (Option Ordering)) : List ℕ :=
  let positionAt := fun index => sorted.getD index 0
  if adjacent.getD 0 none == some Ordering.gt then
    [positionAt 1, positionAt 2, positionAt 3]
  else if adjacent.getD 1 none == some Ordering.gt then
    [positionAt 1, positionAt 0]
  else
    [positionAt 1, positionAt 2, positionAt 0]

/-- A Rule-6 promotion is independent of the arbitrary choice of a symmetry-equivalent reference.

Every choice must produce a strict ranking, and all resulting carrier permutations must have the
same descriptor.  Returning the first ranking retains the prescribed in-place order only after
the remaining choices prove that it is topology-invariant. -/
def rankRule6EquivalentReferences?
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : ℕ) (parity : TetrahedralInputParity)
    (ligands sorted references : List ℕ) : Option Rule6TrackedRanking := do
  let firstReferencePosition ← references.head?
  let first ← rankBranchPositionsThroughRule6Tracked? result mol state fuel center
    (ligands.getD firstReferencePosition 0) ligands sorted
  if !first.unique then none else
  let descriptor := RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven first.positions)
  let consistent ← references.drop 1 |>.allM fun referencePosition => do
    let ranking ← rankBranchPositionsThroughRule6Tracked? result mol state fuel center
      (ligands.getD referencePosition 0) ligands sorted
    some (ranking.unique &&
      RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven ranking.positions) == descriptor)
  if consistent then some first else none

/-- Whether the pre-Rule-6 ligand partition admits an orientation-reversing constitutional
automorphism of the whole molecule.

Rule 6 may sequence duplicate-node topology only when that topology has a well-defined handed
carrier.  Pairwise root mappings are insufficient for this check: a chiral `S4` cage can map every
root to every other root using only even permutations.  Instead, seed the complete molecular
automorphism search with each odd permutation of the four ligand roots, retaining only
permutations that preserve the Rule-1--5 partition.

The result is tri-state. `some true` carries a checked odd automorphism, `some false` means every
admissible odd root permutation was exhaustively disproved, and `none` is reserved for a malformed
ligand frame.  Every admissible permutation uses complete seeded backtracking: the greedy
large-component witness search is sound when it succeeds but cannot prove absence, so it is not
used to establish a handed carrier. -/
def hasOddConstitutionAutomorphismAtCenter (mol : RawMolecule) (center : ℕ)
    (ligands : List ℕ) (sameGroup : ℕ → ℕ → Bool) : Option Bool :=
  if ligands.length != 4 then none else
  let mancudeEdges := mol.localizedMancudeEdges
  let vertices :=
    (mol.reachableAvoiding (mol.atomCount + 1) mol.atomCount [center] [center] ++
      center :: ligands).eraseDups
  (KernelPermutationEnumeration.kernelPermutations (List.range 4)).foldl (fun status permutation =>
    if status == some true || RawMolecule.permutationIsEven permutation ||
        !(List.range 4).all (fun index => sameGroup index (permutation.getD index 0)) then
      status
    else
      let ligandMapping := (List.range 4).map fun index =>
        (ligands.getD index 0, ligands.getD (permutation.getD index 0) 0)
      let seed := (center, center) :: ligandMapping
      let seedValid := seed.all fun pair =>
        mol.sameConstitutionAtom pair.1 pair.2 &&
          mol.constitutionMappingConsistent mancudeEdges (seed.erase pair) pair.1 pair.2
      if !seedValid then status else
        let remaining := vertices.filter fun atom => !(seed.map Prod.fst).contains atom
        if mol.searchConstitutionAutomorphismExact mancudeEdges vertices remaining seed then
          some true
        else status) (some false)

/-- Rules 1--5 comparison used to form the undifferentiated ligand partition before Rule 6.

The canonical compiler can be operationally inconclusive on a cyclic opening even when the two
roots have the same constitution.  Rule 6 is specifically the fallthrough for those cyclic ties,
so they remain in one partition; unrelated inconclusive comparisons are not silently equated. -/
def compareBranchesBeforeRule6? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center left right : ℕ) : Option Ordering :=
  compareBranchesBeforeRule6Context? result mol state fuel center left right

/-- Certified result of the special four-way `S4` Rule-6 path. -/
structure Rule6FourWayAgreement where
  firstRanking : Rule6TrackedRanking
  secondRanking : Rule6TrackedRanking
  /-- Descriptor after quotienting the artificial promoted edge when both rankings remain
  nonunique. -/
  descriptor : RS
  deriving DecidableEq, Repr

/-- Perform the two in-place promotions required by the four-way `S4` case and retain a result only
when their carrier orders differ, their molecular-root descriptors agree, and their uniqueness
status agrees. -/
def rankRule6FourWayReferences?
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : ℕ) (parity : TetrahedralInputParity)
    (ligands sorted : List ℕ) : Option Rule6FourWayAgreement := do
  let firstPosition ← sorted[0]?
  let firstRanking ← rankBranchPositionsThroughRule6Tracked? result mol state fuel center
    (ligands.getD firstPosition 0) ligands sorted
  let firstOrder := firstRanking.positions
  let secondReference := ligands.getD (firstOrder.getD 1 0) 0
  let secondRanking ← rankBranchPositionsThroughRule6Tracked? result mol state fuel center
    secondReference ligands firstOrder
  let secondOrder := secondRanking.positions
  let firstDescriptor := RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven firstOrder)
  let secondDescriptor := RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven secondOrder)
  if firstOrder != secondOrder && firstDescriptor == secondDescriptor &&
      firstRanking.unique == secondRanking.unique then
    some { firstRanking := firstRanking
           secondRanking := secondRanking
           descriptor := if secondRanking.unique then secondDescriptor else RS.swap secondDescriptor }
  else none

/-- Three-valued constitutional perception for an ordinary tetrahedral center.

`notCandidate` is reserved for atoms outside the supported ordinary four-ligand domain.  Within
that domain, failure of a bounded comparison or of a Rule-6 consistency check is `unresolved`, not
chemical nonstereogenicity. -/
inductive TetrahedralStereogenicity where
  | stereogenic
  | notStereogenic
  | unresolved
  | notCandidate
  deriving DecidableEq, Repr

/-- Descriptor-independent Rule-6 perception.

The arbitrary `clockwise` parity is used only inside consistency checks.  Reversing that parity
swaps every candidate `R/S` result simultaneously and therefore cannot change whether all
symmetry-equivalent promotions agree. -/
def tetrahedralRule6Stereogenicity? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel idx : ℕ) : Option Bool :=
  let ligands := mol.ligandsWithLonePair idx
  if ligands.length != 4 then none else
    let atomOf := fun position => ligands.getD position 0
    let uncachedCompareAt := fun left right =>
      compareBranchesBeforeRule6? result mol state fuel idx (atomOf left) (atomOf right)
    let comparisonCache := cachePositionComparisons ligands.length uncachedCompareAt
    let compareAt := cachedPositionComparison? comparisonCache
    let before := fun left right => compareAt left right != some Ordering.lt
    let sorted := sortDescBy before (List.range ligands.length)
    let adjacent := (List.range (sorted.length - 1)).map fun rank =>
      match sorted[rank]?, sorted[rank + 1]? with
      | some left, some right => compareAt left right
      | _, _ => none
    if !(adjacent.all Option.isSome) then none else
      let groupCount := 1 + (adjacent.filter fun verdict =>
        verdict == some Ordering.gt).length
      let group3HasLocalReference :=
        adjacent.getD 1 none == some Ordering.eq &&
          (branchDescriptorSequence mol state idx
            (atomOf (sorted.getD 1 0))).any fun fact => fact.evidenceSize != 0
      let oddTopologySymmetry? :=
        hasOddConstitutionAutomorphismAtCenter mol idx ligands fun left right =>
          compareAt left right == some Ordering.eq
      match oddTopologySymmetry? with
      | some true => some false
      | none => none
      | some false =>
          if groupCount == 1 then
            match rankRule6FourWayReferences? result mol state fuel idx
                TetrahedralInputParity.clockwise ligands sorted with
            | some _ => some true
            | none => none
          else if groupCount == 2 || (groupCount == 3 && group3HasLocalReference) then
            let references :=
              if groupCount == 2 then rule6EquivalentReferencePositions sorted adjacent
              else [sorted.getD 1 0]
            match rankRule6EquivalentReferences? result mol state fuel idx
                TetrahedralInputParity.clockwise ligands sorted references with
            | some _ => some true
            | none => none
          else
            some false

/-- Rule-6 result after the reference-promotion consistency test.

After Rule 5 there must be either two ligand groups (`aabb` or `aaab`) or one four-ligand group.  In
the two-group case one member of the first undifferentiated group is promoted.  In the four-way case
two different promotions must produce the same handedness; opposite outcomes identify an achiral
high-symmetry center and are rejected. -/
def tetrahedralFactThroughRule6? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel idx : ℕ) : Option RawDescriptorFact :=
  match mol.atomAt? idx with
  | some spec =>
      match spec.tetrahedral? with
      | some parity =>
          let ligands := mol.ligandsWithLonePair idx
          if ligands.length != 4 then none else
            let atomOf := fun position => ligands.getD position 0
            let uncachedCompareAt := fun left right =>
              compareBranchesBeforeRule6? result mol state fuel idx
              (atomOf left) (atomOf right)
            let comparisonCache := cachePositionComparisons ligands.length uncachedCompareAt
            let compareAt := cachedPositionComparison? comparisonCache
            let before := fun left right => compareAt left right != some Ordering.lt
            let sorted := sortDescBy before (List.range ligands.length)
            let adjacent := (List.range (sorted.length - 1)).map fun rank =>
              match sorted[rank]?, sorted[rank + 1]? with
              | some left, some right => compareAt left right
              | _, _ => none
            if !(adjacent.all Option.isSome) then none else
              let groupCount := 1 + (adjacent.filter fun verdict =>
                verdict == some Ordering.gt).length
              -- A three-group partition has one tied pair.  Rule 6 may promote edge 1 only when
              -- that is the tied boundary and its reference branch actually contains established
              -- descriptor-dependent evidence.  Remote annotations cannot enable the promotion.
              let group3HasLocalReference :=
                adjacent.getD 1 none == some Ordering.eq &&
                  (branchDescriptorSequence mol state idx
                    (atomOf (sorted.getD 1 0))).any fun fact => fact.evidenceSize != 0
              let oddTopologySymmetry? :=
                hasOddConstitutionAutomorphismAtCenter mol idx ligands fun left right =>
                  compareAt left right == some Ordering.eq
              -- Rule 6 needs proof that no partition-preserving odd automorphism exists.
              if oddTopologySymmetry? != some false then none else if groupCount == 1 then
                -- In the four-way S4 case, the first two possible promotions must induce the
                -- same handedness.  An odd change of ordering is an achiral high-symmetry cage.
                match rankRule6FourWayReferences? result mol state fuel idx parity ligands sorted with
                | some agreement =>
                    -- The helper retains the prescribed in-place second order and performs the
                    -- odd quotient exactly when both individual rankings remain nonunique.
                    some { atom := idx,
                           descriptor := agreement.descriptor,
                           uppercase := agreement.secondRanking.pseudoComparisons != 1,
                           evidenceSize := 2,
                           priorityPositions := agreement.secondRanking.positions }
                | none => none
              else if groupCount == 2 || (groupCount == 3 && group3HasLocalReference) then
                -- Rule 6 promotes edge 1 of the Rule-1--5 sorted edge list.  This handles both
                -- `aa|bb` and `a|bbb`: searching for the first adjacent tie incorrectly chooses
                -- the third edge in the latter partition.
                let references :=
                  if groupCount == 2 then rule6EquivalentReferencePositions sorted adjacent
                  else [sorted.getD 1 0]
                match rankRule6EquivalentReferences? result mol state fuel idx parity ligands sorted
                    references with
                | some ranking =>
                  if ranking.unique then
                    some { atom := idx,
                           descriptor :=
                             let value := RawMolecule.descriptorOfParity parity
                               (RawMolecule.permutationIsEven ranking.positions)
                             if groupCount == 3 then RS.swap value else value,
                           uppercase := groupCount == 3 || ranking.pseudoComparisons != 1,
                           evidenceSize := 1,
                           priorityPositions := ranking.positions }
                  else none
                | none => none
              else none
      | none => none
  | none => none

/-- Insert one ligand into a reversed (lowest-to-highest) priority list while recording the later
sequence-rule comparisons performed by the CIP insertion sort.

Pseudoasymmetry depends on the number of actual `±2` comparisons made by this sort, not on all
pairwise comparisons and not merely on the adjacent pairs in the finished order. -/
def insertBranchPositionTracked (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : ℕ) (ligands : List ℕ) (candidate : ℕ) :
    List ℕ → List ℕ × List CIPRuleFamily
  | [] => ([candidate], [])
  | low :: remaining =>
      let lowAtom := ligands.getD low 0
      let candidateAtom := ligands.getD candidate 0
      let family := decisiveOfficialFamilyForBranches? result mol state fuel center
        lowAtom candidateAtom
      let observed := family.toList
      match compareBranchesThroughOfficialContext? result mol state fuel center
          lowAtom candidateAtom with
      | some Ordering.lt =>
          let deeper := insertBranchPositionTracked result mol state fuel center ligands candidate
            remaining
          (low :: deeper.1, observed ++ deeper.2)
      | _ => (candidate :: low :: remaining, observed)

/-- Sequence-rule families observed by the same stable insertion sort used by the reference
algorithm.  The maintained order is reversed so insertion starts at the current low-priority end. -/
def insertionSortDependentFamilies (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : ℕ) (ligands : List ℕ) : List CIPRuleFamily :=
  let tracked := (List.range ligands.length).foldl (fun accumulator candidate =>
    let inserted := insertBranchPositionTracked result mol state fuel center ligands candidate
      accumulator.1
    (inserted.1, accumulator.2 ++ inserted.2)) ([], [])
  tracked.2

/-- Insert one ligand while counting enantiomorphic revised-Rule-5 comparisons. -/
def insertBranchPositionRule5Tracked (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : ℕ) (ligands : List ℕ) (candidate : ℕ) :
    List ℕ → List ℕ × ℕ
  | [] => ([candidate], 0)
  | low :: remaining =>
      let lowAtom := ligands.getD low 0
      let candidateAtom := ligands.getD candidate 0
      let family := decisiveOfficialFamilyForBranches? result mol state fuel center
        lowAtom candidateAtom
      let pseudo :=
        if family == some CIPRuleFamily.pseudoasymmetricTiebreak then
          match compareRule5Recursive? mol state center lowAtom candidateAtom with
          | some comparison => comparison.pseudo
          | none => false
        else false
      let observed := if pseudo then 1 else 0
      match compareBranchesThroughOfficialContext? result mol state fuel center
          lowAtom candidateAtom with
      | some Ordering.lt =>
          let deeper := insertBranchPositionRule5Tracked result mol state fuel center ligands
            candidate remaining
          (low :: deeper.1, observed + deeper.2)
      | _ => (candidate :: low :: remaining, observed)

/-- Number of revised-Rule-5 `±2` comparisons made by the actual ligand insertion sort. -/
def insertionSortRule5PseudoCount (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : ℕ) (ligands : List ℕ) : ℕ :=
  let tracked := (List.range ligands.length).foldl (fun accumulator candidate =>
    let inserted := insertBranchPositionRule5Tracked result mol state fuel center ligands candidate
      accumulator.1
    (inserted.1, accumulator.2 + inserted.2)) ([], 0)
  tracked.2

/-- Nearest unambiguous lowercase descriptor occurrence after re-rooting away from a center. -/
def nearestLowercaseOccurrenceSense? (mol : RawMolecule) (state : RawDescriptorState)
    (center : ℕ) : Option RS :=
  let rec search : ℕ → List CanonicalRerootCursor → Option RS
    | 0, _ => none
    | _ + 1, [] => none
    | fuel + 1, frontier =>
        let senses := (frontier.filterMap fun cursor =>
          match cursor.node.provenance, state.factAt? cursor.node.atom with
          | RawMolecule.CanonicalNodeProvenance.realAtom, some fact =>
              if fact.atom == center || fact.uppercase then none
              else some (rawAuxiliaryOccurrenceSense mol cursor.node fact)
          | _, _ => none).eraseDups
        match senses with
        | [sense] => some sense
        | [] => search fuel (frontier.flatMap fun cursor => cursor.children mol)
        | _ => none
  search (mol.atomCount + 1) (({ node := canonicalCenterRoot center } : CanonicalRerootCursor).children mol)

def tetrahedralFactFromProjectedState? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (_maxEvidenceSize fuel idx : ℕ) : Option RawDescriptorFact :=
  match mol.atomAt? idx with
  | some spec =>
      match spec.tetrahedral? with
      | some parity =>
          if !RawMolecule.centreElementSupported spec.element then
            none
          else
          let ligands := mol.ligandsWithLonePair idx
          if ligands.length != 4 then none else
          match rankBranchPositionsThroughOfficialContext? result mol state fuel idx ligands with
          | some positions =>
              let dependentFamilies := insertionSortDependentFamilies result mol state fuel idx
                ligands
              let evidenceSize := ligands.foldl (fun largest ligand =>
                Nat.max largest (branchDescriptorSequence mol state idx ligand).length) 0
              -- A tetrahedral result is pseudoasymmetric exactly when one ligand comparison was
              -- decided by Rule 5.  Two or more enantiomorphic comparisons restore an uppercase
              -- chiral descriptor; Rules 3, 4a, 4b, and 4c themselves do not lowercase the root.
              let pseudoComparisons := insertionSortRule5PseudoCount result mol state fuel idx ligands
              let rule4cCarrier :=
                if dependentFamilies.head? == some CIPRuleFamily.pseudoasymmetricDescriptor &&
                    dependentFamilies.length == 1 then
                  nearestLowercaseOccurrenceSense? mol state idx
                else none
              let inheritsHydrogenRule6Reference :=
                (ligands.any fun ligand => result.parsed.atomCount ≤ ligand) &&
                  state.any fun fact => !fact.uppercase && fact.evidenceSize == 1 &&
                    fact.decisiveRule?.isNone
              let uppercase := !inheritsHydrogenRule6Reference && pseudoComparisons != 1 &&
                rule4cCarrier.isNone
              let rawDescriptor := RawMolecule.descriptorOfParity parity
                (RawMolecule.permutationIsEven positions)
              if evidenceSize == 0 && !dependentFamilies.isEmpty then none else some
                { atom := idx
                  descriptor :=
                    if rule4cCarrier == some RS.S then RS.swap rawDescriptor else rawDescriptor
                  uppercase := uppercase
                  evidenceSize := evidenceSize
                  decisiveRule? := dependentFamilies.head?
                  descriptorDependentPairs := dependentFamilies.length
                  priorityPositions := positions }
          | none => tetrahedralFactThroughRule6? result mol state fuel idx
      | none => none
  | none => none

/-- Rules whose projected comparison is only an approximation to the occurrence-local auxiliary
digraph required by Rules 4a--5.  Rule 3 and Rule 6 deliberately do not enter this predicate: their
geometry and promoted-reference constructions are already expressed at the molecular root. -/
def isDescriptorHierarchyRule : CIPRuleFamily → Bool
  | .stereogenicUnitKind
  | .likeUnlikeDescriptorPair
  | .pseudoasymmetricDescriptor
  | .pseudoasymmetricTiebreak => true
  | _ => false

/-- Prefer the exact occurrence-local Rules 4a--5 result exactly when the projected fixed-point
comparison says that one of those rules was decisive.  The projected result remains a bounded
fallback when compiling the occurrence digraph is inconclusive. -/
def preferOccurrenceDescriptorHierarchy (projected occurrence : Option RawDescriptorFact) :
    Option RawDescriptorFact :=
  match projected with
  | some fact =>
      if fact.decisiveRule?.any isDescriptorHierarchyRule then
        Option.first occurrence projected
      else projected
  | none => occurrence

/-- One cyclic Rule-6 anchor uniquely reached from a ligand of an acyclic carrier. -/
structure RootedCyclicAnchorWitness where
  position : ℕ
  target : ℕ
  parent : ℕ
  distance : ℕ
  carrierOdd : Bool
  deriving DecidableEq, Repr

/-- Select an item only when its distance is strictly smaller than every alternative. -/
def uniqueNearestBy? {α : Type} (distance : α → ℕ) (candidates : List α) : Option α :=
  let ordered := sortDescBy (fun left right => distance left ≤ distance right) candidates
  match ordered with
  | [] => none
  | [first] => some first
  | first :: second :: _ => if distance first < distance second then some first else none

/-- Exact two-anchor occurrence-frame witness used to accept an odd-root projected Rule-5 fact.

The witness is local and topology-based: two distinct cyclic Rule-6 anchors must be the unique
nearest annotated occurrences on adjacent tied ligand positions at equal distance.  Each stored
four-ligand order must define a valid incoming-edge promotion.  Acyclic linkers on the paths are
allowed; the uniquely identified target stereogenic units themselves must be cyclic. -/
def exactTwoCyclicAnchorCarrierWitness? (mol : RawMolecule) (state : RawDescriptorState)
    (fuel center : ℕ) (projected : RawDescriptorFact) : Option Bool := do
  if projected.uppercase ||
      projected.decisiveRule? != some CIPRuleFamily.pseudoasymmetricTiebreak ||
      projected.descriptorDependentPairs != 1 || mol.atomLiesInCycle fuel center then none else
  let anchors := state.filter fun anchor =>
    anchor.atom != center && anchor.uppercase && anchor.evidenceSize == 1 &&
      anchor.decisiveRule?.isNone && mol.atomLiesInCycle fuel anchor.atom
  let ligands := mol.ligandsWithLonePair center
  let witnessAt := fun entry : ℕ × ℕ => do
    let nearest ← uniqueNearestBy? (fun candidate : RawDescriptorFact × ℕ => candidate.2)
      (anchors.filterMap fun anchor =>
        (mol.rule6ReferenceDistance? center anchor.atom fuel 0 [entry.1]
          [center, entry.1]).map fun distance => (anchor, distance))
    let anchor := nearest.1
    let incoming ← uniqueNearestBy? (fun candidate : ℕ × ℕ => candidate.2)
      ((mol.ligandsWithLonePair anchor.atom).filterMap fun parent =>
        (mol.rule6ReferenceDistance? anchor.atom center fuel 0 [parent]
          [anchor.atom, parent]).map fun distance => (parent, distance))
    let targetLigands := mol.ligandsWithLonePair anchor.atom
    if targetLigands.length != 4 || anchor.priorityPositions.length != 4 ||
        anchor.priorityPositions.eraseDups.length != 4 ||
        !(anchor.priorityPositions.all fun position => position < targetLigands.length) then
      none
    else
      let parentEntry ← targetLigands.zipIdx.find? fun targetEntry =>
        targetEntry.1 == incoming.1
      let occurrenceOrder := parentEntry.2 :: anchor.priorityPositions.erase parentEntry.2
      if occurrenceOrder.length != 4 then none else
      some ({ position := entry.2, target := anchor.atom, parent := incoming.1,
              distance := nearest.2,
              carrierOdd := RawMolecule.permutationIsEven occurrenceOrder !=
                RawMolecule.permutationIsEven anchor.priorityPositions } :
        RootedCyclicAnchorWitness)
  let witnesses := ligands.zipIdx.filterMap witnessAt
  match witnesses with
  | [left, right] =>
    let adjacent :=
      match projected.priorityPositions.idxOf? left.position,
          projected.priorityPositions.idxOf? right.position with
      | some leftRank, some rightRank => leftRank + 1 == rightRank || rightRank + 1 == leftRank
      | _, _ => false
    if left.target != right.target && left.distance == right.distance && adjacent then
      some (left.carrierOdd == right.carrierOdd)
    else none
  | _ => none

/-- Descriptor-dependent assignment using the center-specific auxiliary digraph when Rule 3 is not
in play.  Geometry-bearing comparisons retain the established Rule-3-aware path; cyclic Rules
4a--5 use occurrence-local labels and fall back only when the bounded tree cannot be compiled. -/
def tetrahedralFactFromState? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (maxEvidenceSize fuel idx : ℕ) : Option RawDescriptorFact :=
  -- Descriptor discovery visits molecule indices repeatedly.  Reject non-centres before compiling
  -- their occurrence trees: the latter can contain hundreds of ring-duplicate nodes in a fused
  -- system even though `tetrahedralFactFromProjectedState?` must ultimately return `none`.
  match result.parsed.atomAt? idx with
  | none => none
  | some spec =>
    if spec.tetrahedral?.isNone then none else
    let ligands := mol.ligandsWithLonePair idx
    let occurrence := tetrahedralOccurrenceFact? mol fuel idx
    let hasRule3Geometry := (mol.ligandsWithLonePair idx).any fun ligand =>
      !(result.rule3GeometrySequenceOnBranch mol idx ligand).isEmpty
    let hasLocalDescriptorEvidence := ligands.any fun ligand =>
      !(branchDescriptorSequence mol state idx ligand).isEmpty
    let blockedByUnlabeledAutomorphism :=
      if !hasRule3Geometry && !hasLocalDescriptorEvidence then
        let hasUnlabeledAutomorphicPair :=
          (List.range ligands.length).any fun leftIndex =>
            (List.range ligands.length).any fun rightIndex =>
              leftIndex < rightIndex &&
                mol.hasConstitutionAutomorphismSwapping idx
                  (ligands.getD leftIndex 0) (ligands.getD rightIndex 0)
        hasUnlabeledAutomorphicPair &&
          (tetrahedralFactThroughRule6? result mol state fuel idx).isNone
      else false
    -- An exact constitutional automorphism proves a tie only while no local stereogenic-unit or
    -- geometry evidence breaks it.  This is deliberately local: adding a remote annotation or an
    -- unrelated disconnected fragment must not change the decision at this center.
    if blockedByUnlabeledAutomorphism then
      none
    -- Once the unlabeled-automorphism refusal above has been discharged, a strict descriptor-
    -- bearing occurrence fact at a cyclic non-Rule-3 center is the result in both remaining
    -- symmetry cases.  The odd branch returns it directly; the non-odd cyclic selector prefers it
    -- over every projected fact.  Return it before running the otherwise redundant whole-molecule
    -- odd-automorphism search, which is especially expensive in recursive Rule-5 systems.
    else if !hasRule3Geometry && mol.atomLiesInCycle fuel idx &&
        occurrence.any (fun fact => fact.descriptorDependentPairs != 0) then
      occurrence
    else
    let uncachedCompareBeforeRule6 := fun left right =>
      compareBranchesBeforeRule6? result mol [] fuel idx
        (ligands.getD left 0) (ligands.getD right 0)
    let comparisonCache := cachePositionComparisons ligands.length uncachedCompareBeforeRule6
    let compareBeforeRule6 := cachedPositionComparison? comparisonCache
    let oddConstitutionalSymmetry? :=
      hasOddConstitutionAutomorphismAtCenter mol idx ligands fun left right =>
        compareBeforeRule6 left right == some Ordering.eq
    let projected := tetrahedralFactFromProjectedState? result mol state maxEvidenceSize fuel idx
    -- An odd root permutation defeats molecular-root projection, but it does not defeat a strict
    -- comparison proved in the exact occurrence-local auxiliary digraph.  The latter transports
    -- the collective descriptor carrier explicitly (VS296--VS298); accepting projected evidence
    -- here would instead let provisional root labels manufacture chirality in achiral cages.
    -- A proved odd automorphism makes molecular-root projection unsound.  Exact occurrence-local
    -- evidence remains independently valid; `none` is conservatively treated the same way.
    if oddConstitutionalSymmetry? != some false then
      match occurrence with
      | some fact => if fact.descriptorDependentPairs != 0 then occurrence else none
      | none =>
        match projected with
        | some fact =>
          if (exactTwoCyclicAnchorCarrierWitness? mol state fuel idx fact).isSome then projected
          else none
        | none => none
    else
    let hierarchy := preferOccurrenceDescriptorHierarchy projected occurrence
    -- Geometry elsewhere on a ligand branch must not suppress occurrence-local Rules 4a--5.  Keep
    -- the projected path only when Rule 3 actually supplied the decisive comparison at this root.
    let rule3Decisive := projected.any fun fact =>
      fact.decisiveRule? == some CIPRuleFamily.doubleBondGeometry
    if hasRule3Geometry && rule3Decisive then projected
    else if !mol.atomLiesInCycle fuel idx then hierarchy
    else
      -- Choose by the evidence that actually decided this center.  Descriptor-hierarchy decisions
      -- use the exact occurrence-local digraph when available; topology-reference decisions retain
      -- the projected Rule-6 carrier.  If projection is inconclusive, an exact occurrence result is
      -- still admissible independently of molecule size or the number of remote annotations.
      match projected with
      | some fact =>
          if fact.decisiveRule?.any isDescriptorHierarchyRule ||
              occurrence.any fun occurrenceFact =>
                occurrenceFact.descriptorDependentPairs != 0 then
            Option.first occurrence projected
          else projected
      | none => occurrence

/-- Seed the fixed point with descriptors resolved without descriptor-dependent evidence. -/
def initialRawDescriptorState (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel : ℕ) : RawDescriptorState :=
  (List.range result.parsed.atomCount).filterMap fun idx =>
    match tetrahedralOutcomeThroughRule3 result mol fuel idx with
    | StereoOutcome.tetrahedral descriptor =>
        let positions := (rankBranchPositionsThroughRule3? result mol fuel idx
          (mol.ligandsWithLonePair idx)).getD []
        some ({ atom := idx, descriptor := descriptor, uppercase := true, evidenceSize := 0,
                priorityPositions := positions } : RawDescriptorFact)
    | _ => none

/-- Update one center during descriptor discovery.  Factoring this transition out makes traversal
order an explicit mathematical parameter rather than an implementation detail of `foldl`. -/
def updateRawDescriptorAt (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (current : RawDescriptorState) (idx : ℕ) : RawDescriptorState :=
  match current.factAt? idx with
  | some existing =>
      -- Only Rule-1--3 seed facts are final.  Every descriptor-dependent or Rule-6 fact is
      -- provisional: remove it before recomputation so that it cannot support its own ranking.
      -- A failed recomputation must really retract the old fact; later passes can rediscover it
      -- after the facts on which it depends have stabilized.
      if existing.evidenceSize == 0 then current else
      let withoutExisting := current.filter fun fact => fact.atom != idx
      match tetrahedralFactFromState? result mol withoutExisting maxEvidenceSize fuel idx with
      | some fact => RawDescriptorState.insertIfAbsent withoutExisting fact
      | none => withoutExisting
  | none =>
      match tetrahedralFactFromState? result mol current maxEvidenceSize fuel idx with
      | some fact => current.insertIfAbsent fact
      | none => current

/-- Run one descriptor-discovery pass in an explicitly supplied center order. -/
def runRawDescriptorDiscoverySchedule (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (schedule : List ℕ) (state : RawDescriptorState) :
    RawDescriptorState :=
  schedule.foldl (updateRawDescriptorAt result mol maxEvidenceSize fuel) state

/-- One left-to-right descriptor-discovery pass. -/
def runRawDescriptorDiscoveryPass (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (state : RawDescriptorState) : RawDescriptorState :=
  runRawDescriptorDiscoverySchedule result mol maxEvidenceSize fuel
    (List.range result.parsed.atomCount) state

/-- The legacy production pass is definitionally the canonical increasing-index schedule. -/
theorem runRawDescriptorDiscoveryPass_eq_schedule
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (state : RawDescriptorState) :
    runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel state =
      runRawDescriptorDiscoverySchedule result mol maxEvidenceSize fuel
        (List.range result.parsed.atomCount) state :=
  rfl

/-- Global local-confluence condition for the production center update: updating any two centers
commutes in every descriptor environment. -/
def RawDescriptorUpdatesCommute (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) : Prop :=
  ∀ state left right,
    updateRawDescriptorAt result mol maxEvidenceSize fuel
        (updateRawDescriptorAt result mol maxEvidenceSize fuel state left) right =
      updateRawDescriptorAt result mol maxEvidenceSize fuel
        (updateRawDescriptorAt result mol maxEvidenceSize fuel state right) left

/-- Updating one center respects semantic equality of descriptor environments. -/
def RawDescriptorUpdateRespectsAtomwiseEquivalence
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) : Prop :=
  ∀ {left right}, RawDescriptorState.AtomwiseEquivalent left right → ∀ center,
    RawDescriptorState.AtomwiseEquivalent
      (updateRawDescriptorAt result mol maxEvidenceSize fuel left center)
      (updateRawDescriptorAt result mol maxEvidenceSize fuel right center)

/-- Semantic local confluence: the two update orders may arrange the backing list differently, but
must associate exactly the same fact with every atom. -/
def RawDescriptorUpdatesCommuteAtomwise
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) : Prop :=
  ∀ state left right,
    RawDescriptorState.AtomwiseEquivalent
      (updateRawDescriptorAt result mol maxEvidenceSize fuel
        (updateRawDescriptorAt result mol maxEvidenceSize fuel state left) right)
      (updateRawDescriptorAt result mol maxEvidenceSize fuel
        (updateRawDescriptorAt result mol maxEvidenceSize fuel state right) left)

/-- One center update lifted to semantic descriptor states. -/
def updateSemanticRawDescriptorAt
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ)
    (respects : RawDescriptorUpdateRespectsAtomwiseEquivalence result mol maxEvidenceSize fuel)
    (state : RawDescriptorState.SemanticState) (center : ℕ) :
    RawDescriptorState.SemanticState :=
  @Quotient.map RawDescriptorState RawDescriptorState
    RawDescriptorState.atomwiseSetoid RawDescriptorState.atomwiseSetoid
    (fun raw => updateRawDescriptorAt result mol maxEvidenceSize fuel raw center)
    (fun _ _ equivalence => respects equivalence center) state

@[simp] theorem updateSemanticRawDescriptorAt_mk
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ)
    (respects : RawDescriptorUpdateRespectsAtomwiseEquivalence result mol maxEvidenceSize fuel)
    (state : RawDescriptorState) (center : ℕ) :
    updateSemanticRawDescriptorAt result mol maxEvidenceSize fuel respects
        (RawDescriptorState.semanticMk state) center =
      RawDescriptorState.semanticMk
        (updateRawDescriptorAt result mol maxEvidenceSize fuel state center) :=
  rfl

/-- Semantic local confluence is literal right-commutativity after quotienting list order. -/
theorem updateSemanticRawDescriptorAt_rightCommutative
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ)
    (respects : RawDescriptorUpdateRespectsAtomwiseEquivalence result mol maxEvidenceSize fuel)
    (commutes : RawDescriptorUpdatesCommuteAtomwise result mol maxEvidenceSize fuel) :
    RightCommutative
      (updateSemanticRawDescriptorAt result mol maxEvidenceSize fuel respects) := by
  constructor
  intro state left right
  refine Quotient.inductionOn state ?_
  intro raw
  apply Quotient.sound
  exact commutes raw left right

/-- Under local confluence, a descriptor-discovery pass is independent of every permutation of its
center traversal order. -/
theorem runRawDescriptorDiscoverySchedule_eq_of_perm
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (left right : List ℕ) (state : RawDescriptorState)
    (commutes : RawDescriptorUpdatesCommute result mol maxEvidenceSize fuel)
    (permutation : left.Perm right) :
    runRawDescriptorDiscoverySchedule result mol maxEvidenceSize fuel left state =
      runRawDescriptorDiscoverySchedule result mol maxEvidenceSize fuel right state := by
  let update := updateRawDescriptorAt result mol maxEvidenceSize fuel
  letI : RightCommutative update := ⟨commutes⟩
  exact permutation.foldl_eq state

/-- A schedule preserves semantic equality when each individual center update does. -/
theorem runRawDescriptorDiscoverySchedule_atomwiseEquivalent
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (schedule : List ℕ) (left right : RawDescriptorState)
    (respects : RawDescriptorUpdateRespectsAtomwiseEquivalence result mol maxEvidenceSize fuel)
    (equivalent : RawDescriptorState.AtomwiseEquivalent left right) :
    RawDescriptorState.AtomwiseEquivalent
      (runRawDescriptorDiscoverySchedule result mol maxEvidenceSize fuel schedule left)
      (runRawDescriptorDiscoverySchedule result mol maxEvidenceSize fuel schedule right) := by
  induction schedule generalizing left right with
  | nil => exact equivalent
  | cons center rest inductionHypothesis =>
      apply inductionHypothesis
      exact respects equivalent center

/-- Folding the quotient update is exactly quotienting the concrete scheduled result. -/
theorem foldl_updateSemanticRawDescriptorAt_mk
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (schedule : List ℕ) (state : RawDescriptorState)
    (respects : RawDescriptorUpdateRespectsAtomwiseEquivalence result mol maxEvidenceSize fuel) :
    schedule.foldl (updateSemanticRawDescriptorAt result mol maxEvidenceSize fuel respects)
        (RawDescriptorState.semanticMk state) =
      RawDescriptorState.semanticMk
        (runRawDescriptorDiscoverySchedule result mol maxEvidenceSize fuel schedule state) := by
  induction schedule generalizing state with
  | nil => rfl
  | cons center rest inductionHypothesis =>
      change rest.foldl (updateSemanticRawDescriptorAt result mol maxEvidenceSize fuel respects)
          (updateSemanticRawDescriptorAt result mol maxEvidenceSize fuel respects
            (RawDescriptorState.semanticMk state) center) = _
      rw [updateSemanticRawDescriptorAt_mk]
      exact inductionHypothesis
        (updateRawDescriptorAt result mol maxEvidenceSize fuel state center)

/-- Relational traversal-independence theorem.  If individual updates respect atom-indexed state
semantics and commute under that semantics, every permutation of a center schedule produces the
same atom-to-fact assignment even when its backing list order differs. -/
theorem runRawDescriptorDiscoverySchedule_atomwiseEquivalent_of_perm
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (left right : List ℕ) (state : RawDescriptorState)
    (respects : RawDescriptorUpdateRespectsAtomwiseEquivalence result mol maxEvidenceSize fuel)
    (commutes : RawDescriptorUpdatesCommuteAtomwise result mol maxEvidenceSize fuel)
    (permutation : left.Perm right) :
    RawDescriptorState.AtomwiseEquivalent
      (runRawDescriptorDiscoverySchedule result mol maxEvidenceSize fuel left state)
      (runRawDescriptorDiscoverySchedule result mol maxEvidenceSize fuel right state) := by
  let semanticUpdate := updateSemanticRawDescriptorAt result mol maxEvidenceSize fuel respects
  letI : RightCommutative semanticUpdate :=
    updateSemanticRawDescriptorAt_rightCommutative result mol maxEvidenceSize fuel respects commutes
  have quotientEquality :
      left.foldl semanticUpdate (RawDescriptorState.semanticMk state) =
        right.foldl semanticUpdate (RawDescriptorState.semanticMk state) :=
    permutation.foldl_eq (RawDescriptorState.semanticMk state)
  rw [foldl_updateSemanticRawDescriptorAt_mk result mol maxEvidenceSize fuel left state respects,
    foldl_updateSemanticRawDescriptorAt_mk result mol maxEvidenceSize fuel right state respects]
    at quotientEquality
  exact Quotient.exact quotientEquality

/-- Iterate descriptor discovery to a molecule-size bound, stopping at the first fixed point. -/
def discoverRawDescriptorsFrom (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) : ℕ → RawDescriptorState → RawDescriptorState
  | 0, state => state
  | remaining + 1, state =>
      let next := runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel state
      if next == state then state else
        discoverRawDescriptorsFrom result mol maxEvidenceSize fuel remaining next

/-- Reachability along the actual deterministic production pass from an explicit seed. -/
def RawDescriptorReachableFrom (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (seed state : RawDescriptorState) : Prop :=
  DeterministicReachable
    (runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel) seed state

/-- A fixed point on the production orbit from a specified seed. -/
def IsReachableRawDescriptorFixedPoint (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (maxEvidenceSize fuel : ℕ)
    (seed state : RawDescriptorState) : Prop :=
  RawDescriptorReachableFrom result mol maxEvidenceSize fuel seed state ∧
    runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel state = state

/-- Every bounded production iteration returns a state on the deterministic orbit of its input
seed, whether it stabilizes early or exhausts the supplied iteration budget. -/
theorem discoverRawDescriptorsFrom_reachable
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel remaining : ℕ) (state : RawDescriptorState) :
    RawDescriptorReachableFrom result mol maxEvidenceSize fuel state
      (discoverRawDescriptorsFrom result mol maxEvidenceSize fuel remaining state) := by
  induction remaining generalizing state with
  | zero => exact DeterministicReachable.refl state
  | succ remaining inductionHypothesis =>
      simp only [discoverRawDescriptorsFrom]
      split
      · exact DeterministicReachable.refl state
      · exact DeterministicReachable.from_next (inductionHypothesis _)

/-- A constructive descriptor-discovery run records whether it reached a literal fixed point before
its explicit iteration budget was exhausted. -/
structure RawDescriptorDiscoveryRun where
  state : RawDescriptorState
  stabilized : Bool
  deriving DecidableEq, Repr

/-- Certified companion to `discoverRawDescriptorsFrom`.

The state transition and stopping test are identical to the production iterator.  The additional
bit prevents a fuel-exhausted approximation from being mistaken for a fixed point. -/
def discoverRawDescriptorsFromCertified (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (maxEvidenceSize fuel : ℕ) :
    ℕ → RawDescriptorState → RawDescriptorDiscoveryRun
  | 0, state => { state := state, stabilized := false }
  | remaining + 1, state =>
      let next := runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel state
      if next == state then { state := state, stabilized := true } else
        discoverRawDescriptorsFromCertified result mol maxEvidenceSize fuel remaining next

/-- The certified iterator computes exactly the same state as the production iterator. -/
theorem discoverRawDescriptorsFromCertified_state
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel remaining : ℕ) (state : RawDescriptorState) :
    (discoverRawDescriptorsFromCertified result mol maxEvidenceSize fuel remaining state).state =
      discoverRawDescriptorsFrom result mol maxEvidenceSize fuel remaining state := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
      simp only [discoverRawDescriptorsFromCertified, discoverRawDescriptorsFrom]
      split
      · rfl
      · exact ih _

/-- A run marked as stabilized ends at a literal fixed point of the constructive pass. -/
theorem discoverRawDescriptorsFromCertified_fixed_of_stabilized
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel remaining : ℕ) (state : RawDescriptorState)
    (stabilized :
      (discoverRawDescriptorsFromCertified result mol maxEvidenceSize fuel remaining state).stabilized =
        true) :
    runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel
        (discoverRawDescriptorsFromCertified result mol maxEvidenceSize fuel remaining state).state =
      (discoverRawDescriptorsFromCertified result mol maxEvidenceSize fuel remaining state).state := by
  induction remaining generalizing state with
  | zero => simp [discoverRawDescriptorsFromCertified] at stabilized
  | succ remaining ih =>
      simp only [discoverRawDescriptorsFromCertified] at stabilized ⊢
      split <;> rename_i fixed
      · simpa using fixed
      · apply ih
        simpa [fixed] using stabilized

/-- Return a constructive result only when the bounded run actually reaches a fixed point. -/
def stabilizedRawDescriptorState? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel remaining : ℕ) (state : RawDescriptorState) :
    Option RawDescriptorState :=
  let run := discoverRawDescriptorsFromCertified result mol maxEvidenceSize fuel remaining state
  if run.stabilized then some run.state else none

/-- Every state returned by the stabilization gate is idempotent under another constructive pass. -/
theorem stabilizedRawDescriptorState_fixed
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel remaining : ℕ) (state fixed : RawDescriptorState)
    (accepted :
      stabilizedRawDescriptorState? result mol maxEvidenceSize fuel remaining state = some fixed) :
    runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel fixed = fixed := by
  dsimp [stabilizedRawDescriptorState?] at accepted
  split at accepted <;> rename_i stabilized
  · have fixedEq := Option.some.inj accepted
    rw [← fixedEq]
    apply discoverRawDescriptorsFromCertified_fixed_of_stabilized
    simpa using stabilized
  · simp at accepted


theorem stabilizedRawDescriptorState_reachable
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel remaining : ℕ) (state fixed : RawDescriptorState)
    (accepted :
      stabilizedRawDescriptorState? result mol maxEvidenceSize fuel remaining state = some fixed) :
    RawDescriptorReachableFrom result mol maxEvidenceSize fuel state fixed := by
  dsimp [stabilizedRawDescriptorState?] at accepted
  split at accepted <;> rename_i stabilized
  · have fixedEq := Option.some.inj accepted
    rw [← fixedEq, discoverRawDescriptorsFromCertified_state]
    exact discoverRawDescriptorsFrom_reachable result mol maxEvidenceSize fuel remaining state
  · simp at accepted

/-- Reachable-state uniqueness for the production descriptor pass.  Among all states on the orbit
of one seed, at most one can be a fixed point, even though provisional facts may be retracted and
the pass is not monotone on arbitrary raw states. -/
theorem reachableRawDescriptorFixedPoint_unique
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (seed left right : RawDescriptorState)
    (leftFixed :
      IsReachableRawDescriptorFixedPoint result mol maxEvidenceSize fuel seed left)
    (rightFixed :
      IsReachableRawDescriptorFixedPoint result mol maxEvidenceSize fuel seed right) :
    left = right := by
  exact DeterministicReachable.fixedPoint_unique
    leftFixed.1 rightFixed.1 leftFixed.2 rightFixed.2

/-- Reachable fixed points from one production seed form a subsingleton. -/
theorem reachableRawDescriptorFixedPoints_subsingleton
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (seed : RawDescriptorState) :
    Subsingleton
      { state //
        IsReachableRawDescriptorFixedPoint result mol maxEvidenceSize fuel seed state } := by
  constructor
  intro left right
  apply Subtype.ext
  exact reachableRawDescriptorFixedPoint_unique result mol maxEvidenceSize fuel seed
    left.val right.val left.property right.property



theorem stabilizedRawDescriptorState_unique_reachable_fixedPoint
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel remaining : ℕ) (state fixed : RawDescriptorState)
    (accepted :
      stabilizedRawDescriptorState? result mol maxEvidenceSize fuel remaining state = some fixed) :
    IsReachableRawDescriptorFixedPoint result mol maxEvidenceSize fuel state fixed ∧
      ∀ candidate,
        IsReachableRawDescriptorFixedPoint result mol maxEvidenceSize fuel state candidate →
          candidate = fixed := by
  have fixedReachable := stabilizedRawDescriptorState_reachable result mol maxEvidenceSize fuel
    remaining state fixed accepted
  have fixedStable := stabilizedRawDescriptorState_fixed result mol maxEvidenceSize fuel
    remaining state fixed accepted
  refine ⟨⟨fixedReachable, fixedStable⟩, ?_⟩
  intro candidate candidateFixed
  exact reachableRawDescriptorFixedPoint_unique result mol maxEvidenceSize fuel state
    candidate fixed candidateFixed ⟨fixedReachable, fixedStable⟩



theorem stabilizedRawDescriptorState_existsUnique_reachable_fixedPoint
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel remaining : ℕ) (state fixed : RawDescriptorState)
    (accepted :
      stabilizedRawDescriptorState? result mol maxEvidenceSize fuel remaining state = some fixed) :
    ∃! candidate,
      IsReachableRawDescriptorFixedPoint result mol maxEvidenceSize fuel state candidate := by
  rcases stabilizedRawDescriptorState_unique_reachable_fixedPoint result mol maxEvidenceSize fuel
      remaining state fixed accepted with ⟨fixedProperty, unique⟩
  exact ⟨fixed, fixedProperty, unique⟩

/-- Annotated tetrahedral centers in parser order. -/
def rawAnnotatedCenters (result : ChemistryNormalizationResult) : List ℕ :=
  (List.range result.parsed.atomCount).filter fun atom =>
    match result.parsed.atomAt? atom with
    | some spec => spec.tetrahedral?.isSome
    | none => false

/-- Recompute every unresolved center against one shared provisional auxiliary environment. -/
def auxiliarySimultaneousDescriptorState (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (auxiliary : RawDescriptorState) (maxEvidenceSize fuel : ℕ)
    (unresolved : List ℕ) (seed : RawDescriptorState) : RawDescriptorState :=
  unresolved.foldl (fun state center =>
    match tetrahedralFactFromState? result mol auxiliary maxEvidenceSize fuel center with
    | some fact =>
        let committed :=
          if fact.decisiveRule? == some CIPRuleFamily.likeUnlikeDescriptorPair &&
              fact.descriptorDependentPairs == 1 then
            { fact with uppercase := true }
          else fact
        state.insertIfAbsent committed
    | none => state) seed

/-- Resolve a circular dependency through temporary auxiliary `R₀/S₀` senses.

The temporary facts are used only as branch-ranking evidence.  They are never returned as actual
descriptors: every unresolved center is recomputed against the complete auxiliary environment, and
only those recomputed facts are committed simultaneously before the ordinary fixed point resumes. -/
def solveAuxiliaryDescriptorDependencies (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (seed : RawDescriptorState) : RawDescriptorState :=
  let unresolved := (rawAnnotatedCenters result).filter fun center => (seed.factAt? center).isNone
  -- A two-center dependency with no absolute seed is the exact circular case handled below by
  -- simultaneous sense-and-case enumeration.  Committing uppercase `R₀/S₀` occurrences here
  -- would erase its valid lowercase fixed point before that solver can inspect it.
  if seed.isEmpty && unresolved.length == 2 then seed else
  let auxiliary := unresolved.foldl (fun state center =>
    let ligands := mol.ligandsWithLonePair center
    let uncachedCompareAt := fun left right =>
      compareBranchesBeforeRule6? result mol seed fuel center
        (ligands.getD left 0) (ligands.getD right 0)
    let comparisonCache := cachePositionComparisons ligands.length uncachedCompareAt
    let compareAt := cachedPositionComparison? comparisonCache
    let oddSeedSymmetry? :=
      hasOddConstitutionAutomorphismAtCenter mol center ligands fun left right =>
        compareAt left right == some Ordering.eq
    -- Temporary `R₀/S₀` labels may not defeat a symmetry that exists in the constructive seed;
    -- doing so bootstraps false Rule-4/5 facts in VS006/VS009.  A strict occurrence-local result is
    -- independent evidence and therefore remains eligible (the collective VS296--VS298 path).
    if oddSeedSymmetry? != some false &&
        (tetrahedralOccurrenceFact? mol fuel center).isNone then state else
      match tentativeAuxiliaryFactAt? mol fuel center with
      | some fact => state.insertIfAbsent fact
      | none => state) seed
  let simultaneous := auxiliarySimultaneousDescriptorState
    result mol auxiliary maxEvidenceSize fuel unresolved seed
  if seed.length < simultaneous.length then
    discoverRawDescriptorsFrom result mol maxEvidenceSize fuel
      (result.parsed.atomCount + 1) simultaneous
  else
    seed

/-- All exact sense-and-case environments for a bounded set of unresolved auxiliary nodes. -/
def auxiliaryDescriptorEnvironments : ℕ → List (List (RS × Bool))
  | 0 => [[]]
  | count + 1 => (auxiliaryDescriptorEnvironments count).flatMap fun tail =>
      [(RS.R, true) :: tail, (RS.S, true) :: tail,
       (RS.R, false) :: tail, (RS.S, false) :: tail]

/-- Result of an exhaustive uniqueness search retaining at most one accepted value. -/
inductive AuxiliarySolutionSummary (α : Type) where
  | none
  | unique (value : α)
  | ambiguous
  deriving DecidableEq, Repr

/-- Add one evaluated environment, stopping semantically after the second accepted candidate. -/
def AuxiliarySolutionSummary.addCandidate {α : Type} (summary : AuxiliarySolutionSummary α)
    (candidate : Option α) : AuxiliarySolutionSummary α :=
  match summary, candidate with
  | .ambiguous, _ => .ambiguous
  | summary, Option.none => summary
  | .none, Option.some value => .unique value
  | .unique _, Option.some _ => .ambiguous

/-- Fold the same four-way environment family without constructing its exponentially large list. -/
def foldAuxiliaryDescriptorEnvironments {σ : Type} :
    Nat → (σ → List (RS × Bool) → σ) → σ → σ
  | 0, step, initial => step initial []
  | count + 1, step, initial =>
      foldAuxiliaryDescriptorEnvironments count (fun state tail =>
        [(RS.R, true), (RS.S, true), (RS.R, false), (RS.S, false)].foldl
          (fun current choice => step current (choice :: tail)) state) initial

/-- Streaming fold with an absorbing stop condition checked before descending or evaluating a leaf. -/
def foldAuxiliaryDescriptorEnvironmentsUntil {σ : Type} :
    Nat → (σ → Bool) → (σ → List (RS × Bool) → σ) → σ → σ
  | 0, stop, step, initial => if stop initial then initial else step initial []
  | count + 1, stop, step, initial =>
      if stop initial then initial else
        foldAuxiliaryDescriptorEnvironmentsUntil count stop (fun state tail =>
          [(RS.R, true), (RS.S, true), (RS.R, false), (RS.S, false)].foldl
            (fun current choice =>
              if stop current then current else step current (choice :: tail)) state) initial

/-- Cap-free streaming uniqueness search from an empty environment. -/
def searchAuxiliaryDescriptorEnvironments {α : Type} (count : Nat)
    (evaluate : List (RS × Bool) → Option α) : AuxiliarySolutionSummary α :=
  foldAuxiliaryDescriptorEnvironmentsUntil count
    (fun summary => match summary with | .ambiguous => true | _ => false)
    (fun summary environment => summary.addCandidate (evaluate environment)) .none

private theorem foldl_flatMap_eq {α σ β : Type} (items : List α) (expand : α → List β)
    (step : σ → β → σ) (initial : σ) :
    (items.flatMap expand).foldl step initial =
      items.foldl (fun state item => (expand item).foldl step state) initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih =>
      simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons]
      exact ih _

/-- The non-materializing fold visits exactly the historical environment list, in the same order. -/
theorem foldAuxiliaryDescriptorEnvironments_eq_foldl {σ : Type} (count : Nat)
    (step : σ → List (RS × Bool) → σ) (initial : σ) :
    foldAuxiliaryDescriptorEnvironments count step initial =
      (auxiliaryDescriptorEnvironments count).foldl step initial := by
  induction count generalizing step initial with
  | zero => rfl
  | succ count ih =>
      simp only [foldAuxiliaryDescriptorEnvironments, auxiliaryDescriptorEnvironments]
      rw [ih, foldl_flatMap_eq]
      rfl

private theorem guardedFoldl_eq_foldl {α σ : Type} (items : List α) (stop : σ → Bool)
    (step : σ → α → σ) (initial : σ)
    (absorbing : ∀ state item, stop state = true → step state item = state) :
    items.foldl (fun state item => if stop state then state else step state item) initial =
      items.foldl step initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih =>
      simp only [List.foldl_cons]
      split <;> rename_i stopped
      · rw [absorbing initial item stopped]
        exact ih initial
      · exact ih _

private theorem foldl_eq_initial_of_absorbing {α σ : Type} (items : List α)
    (stop : σ → Bool) (step : σ → α → σ) (initial : σ)
    (stopped : stop initial = true)
    (absorbing : ∀ state item, stop state = true → step state item = state) :
    items.foldl step initial = initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih =>
      simp only [List.foldl_cons]
      rw [absorbing initial item stopped]
      exact ih initial stopped

/-- An absorbing early stop changes evaluation cost but not the exhaustive fold result. -/
theorem foldAuxiliaryDescriptorEnvironmentsUntil_eq_fold {σ : Type} (count : Nat)
    (stop : σ → Bool) (step : σ → List (RS × Bool) → σ) (initial : σ)
    (absorbing : ∀ state environment, stop state = true → step state environment = state) :
    foldAuxiliaryDescriptorEnvironmentsUntil count stop step initial =
      foldAuxiliaryDescriptorEnvironments count step initial := by
  induction count generalizing step initial with
  | zero =>
      simp only [foldAuxiliaryDescriptorEnvironmentsUntil,
        foldAuxiliaryDescriptorEnvironments]
      split <;> rename_i stopped
      · exact (absorbing initial [] stopped).symm
      · rfl
  | succ count ih =>
      simp only [foldAuxiliaryDescriptorEnvironmentsUntil,
        foldAuxiliaryDescriptorEnvironments]
      split <;> rename_i stopped
      · rw [foldAuxiliaryDescriptorEnvironments_eq_foldl]
        exact (foldl_eq_initial_of_absorbing
          (auxiliaryDescriptorEnvironments count)
          stop
          (fun state tail =>
            [(RS.R, true), (RS.S, true), (RS.R, false), (RS.S, false)].foldl
              (fun current choice => step current (choice :: tail)) state)
          initial stopped (by
            intro state tail stateStopped
            apply foldl_eq_initial_of_absorbing
              [(RS.R, true), (RS.S, true), (RS.R, false), (RS.S, false)]
              stop (fun current choice => step current (choice :: tail)) state stateStopped
            intro current choice currentStopped
            exact absorbing current (choice :: tail) currentStopped)).symm
      · let guardedStep := fun state tail =>
          [(RS.R, true), (RS.S, true), (RS.R, false), (RS.S, false)].foldl
            (fun current choice =>
              if stop current then current else step current (choice :: tail)) state
        let plainStep := fun state tail =>
          [(RS.R, true), (RS.S, true), (RS.R, false), (RS.S, false)].foldl
            (fun current choice => step current (choice :: tail)) state
        have guardedAbsorbing : ∀ state tail, stop state = true → guardedStep state tail = state := by
          intro state tail stateStopped
          dsimp only [guardedStep]
          apply foldl_eq_initial_of_absorbing
            [(RS.R, true), (RS.S, true), (RS.R, false), (RS.S, false)]
            stop
            (fun current choice =>
              if stop current then current else step current (choice :: tail))
            state stateStopped
          intro current choice currentStopped
          simp [currentStopped]
        rw [ih guardedStep initial guardedAbsorbing]
        have guardedEq : guardedStep = plainStep := by
          funext state tail
          exact guardedFoldl_eq_foldl
            [(RS.R, true), (RS.S, true), (RS.R, false), (RS.S, false)]
            stop (fun current choice => step current (choice :: tail)) state
            (fun current choice currentStopped =>
              absorbing current (choice :: tail) currentStopped)
        rw [guardedEq]

private theorem foldl_addCandidate_unique_iff {α β : Type} (items : List β)
    (evaluate : β → Option α) (initial : AuxiliarySolutionSummary α) (facts : α) :
    items.foldl (fun summary item => summary.addCandidate (evaluate item)) initial =
        .unique facts ↔
      match initial with
      | .none => items.filterMap evaluate = [facts]
      | .unique prior => prior = facts ∧ items.filterMap evaluate = []
      | .ambiguous => False := by
  induction items generalizing initial facts with
  | nil => cases initial <;> simp
  | cons item items ih =>
      cases evaluated : evaluate item with
      | none =>
          cases initial with
          | none =>
              simpa [evaluated, AuxiliarySolutionSummary.addCandidate] using
                ih AuxiliarySolutionSummary.none facts
          | unique prior =>
              simpa [evaluated, AuxiliarySolutionSummary.addCandidate] using
                ih (AuxiliarySolutionSummary.unique prior) facts
          | ambiguous =>
              simpa [evaluated, AuxiliarySolutionSummary.addCandidate] using
                ih AuxiliarySolutionSummary.ambiguous facts
      | some value =>
          cases initial with
          | none =>
              simpa [evaluated, AuxiliarySolutionSummary.addCandidate] using
                ih (AuxiliarySolutionSummary.unique value) facts
          | unique prior =>
              simpa [evaluated, AuxiliarySolutionSummary.addCandidate] using
                ih AuxiliarySolutionSummary.ambiguous facts
          | ambiguous =>
              simpa [evaluated, AuxiliarySolutionSummary.addCandidate] using
                ih AuxiliarySolutionSummary.ambiguous facts

/-- Streaming uniqueness is extensionally identical to asking for a singleton filtered list. -/
theorem searchAuxiliaryDescriptorEnvironments_unique_iff {α : Type} (count : Nat)
    (evaluate : List (RS × Bool) → Option α) (facts : α) :
    searchAuxiliaryDescriptorEnvironments count evaluate = .unique facts ↔
      (auxiliaryDescriptorEnvironments count).filterMap evaluate = [facts] := by
  unfold searchAuxiliaryDescriptorEnvironments
  rw [foldAuxiliaryDescriptorEnvironmentsUntil_eq_fold]
  · rw [foldAuxiliaryDescriptorEnvironments_eq_foldl]
    simpa using foldl_addCandidate_unique_iff
      (auxiliaryDescriptorEnvironments count) evaluate (.none) facts
  · intro summary environment stopped
    cases summary <;> simp [AuxiliarySolutionSummary.addCandidate] at stopped ⊢

/-- Strict Rule-3 ranking with shared geometry retained as an orientation frame.

This is not the ordinary Rule-3 comparator: a lone physical unit seen through two ring arms cannot
rank those arms by itself.  The exact circular solver uses this order only after a unique lowercase
descriptor carrier has independently been found on that unit's far-side reference path. -/
def rankBranchPositionsThroughCircularRule3Authoritative?
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (center : ℕ) (branches : List ℕ) : Option (List ℕ) :=
  let atomOf := fun position => branches.getD position 0
  let compareAt := fun left right =>
    match mol.compareBranchesAuthoritativeStatus center (atomOf left) (atomOf right) with
    | .lower => some Ordering.lt
    | .higher => some Ordering.gt
    | .unresolved => none
    | .tied => some (ChemistryNormalizationResult.compareRule3GeometrySequences
        (result.rule3GeometrySequenceOnBranch mol center (atomOf left))
        (result.rule3GeometrySequenceOnBranch mol center (atomOf right)))
  let before := fun left right => compareAt left right != some Ordering.lt
  let sorted := sortDescBy before (List.range branches.length)
  let strict := (List.range (sorted.length - 1)).all fun index =>
    match sorted[index]?, sorted[index + 1]? with
    | some left, some right => compareAt left right == some Ordering.gt
    | _, _ => false
  if strict then some sorted else none

/-- Public circular Rule-3 ranking routed through the width-unbounded comparator. -/
def rankBranchPositionsThroughCircularRule3? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (_fuel center : ℕ) (branches : List ℕ) : Option (List ℕ) :=
  rankBranchPositionsThroughCircularRule3Authoritative? result mol center branches

/-- Side of one alkene substituent, inferring it from the marked partner when necessary. -/
def rule3SubstituentSide? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (endpoint partner substituent : ℕ) : Option DirectionalBondMarker :=
  match result.stereobonds.substituentSideMarker? endpoint substituent with
  | some side => some side
  | none =>
      match (mol.alkeneSubstituents endpoint partner).filter fun atom => atom != substituent with
      | [other] =>
          (result.stereobonds.substituentSideMarker? endpoint other).map
            DirectionalBondMarker.flip
      | _ => none

/-- Unique lowercase occurrence sense selected by a lone shared Rule-3 unit.

The geometrical unit chooses a far-side reference path but never supplies the priority decision.
The descriptor on the first annotated occurrence along that path is the independent Rule-4c
carrier.  Requiring one physical unit, one entry endpoint, and one nearest sense excludes coupled
two-unit topology sequencing and ambiguous ring closures. -/
def exactCircularSharedRule3CarrierSenseCapFree? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel center : ℕ) : Option RS := do
  let ligands := mol.ligandsWithLonePair center
  let occurrences := ligands.flatMap fun ligand =>
    result.rule3GeometryOccurrencesOnBranch mol center ligand
  let units := (occurrences.map fun occurrence =>
    (occurrence.left, occurrence.right)).eraseDups
  if units.length != 1 || occurrences.length < 2 ||
      result.hasCoupledRule3PerfectMatching mol fuel center then none else
  let unit ← units.head?
  let unitOccurrences := occurrences.filter fun occurrence =>
    occurrence.left == unit.1 && occurrence.right == unit.2
  let nearEndpoints := (unitOccurrences.map fun occurrence => occurrence.near).eraseDups
  if nearEndpoints.length != 1 then none else
  let near ← nearEndpoints.head?
  let far := if near == unit.1 then unit.2 else unit.1
  let farReferenceSide? :=
    match result.seniorSideAt? far near with
    | some side => some side
    | none =>
        ((mol.alkeneSubstituents far near).filterMap fun substituent =>
          result.stereobonds.substituentSideMarker? far substituent).head?
  let farReferenceSide ← farReferenceSide?
  let referenceSubstituents := (mol.alkeneSubstituents far near).filter fun substituent =>
    rule3SubstituentSide? result mol far near substituent == some farReferenceSide
  let referenceSubstituent ← match referenceSubstituents with
    | [substituent] => some substituent
    | _ => none
  let nodes ← collectCanonicalTreeAuthoritative mol fuel [canonicalCenterRoot center]
  let candidates := nodes.filter fun node =>
    node.provenance == RawMolecule.CanonicalNodeProvenance.realAtom &&
      node.atom != center && node.history.contains near && node.history.contains far &&
      node.history.contains referenceSubstituent &&
      (state.factAt? node.atom).any fun fact => !fact.uppercase
  let first ← candidates.head?
  let senses := (candidates.takeWhile fun node => node.depth == first.depth).filterMap fun node =>
    (state.factAt? node.atom).map fun fact =>
      rawAuxiliaryOccurrenceSenseAuthoritative mol node fact
  match senses.eraseDups with
  | [sense] => some sense
  | _ => none

/-- Public circular Rule-3 carrier search routed through cap-free occurrence collection. -/
def exactCircularSharedRule3CarrierSense? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel center : ℕ) : Option RS :=
  exactCircularSharedRule3CarrierSenseCapFree? result mol state fuel center

/-- Exact circular fact when Rule 3 supplies only the orientation of an independently labelled
Rule-4c carrier. -/
def tetrahedralExactCircularGeometryFact? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel idx : ℕ) : Option RawDescriptorFact := do
  let spec ← mol.atomAt? idx
  let parity ← spec.tetrahedral?
  let ligands := mol.ligandsWithLonePair idx
  if ligands.length != 4 then none else
  let positions ← rankBranchPositionsThroughCircularRule3? result mol fuel idx ligands
  let carrier ← exactCircularSharedRule3CarrierSense? result mol state fuel idx
  let evidenceSize := ligands.foldl (fun largest ligand =>
    Nat.max largest (branchDescriptorSequence mol state idx ligand).length) 0
  if evidenceSize == 0 then none else
  let rawDescriptor := RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven positions)
  some { atom := idx
         descriptor := if carrier == RS.S then RS.swap rawDescriptor else rawDescriptor
         uppercase := false
         evidenceSize := evidenceSize
         decisiveRule? := some CIPRuleFamily.pseudoasymmetricDescriptor
         descriptorDependentPairs := 1
         priorityPositions := positions }

/-- Projected Rule-4c already uses occurrence-local senses while ranking the ligands.  During an
exact simultaneous fixed-point test, applying its molecular-global carrier transport a second time
double-counts that re-rooting. -/
def normalizeExactCircularCarrier (mol : RawMolecule) (state : RawDescriptorState)
    (fact : RawDescriptorFact) : RawDescriptorFact :=
  if fact.decisiveRule? == some CIPRuleFamily.pseudoasymmetricDescriptor &&
      fact.descriptorDependentPairs == 1 &&
      nearestLowercaseOccurrenceSense? mol state fact.atom == some RS.S then
    { fact with descriptor := RS.swap fact.descriptor }
  else fact

structure ExactCircularPositionComparison where
  ordering : Ordering
  pseudo : Bool := false
  deriving DecidableEq, Repr

/-- Nearest real occurrence of `partner` on one ligand branch of an already compiled exact tree. -/
def nearestExactCircularOccurrenceLayer? (nodes : List RawMolecule.CanonicalBranchNode)
    (partner ligand : ℕ) : Option (ℕ × List RawMolecule.CanonicalBranchNode) :=
  let occurrences := nodes.filter fun node =>
    node.provenance == RawMolecule.CanonicalNodeProvenance.realAtom &&
      node.atom == partner && node.history.reverse.getD 1 0 == ligand
  match occurrences with
  | [] => none
  | first :: rest =>
      let depth := rest.foldl (fun minimum node => Nat.min minimum node.depth) first.depth
      some (depth, occurrences.filter fun node => node.depth == depth)

def compareExactCircularOccurrenceSenses : List RS → List RS → ExactCircularPositionComparison
  | [], [] => { ordering := Ordering.eq }
  | [], _ :: _ => { ordering := Ordering.lt }
  | _ :: _, [] => { ordering := Ordering.gt }
  | left :: lefts, right :: rights =>
      if left == right then compareExactCircularOccurrenceSenses lefts rights
      else if left == RS.R then { ordering := Ordering.gt, pseudo := true }
      else { ordering := Ordering.lt, pseudo := true }

/-- Compare two nearest partner-occurrence layers.  An occurrence in an earlier sphere decides by
Rule 4a; only an `r/s` difference at corresponding positions is a lowercase Rule-4c boundary. -/
def compareExactCircularOccurrenceLayers (mol : RawMolecule) (partnerFact : RawDescriptorFact) :
    Option (ℕ × List RawMolecule.CanonicalBranchNode) →
      Option (ℕ × List RawMolecule.CanonicalBranchNode) → ExactCircularPositionComparison
  | none, none => { ordering := Ordering.eq }
  | some _, none => { ordering := Ordering.gt }
  | none, some _ => { ordering := Ordering.lt }
  | some left, some right =>
      if left.1 < right.1 then { ordering := Ordering.gt }
      else if right.1 < left.1 then { ordering := Ordering.lt }
      else
        let before := fun a b => a == RS.R || b == RS.S
        let leftSenses := sortDescBy before (left.2.map fun node =>
          rawAuxiliaryOccurrenceSenseAuthoritative mol node partnerFact)
        let rightSenses := sortDescBy before (right.2.map fun node =>
          rawAuxiliaryOccurrenceSenseAuthoritative mol node partnerFact)
        compareExactCircularOccurrenceSenses leftSenses rightSenses

/-- Width-unbounded Rule-1/2 comparison followed by one exact nearest partner-occurrence layer. -/
def compareBranchesThroughExactCircularPositions? (mol : RawMolecule)
    (partnerFact : RawDescriptorFact) (nodes : List RawMolecule.CanonicalBranchNode)
    (_fuel center left right : ℕ) : Option ExactCircularPositionComparison :=
  match mol.compareBranchesAuthoritativeStatus center left right with
  | .lower => some { ordering := Ordering.lt }
  | .higher => some { ordering := Ordering.gt }
  | .tied =>
      some (compareExactCircularOccurrenceLayers mol partnerFact
        (nearestExactCircularOccurrenceLayer? nodes partnerFact.atom left)
        (nearestExactCircularOccurrenceLayer? nodes partnerFact.atom right))
  | .unresolved => none

/-- Recompute one member of an exact two-center positional environment. -/
def tetrahedralExactCircularPositionFact? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (nodes : List RawMolecule.CanonicalBranchNode) (fuel center partner : ℕ)
    (partnerPositions : List ℕ) : Option RawDescriptorFact := do
  let spec ← mol.atomAt? center
  let parity ← spec.tetrahedral?
  let ligands := mol.ligandsWithLonePair center
  if ligands.length != 4 || partnerPositions.length != 4 then none else
  let partnerFact : RawDescriptorFact :=
    { atom := partner, descriptor := RS.S, uppercase := false, evidenceSize := 0,
      priorityPositions := partnerPositions }
  let atomOf := fun position => ligands.getD position 0
  let compareAt := fun left right =>
    compareBranchesThroughExactCircularPositions? mol partnerFact nodes fuel center
      (atomOf left) (atomOf right)
  let before := fun left right =>
    (compareAt left right).any fun decision => decision.ordering != Ordering.lt
  let positions := sortDescBy before (List.range ligands.length)
  let decisions ← (List.range (positions.length - 1)).mapM fun index => do
    let left ← positions[index]?
    let right ← positions[index + 1]?
    compareAt left right
  if !(decisions.all fun decision => decision.ordering != Ordering.eq) ||
      (decisions.filter fun decision => decision.pseudo).length != 1 then none else
  let pseudoRank := (List.range decisions.length).find? fun index =>
    (decisions[index]?).any ExactCircularPositionComparison.pseudo
  let geometryCarrierSwap := pseudoRank.any fun rank =>
    let seniorPosition := positions.getD rank 0
    let seniorLigand := atomOf seniorPosition
    match result.rule3GeometryOccurrencesOnBranch mol center seniorLigand with
    | first :: _ =>
        result.stereobonds.doubleBondAssignments.any fun assignment =>
          let source := assignment.1
          let target := assignment.2.1
          min source target == first.left && max source target == first.right &&
            first.near == target
    | [] => false
  -- Rule 5 starts by attaching an artificial `R` reference to the enantiomorphic ligand pair.
  -- Returning that comparison to the molecular root transports the reference past every ligand
  -- senior to the pair.  An odd number of such positions reverses the lowercase root descriptor.
  -- If the decisive paths contain a geometrical unit, that unit supplies the orientation frame
  -- instead and `geometryCarrierSwap` performs the corresponding endpoint transport.
  let rule5ReferenceCarrierSwap := pseudoRank.any fun rank =>
    let seniorPosition := positions.getD rank 0
    let juniorPosition := positions.getD (rank + 1) 0
    let hasGeometry :=
      !(result.rule3GeometryOccurrencesOnBranch mol center (atomOf seniorPosition)).isEmpty ||
      !(result.rule3GeometryOccurrencesOnBranch mol center (atomOf juniorPosition)).isEmpty
    !hasGeometry && rank % 2 == 1
  let rawDescriptor := RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven positions)
  some { atom := center
         descriptor := if geometryCarrierSwap || rule5ReferenceCarrierSwap then
             RS.swap rawDescriptor else rawDescriptor
         uppercase := false
         evidenceSize := 1
         decisiveRule? := some CIPRuleFamily.pseudoasymmetricTiebreak
         descriptorDependentPairs := 1
         priorityPositions := positions }

/-- Simultaneously self-consistent positional environments for a two-center circular Rule-4c
hierarchy.

Only the 24 genuine ligand permutations are enumerated.  Both complete canonical trees are
collected without a total-node budget, and every member of this list is a simultaneous positional
fixed point. -/
def exactCircularPositionSolutionsCapFree (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel : ℕ) (unresolved : List ℕ) : List (List RawDescriptorFact) :=
  (do
  let left ← unresolved[0]?
  let right ← unresolved[1]?
  if unresolved.length != 2 then none else
  let leftLigands := mol.ligandsWithLonePair left
  let rightLigands := mol.ligandsWithLonePair right
  let rule3Blocks := fun (center : ℕ) (ligands : List ℕ) =>
    (result.rule3CenterPairStatuses mol fuel center ligands).any fun status =>
      status == ChemistryNormalizationResult.Rule3PairStatus.decides ||
        status == ChemistryNormalizationResult.Rule3PairStatus.unavailable
  if rule3Blocks left leftLigands || rule3Blocks right rightLigands then none else
  let leftNodes ← collectCanonicalTreeAuthoritative mol fuel [canonicalCenterRoot left]
  let rightNodes ← collectCanonicalTreeAuthoritative mol fuel [canonicalCenterRoot right]
  let permutations := (KernelPermutationEnumeration.kernelPermutations ([0, 1, 2, 3] : List ℕ))
  -- One center's response depends only on the partner permutation.  Cache those 24 responses
  -- before joining them into the same 24×24 simultaneous fixed-point search; recomputing each
  -- response for every permutation of the other center is both redundant and prohibitively slow.
  let leftResponses : List (List ℕ × RawDescriptorFact) :=
    permutations.filterMap fun rightPositions => do
    let fact ← tetrahedralExactCircularPositionFact? result mol leftNodes fuel left right
      rightPositions
    some (rightPositions, fact)
  let rightResponses : List (List ℕ × RawDescriptorFact) :=
    permutations.filterMap fun leftPositions => do
    let fact ← tetrahedralExactCircularPositionFact? result mol rightNodes fuel right left
      leftPositions
    some (leftPositions, fact)
  let solutions : List (List RawDescriptorFact) :=
    leftResponses.flatMap fun (leftResponse : List ℕ × RawDescriptorFact) =>
    rightResponses.filterMap fun (rightResponse : List ℕ × RawDescriptorFact) =>
      if leftResponse.2.priorityPositions == rightResponse.1 &&
          rightResponse.2.priorityPositions == leftResponse.1 then
        some [leftResponse.2, rightResponse.2]
      else none
  some solutions).getD []

/-- Public two-center circular search, routed exclusively through cap-free collection. -/
def exactCircularPositionSolutions (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel : ℕ) (unresolved : List ℕ) : List (List RawDescriptorFact) :=
  exactCircularPositionSolutionsCapFree result mol fuel unresolved

/-- Accept the two-center positional search only when its simultaneous solution is unique. -/
def solveExactCircularPositionDependencies? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel : ℕ) (unresolved : List ℕ) : Option (List RawDescriptorFact) :=
  match exactCircularPositionSolutions result mol fuel unresolved with
  | [facts] => some facts
  | _ => none

/-- Successful two-center positional discovery is exactly singleton acceptance. -/
theorem solveExactCircularPositionDependencies?_eq_some_iff
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (fuel : ℕ)
    (unresolved : List ℕ) (facts : List RawDescriptorFact) :
    solveExactCircularPositionDependencies? result mol fuel unresolved = some facts ↔
      exactCircularPositionSolutions result mol fuel unresolved = [facts] := by
  unfold solveExactCircularPositionDependencies?
  cases exactCircularPositionSolutions result mol fuel unresolved with
  | nil => simp
  | cons first rest =>
      cases rest with
      | nil => simp
      | cons second tail => simp

/-! ### Exact four-center circular Rule-5 topology

The supported four-center topology has one constitutional tie at each root: two cyclic arms related
by an exact molecular automorphism, with distinct unique annotated occurrences at the same nearest
distance in either direction.  Compiling complete occurrence trees also explores terminal
substituents irrelevant to that first Rule-5 decision.  The solver below keeps the same exact
fixed-point discipline while compiling only this proved nearest-occurrence topology. -/

structure ShallowCircularOccurrence where
  target : ℕ
  parent : ℕ
  distance : ℕ
  deriving DecidableEq, Repr

structure ShallowCircularCenterChoice where
  center : ℕ
  rankings : List (List ℕ)
  leftPosition : ℕ
  rightPosition : ℕ
  leftOccurrence : ShallowCircularOccurrence
  rightOccurrence : ShallowCircularOccurrence
  deriving DecidableEq, Repr

/-- Select a unique nearest item by its final natural-number field. -/
def uniqueNearestTriple? (candidates : List (ℕ × ℕ × ℕ)) : Option (ℕ × ℕ × ℕ) :=
  let ordered := sortDescBy (fun left right => left.2.2 ≤ right.2.2) candidates
  match ordered with
  | [] => none
  | [first] => some first
  | first :: second :: _ => if first.2.2 < second.2.2 then some first else none

/-- Result of searching one canonical ligand digraph for the nearest real occurrence of an atom.

`none` around this result is reserved for bounded-search exhaustion.  Keeping `absent` distinct
from `ambiguous` prevents a caller from discarding a nearer ambiguous carrier and selecting a
farther unique one. -/
inductive ShallowRealOccurrenceSearch where
  | absent
  | unique (occurrence : RawMolecule.CanonicalBranchNode)
  | ambiguous (depth : ℕ)
  deriving DecidableEq, Repr

/-- Unique nearest real occurrence of an atom in one canonical ligand digraph.

Unlike graph distance alone, this retains separate equal-depth simple paths to the same atom.  The
shallow circular solver needs that distinction: collapsing those paths by atom identity can invent a
unique incoming carrier where the auxiliary digraph actually has two occurrences. -/
def nearestShallowRealOccurrenceSearch? (mol : RawMolecule) (target : ℕ) :
    ℕ → ℕ → List RawMolecule.CanonicalBranchNode →
      Option ShallowRealOccurrenceSearch
  | 0, _, [] => some ShallowRealOccurrenceSearch.absent
  | 0, _, _ => none
  | _ + 1, _, [] => some ShallowRealOccurrenceSearch.absent
  | fuel + 1, cap, frontier =>
      if cap < frontier.length then none else
      let occurrences := frontier.filter fun node =>
        node.provenance == RawMolecule.CanonicalNodeProvenance.realAtom && node.atom == target
      match occurrences with
      | [occurrence] => some (ShallowRealOccurrenceSearch.unique occurrence)
      | first :: _ :: _ => some (ShallowRealOccurrenceSearch.ambiguous first.depth)
      | [] =>
          nearestShallowRealOccurrenceSearch? mol target fuel (cap - frontier.length)
            (frontier.flatMap mol.canonicalChildren)

/-- Nearest-layer occurrence search without a total-frontier budget. -/
def nearestShallowRealOccurrenceSearchAuthoritative? (mol : RawMolecule) (target : ℕ) :
    ℕ → List RawMolecule.CanonicalBranchNode → Option ShallowRealOccurrenceSearch
  | 0, [] => some ShallowRealOccurrenceSearch.absent
  | 0, _ => none
  | _ + 1, [] => some ShallowRealOccurrenceSearch.absent
  | fuel + 1, frontier =>
      let occurrences := frontier.filter fun node =>
        node.provenance == RawMolecule.CanonicalNodeProvenance.realAtom && node.atom == target
      match occurrences with
      | [occurrence] => some (ShallowRealOccurrenceSearch.unique occurrence)
      | first :: _ :: _ => some (ShallowRealOccurrenceSearch.ambiguous first.depth)
      | [] =>
          nearestShallowRealOccurrenceSearchAuthoritative? mol target fuel
            (frontier.flatMap mol.canonicalChildren)

/-- Cap-free nearest other annotated center on one ligand arm, together with the real atom through
which that occurrence is entered.  Both rooting directions must have a unique nearest path. -/
def nearestShallowCircularOccurrenceCapFree? (mol : RawMolecule) (centers : List ℕ)
    (fuel center ligand : ℕ) : Option ShallowCircularOccurrence := do
  let forwardSearches ← (centers.filter fun target => target != center).mapM fun target => do
    let search ← nearestShallowRealOccurrenceSearchAuthoritative? mol target fuel
      [RawMolecule.canonicalRoot center ligand]
    some (target, search)
  let nearest ← uniqueNearestTriple? (forwardSearches.filterMap fun entry =>
    match entry.2 with
    | ShallowRealOccurrenceSearch.unique occurrence =>
        some (entry.1, occurrence.parent, occurrence.depth)
    | _ => none)
  if forwardSearches.any fun entry =>
      match entry.2 with
      | ShallowRealOccurrenceSearch.ambiguous depth => depth ≤ nearest.2.2
      | _ => false then none else
  let target := nearest.1
  let reverseSearches ← (mol.ligandsWithLonePair target).mapM fun parent => do
    let search ← nearestShallowRealOccurrenceSearchAuthoritative? mol center fuel
      [RawMolecule.canonicalRoot target parent]
    some (parent, search)
  let incoming ← uniqueNearestTriple? (reverseSearches.filterMap fun entry =>
    match entry.2 with
    | ShallowRealOccurrenceSearch.unique occurrence =>
        some (target, entry.1, occurrence.depth)
    | _ => none)
  if reverseSearches.any fun entry =>
      match entry.2 with
      | ShallowRealOccurrenceSearch.ambiguous depth => depth ≤ incoming.2.2
      | _ => false then none else
  if incoming.2.1 != nearest.2.1 || incoming.2.2 != nearest.2.2 then none else
    some { target := target, parent := nearest.2.1, distance := nearest.2.2 }

/-- Public shallow circular carrier search, routed through the cap-free implementation. -/
def nearestShallowCircularOccurrence? (mol : RawMolecule) (centers : List ℕ)
    (fuel center ligand : ℕ) : Option ShallowCircularOccurrence :=
  nearestShallowCircularOccurrenceCapFree? mol centers fuel center ligand

/-- Exact bounded constitutional result used by the shallow solver.  The production canonical
comparator must complete; a tie is accepted only with an explicit automorphism fixing the center
and swapping the two roots. -/
def compareShallowCircularConstitution? (mol : RawMolecule) (_fuel center left right : ℕ) :
    Option Ordering :=
  match mol.compareBranchesAuthoritative? center left right with
  | some Ordering.eq =>
      if mol.hasConstitutionAutomorphismSwapping center left right then some Ordering.eq else none
  | verdict => verdict

/-- The two genuine constitutional rankings at a four-ligand center.  Exactly one adjacent pair
must be an automorphism-proved tie; all other adjacent boundaries are strict. -/
def shallowCircularConstitutionalRankings? (mol : RawMolecule) (fuel center : ℕ) :
    Option (List (List ℕ)) := do
  let ligands := mol.ligandsWithLonePair center
  if ligands.length != 4 then none else
  let atomOf := fun position => ligands.getD position 0
  let pairDecisions := (List.range 4).flatMap fun leftPosition =>
    (List.range 4).filterMap fun rightPosition =>
      if leftPosition < rightPosition then
        some (leftPosition, rightPosition,
          compareShallowCircularConstitution? mol fuel center
            (atomOf leftPosition) (atomOf rightPosition))
      else none
  if pairDecisions.length != 6 ||
      !(pairDecisions.all fun entry => entry.2.2.isSome) ||
      (pairDecisions.filter fun entry => entry.2.2 == some Ordering.eq).length != 1 then none else
  let comparePositions := fun leftPosition rightPosition =>
    if leftPosition == rightPosition then some Ordering.eq
    else if leftPosition < rightPosition then
      (pairDecisions.find? fun entry => entry.1 == leftPosition && entry.2.1 == rightPosition).bind
        fun entry => entry.2.2
    else
      ((pairDecisions.find? fun entry =>
        entry.1 == rightPosition && entry.2.1 == leftPosition).bind fun entry => entry.2.2).map
          Ordering.swap
  let rankings := (KernelPermutationEnumeration.kernelPermutations ([0, 1, 2, 3] : List ℕ)).filter fun positions =>
    let decisions := (List.range 3).map fun index =>
      comparePositions (positions.getD index 0) (positions.getD (index + 1) 0)
    decisions.all Option.isSome &&
      decisions.all fun decision => decision != some Ordering.lt &&
      (decisions.filter fun decision => decision == some Ordering.eq).length == 1
  if rankings.length == 2 then some rankings else none

/-- Enumerate only the two constitutional ligand orders at each center (2⁴ environments), not
arbitrary descriptor senses/cases or 24⁴ ligand permutations. -/
def shallowCircularPositionEnvironments : List (ℕ × List (List ℕ)) →
    List (List (ℕ × List ℕ))
  | [] => [[]]
  | entry :: rest => entry.2.flatMap fun positions =>
      (shallowCircularPositionEnvironments rest).map fun tail => (entry.1, positions) :: tail

/-- Parity of the occurrence frame relative to an established molecular-root ligand order.
Promoting the incoming edge is valid only when both lists are genuine four-ligand permutations. -/
def shallowCircularOccurrenceCarrierOdd? (mol : RawMolecule)
    (occurrence : ShallowCircularOccurrence) (fact : RawDescriptorFact) : Option Bool := do
  let ligands := mol.ligandsWithLonePair occurrence.target
  if ligands.length != 4 || fact.priorityPositions.length != 4 ||
      (fact.priorityPositions.eraseDups).length != 4 ||
      !(fact.priorityPositions.all fun position => position < ligands.length) then none else
  let parentEntry ← ligands.zipIdx.find? fun entry => entry.1 == occurrence.parent
  let occurrenceOrder := parentEntry.2 :: fact.priorityPositions.erase parentEntry.2
  if occurrenceOrder.length != 4 then none else
    some (RawMolecule.permutationIsEven occurrenceOrder !=
      RawMolecule.permutationIsEven fact.priorityPositions)

/-- Recompute one center against a proposed four-center position environment. -/
def tetrahedralShallowCircularFact? (_result : ChemistryNormalizationResult) (mol : RawMolecule)
    (choice : ShallowCircularCenterChoice) (environment : List (ℕ × List ℕ)) :
    Option RawDescriptorFact := do
  let center := choice.center
  let spec ← mol.atomAt? center
  let parity ← spec.tetrahedral?
  let ligands := mol.ligandsWithLonePair center
  let assumed : RawDescriptorState := environment.filterMap fun entry =>
    match mol.atomAt? entry.1 with
    | some targetSpec => targetSpec.tetrahedral?.map fun targetParity =>
        ({ atom := entry.1
           descriptor := RawMolecule.descriptorOfParity targetParity
             (RawMolecule.permutationIsEven entry.2)
           uppercase := false
           evidenceSize := 1
           priorityPositions := entry.2 } : RawDescriptorFact)
    | none => none
  if assumed.length != environment.length || ligands.length != 4 then none else
  let leftFact ← assumed.factAt? choice.leftOccurrence.target
  let rightFact ← assumed.factAt? choice.rightOccurrence.target
  let nodeOf := fun occurrence : ShallowCircularOccurrence =>
    ({ atom := occurrence.target, parent := occurrence.parent,
       history := [occurrence.target, occurrence.parent],
       provenance := RawMolecule.CanonicalNodeProvenance.realAtom } :
      RawMolecule.CanonicalBranchNode)
  let leftSense :=
    rawAuxiliaryOccurrenceSenseAuthoritative mol (nodeOf choice.leftOccurrence) leftFact
  let rightSense :=
    rawAuxiliaryOccurrenceSenseAuthoritative mol (nodeOf choice.rightOccurrence) rightFact
  let leftCarrierOdd ← shallowCircularOccurrenceCarrierOdd? mol choice.leftOccurrence leftFact
  let rightCarrierOdd ← shallowCircularOccurrenceCarrierOdd? mol choice.rightOccurrence rightFact
  if leftSense == rightSense then none else
  let senior := if leftSense == RS.R then choice.leftPosition else choice.rightPosition
  let junior := if leftSense == RS.R then choice.rightPosition else choice.leftPosition
  let solutions := choice.rankings.filter fun positions =>
    match positions.idxOf? senior, positions.idxOf? junior with
    | some seniorIndex, some juniorIndex => seniorIndex + 1 == juniorIndex
    | _, _ => false
  let positions ← match solutions with | [positions] => some positions | _ => none
  let rawDescriptor := RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven positions)
  some { atom := center
         -- Transport the tied-arm decision from its two independently re-rooted occurrence frames
         -- back to the molecular root.  Only an odd relative carrier parity reverses the sense.
         descriptor := if leftCarrierOdd != rightCarrierOdd then RS.swap rawDescriptor
           else rawDescriptor
         uppercase := false
         evidenceSize := 1
         decisiveRule? := some CIPRuleFamily.pseudoasymmetricTiebreak
         descriptorDependentPairs := 1
         priorityPositions := positions }

/-- Simultaneously self-consistent positional environments for the exactly four-center shallow
circular topology. -/
def exactFourCenterCircularPositionSolutions (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel : ℕ) (centers : List ℕ) : List (List RawDescriptorFact) :=
  (do
  if centers.length != 4 || centers.eraseDups.length != 4 then none else
  let choices ← centers.mapM fun (center : ℕ) => do
    let rankings : List (List ℕ) ← shallowCircularConstitutionalRankings? mol fuel center
    -- Both tied cyclic arms must reach distinct, equidistant, unique annotated occurrences; this
    -- rejects ordinary local constitutional ties unrelated to the four-center circular hierarchy.
    let ligands := mol.ligandsWithLonePair center
    let first : List ℕ ← rankings[0]?
    let second : List ℕ ← rankings[1]?
    let changedIndices := (List.range 4).filter fun index =>
      first.getD index 0 != second.getD index 0
    if changedIndices.length != 2 then none else
    let leftRank := changedIndices.getD 0 0
    let rightRank := changedIndices.getD 1 0
    let leftPosition := first.getD leftRank 0
    let rightPosition := first.getD rightRank 0
    if leftRank + 1 != rightRank || second.getD leftRank 0 != rightPosition ||
        second.getD rightRank 0 != leftPosition then none else
    let leftOccurrence ← nearestShallowCircularOccurrence? mol centers fuel center
      (ligands.getD leftPosition 0)
    let rightOccurrence ← nearestShallowCircularOccurrence? mol centers fuel center
      (ligands.getD rightPosition 0)
    if !mol.atomLiesInCycle fuel (ligands.getD leftPosition 0) ||
        !mol.atomLiesInCycle fuel (ligands.getD rightPosition 0) ||
        !mol.atomLiesInCycle fuel leftOccurrence.parent ||
        !mol.atomLiesInCycle fuel rightOccurrence.parent ||
        leftOccurrence.target == rightOccurrence.target ||
        leftOccurrence.distance != rightOccurrence.distance then none else
    let hasRule3Geometry := ligands.any fun ligand =>
      !(result.rule3GeometrySequenceOnBranch mol center ligand).isEmpty ||
        !(result.rule3GeometryOccurrencesOnBranch mol center ligand).isEmpty
    if hasRule3Geometry then none else
    let choice : ShallowCircularCenterChoice :=
      { center := center, rankings := rankings,
        leftPosition := leftPosition, rightPosition := rightPosition,
        leftOccurrence := leftOccurrence, rightOccurrence := rightOccurrence }
    some choice
  let environments : List (List (ℕ × List ℕ)) := shallowCircularPositionEnvironments
    (choices.map fun (choice : ShallowCircularCenterChoice) =>
      (choice.center, choice.rankings))
  -- This simultaneous check is self-free even though the environment contains all four entries:
  -- `tetrahedralShallowCircularFact?` reads only the two occurrence targets, and applicability
  -- proves both targets differ from the center being recomputed.  The center's own entry is used
  -- only by the final equality check below.  A unique surviving environment is therefore a unique
  -- positional fixed point, not a descriptor supported by its own provisional fact.
  let solutions : List (List RawDescriptorFact) :=
    environments.filterMap fun (environment : List (ℕ × List ℕ)) => do
    let facts : List RawDescriptorFact ←
      choices.mapM fun (choice : ShallowCircularCenterChoice) =>
      tetrahedralShallowCircularFact? result mol choice environment
    let agrees := facts.length == centers.length && facts.all fun (fact : RawDescriptorFact) =>
      (environment.find? fun (entry : ℕ × List ℕ) => entry.1 == fact.atom).any
        fun (entry : ℕ × List ℕ) =>
        entry.2 == fact.priorityPositions
    if agrees then some facts else none
  some solutions).getD []

/-- Accept the four-center positional search only when the simultaneous solution is unique and
covers each requested center exactly once. -/
def solveExactFourCenterCircularDependencies? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel : ℕ) (centers : List ℕ) : Option (List RawDescriptorFact) :=
  match exactFourCenterCircularPositionSolutions result mol fuel centers with
  | [facts] =>
      let factAtoms := facts.map RawDescriptorFact.atom
      if facts.length != 4 || factAtoms.eraseDups.length != 4 ||
          !(centers.all fun center => factAtoms.contains center) ||
          !(factAtoms.all fun atom => centers.contains atom) then none else
      some facts
  | _ => none

/-- A successful four-center result comes from the sole simultaneous positional environment. -/
theorem solveExactFourCenterCircularDependencies?_unique
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (fuel : ℕ)
    (centers : List ℕ) (facts : List RawDescriptorFact)
    (accepted : solveExactFourCenterCircularDependencies? result mol fuel centers = some facts) :
    exactFourCenterCircularPositionSolutions result mol fuel centers = [facts] ∧
      ∀ candidate,
        candidate ∈ exactFourCenterCircularPositionSolutions result mol fuel centers →
          candidate = facts := by
  unfold solveExactFourCenterCircularDependencies? at accepted
  generalize solutionsEq : exactFourCenterCircularPositionSolutions result mol fuel centers =
      solutions at accepted
  cases solutions with
  | nil => simp at accepted
  | cons first rest =>
      cases rest with
      | nil =>
          simp only at accepted
          split at accepted
          · simp at accepted
          · have factsEq := Option.some.inj accepted
            subst facts
            refine ⟨rfl, ?_⟩
            intro candidate member
            simpa using member
      | cons second tail => simp at accepted

/-- Complete provisional environment associated with one simultaneous circular candidate. -/
def exactAuxiliaryAssumedState (mol : RawMolecule) (fuel : ℕ)
    (seed : RawDescriptorState) (unresolved : List ℕ)
    (descriptors : List (RS × Bool)) : RawDescriptorState :=
  (unresolved.zip descriptors).foldl (fun state entry =>
      let provisional := match tentativeAuxiliaryFactAt? mol fuel entry.1 with
        | some fact => { fact with descriptor := entry.2.1, uppercase := entry.2.2 }
        | none =>
            { atom := entry.1, descriptor := entry.2.1, uppercase := entry.2.2,
              evidenceSize := 0 }
      state.insertIfAbsent provisional) seed

/-- Simultaneously recompute every unresolved center against one complete provisional environment. -/
def exactAuxiliaryRecomputedState (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (maxEvidenceSize fuel : ℕ) (unresolved : List ℕ)
    (assumed : RawDescriptorState) : RawDescriptorState :=
  unresolved.filterMap fun center =>
    match tetrahedralFactFromProjectedState? result mol assumed maxEvidenceSize fuel center with
    | some fact => some (normalizeExactCircularCarrier mol assumed fact)
    | none => tetrahedralExactCircularGeometryFact? result mol assumed fuel center

/-- The simultaneous fixed-point equation for one candidate sense/case environment. -/
def exactAuxiliaryCandidateAgrees (unresolved : List ℕ)
    (descriptors : List (RS × Bool)) (recomputed : RawDescriptorState) : Bool :=
  recomputed.length == unresolved.length &&
    (unresolved.zip descriptors).all fun entry =>
      match recomputed.find? fun fact => fact.atom == entry.1 with
      | some fact => fact.descriptor == entry.2.1 && fact.uppercase == entry.2.2
      | none => false

/-- Evaluate one complete provisional sense-and-case environment against the production
simultaneous fixed-point equation. -/
def exactAuxiliaryDescriptorCandidate? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (maxEvidenceSize fuel : ℕ) (seed : RawDescriptorState)
    (unresolved : List ℕ) (descriptors : List (RS × Bool)) : Option RawDescriptorState :=
  let assumed := exactAuxiliaryAssumedState mol fuel seed unresolved descriptors
  let recomputed :=
    exactAuxiliaryRecomputedState result mol maxEvidenceSize fuel unresolved assumed
  if exactAuxiliaryCandidateAgrees unresolved descriptors recomputed then some recomputed else none

/-- Simultaneously self-consistent descriptor environments for one unresolved circular system.
Membership is the production fixed-point equation: provisional senses are supplied to every
unresolved center, every center is recomputed against that same complete environment, and all
recomputed sense/case pairs must agree with their assumptions.  This materialized list is retained
as the proof specification; production uniqueness search uses the streaming equivalent below. -/
def exactAuxiliaryDescriptorSolutions (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (maxEvidenceSize fuel : ℕ) (seed : RawDescriptorState)
    (unresolved : List ℕ) : List RawDescriptorState :=
  (auxiliaryDescriptorEnvironments unresolved.length).filterMap
    (exactAuxiliaryDescriptorCandidate? result mol maxEvidenceSize fuel seed unresolved)

/-- Cap-free, constant-result-memory classification of the exact simultaneous solution set. -/
def exactAuxiliaryDescriptorSolutionSummary (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (maxEvidenceSize fuel : ℕ) (seed : RawDescriptorState)
    (unresolved : List ℕ) : AuxiliarySolutionSummary RawDescriptorState :=
  searchAuxiliaryDescriptorEnvironments unresolved.length
    (exactAuxiliaryDescriptorCandidate? result mol maxEvidenceSize fuel seed unresolved)

/-- The streaming production classifier reports a unique solution exactly when the retained
proof specification is a singleton. -/
theorem exactAuxiliaryDescriptorSolutionSummary_unique_iff
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (seed : RawDescriptorState)
    (unresolved : List ℕ) (facts : RawDescriptorState) :
    exactAuxiliaryDescriptorSolutionSummary result mol maxEvidenceSize fuel seed unresolved =
        .unique facts ↔
      exactAuxiliaryDescriptorSolutions result mol maxEvidenceSize fuel seed unresolved =
        [facts] := by
  exact searchAuxiliaryDescriptorEnvironments_unique_iff unresolved.length
    (exactAuxiliaryDescriptorCandidate? result mol maxEvidenceSize fuel seed unresolved) facts

/-- Predicate form of membership in the exact simultaneous fixed-point solution set. -/
def IsExactAuxiliaryDescriptorSolution (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (maxEvidenceSize fuel : ℕ) (seed : RawDescriptorState)
    (unresolved : List ℕ) (facts : RawDescriptorState) : Prop :=
  ∃ descriptors, descriptors ∈ auxiliaryDescriptorEnvironments unresolved.length ∧
    let assumed := exactAuxiliaryAssumedState mol fuel seed unresolved descriptors
    let recomputed :=
      exactAuxiliaryRecomputedState result mol maxEvidenceSize fuel unresolved assumed
    recomputed = facts ∧ exactAuxiliaryCandidateAgrees unresolved descriptors recomputed = true

/-- List membership is exactly simultaneous self-consistency, not an enumeration-order condition. -/
theorem mem_exactAuxiliaryDescriptorSolutions_iff
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (seed : RawDescriptorState)
    (unresolved : List ℕ) (facts : RawDescriptorState) :
    facts ∈ exactAuxiliaryDescriptorSolutions result mol maxEvidenceSize fuel seed unresolved ↔
      IsExactAuxiliaryDescriptorSolution result mol maxEvidenceSize fuel seed unresolved facts := by
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with ⟨descriptors, descriptorMember, emitted⟩
    refine ⟨descriptors, descriptorMember, ?_⟩
    dsimp [exactAuxiliaryDescriptorSolutions, exactAuxiliaryDescriptorCandidate?] at emitted
    split at emitted <;> rename_i agrees
    · exact ⟨Option.some.inj emitted, agrees⟩
    · simp at emitted
  · rintro ⟨descriptors, descriptorMember, recomputedEq, agrees⟩
    apply List.mem_filterMap.mpr
    refine ⟨descriptors, descriptorMember, ?_⟩
    dsimp [exactAuxiliaryDescriptorSolutions, exactAuxiliaryDescriptorCandidate?]
    rw [agrees, recomputedEq]
    rfl

/-- Resolve a genuinely circular descriptor hierarchy by a cap-free exact fixed-point test.

Each candidate supplies temporary `R₀/S₀` senses to every unresolved annotated center.  The normal
Rules 3--6 assigner then recomputes all of them simultaneously.  A candidate survives only when
every recomputed sense agrees with its assumption; facts are committed only when exactly one such
environment exists.  Thus enumeration cannot turn ambiguity into a descriptor. -/
def solveExactAuxiliaryDescriptorDependencies (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (maxEvidenceSize fuel : ℕ) (seed : RawDescriptorState) :
    RawDescriptorState :=
  let unresolved := (rawAnnotatedCenters result).filter fun center => (seed.factAt? center).isNone
  let emptyGeometryPair := seed.isEmpty && unresolved.length == 2 && unresolved.all fun center =>
    (mol.ligandsWithLonePair center).any fun ligand =>
      !(result.rule3GeometryOccurrencesOnBranch mol center ligand).isEmpty
  if (seed.isEmpty && !emptyGeometryPair) || unresolved.isEmpty then
    seed
  else
    match exactAuxiliaryDescriptorSolutionSummary result mol maxEvidenceSize fuel seed unresolved with
    | .unique facts =>
        facts.foldl RawDescriptorState.insertIfAbsent seed
    | _ => seed

/-- The exact circular solver either leaves the seed unchanged or commits the sole member of its
simultaneous fixed-point solution list. -/
theorem solveExactAuxiliaryDescriptorDependencies_eq_seed_or_unique
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (seed : RawDescriptorState) :
    let unresolved :=
      (rawAnnotatedCenters result).filter fun center => (seed.factAt? center).isNone
    let solutions :=
      exactAuxiliaryDescriptorSolutions result mol maxEvidenceSize fuel seed unresolved
    solveExactAuxiliaryDescriptorDependencies result mol maxEvidenceSize fuel seed = seed ∨
      ∃ facts, solutions = [facts] ∧
        solveExactAuxiliaryDescriptorDependencies result mol maxEvidenceSize fuel seed =
          facts.foldl RawDescriptorState.insertIfAbsent seed := by
  dsimp only
  unfold solveExactAuxiliaryDescriptorDependencies
  simp only
  split
  · exact Or.inl rfl
  · cases summaryEq : exactAuxiliaryDescriptorSolutionSummary result mol maxEvidenceSize fuel seed
        ((rawAnnotatedCenters result).filter fun center => (seed.factAt? center).isNone) with
    | none => exact Or.inl rfl
    | unique facts =>
        exact Or.inr ⟨facts,
          (exactAuxiliaryDescriptorSolutionSummary_unique_iff result mol maxEvidenceSize fuel seed
            _ facts).mp summaryEq, rfl⟩
    | ambiguous => exact Or.inl rfl

/-- Whenever the exact circular solver changes the seed, its accepted simultaneous descriptor
environment is unique. -/
theorem solveExactAuxiliaryDescriptorDependencies_unique_solution_of_ne_seed
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (seed : RawDescriptorState)
    (changed :
      solveExactAuxiliaryDescriptorDependencies result mol maxEvidenceSize fuel seed ≠ seed) :
    let unresolved :=
      (rawAnnotatedCenters result).filter fun center => (seed.factAt? center).isNone
    let solutions :=
      exactAuxiliaryDescriptorSolutions result mol maxEvidenceSize fuel seed unresolved
    ∃ facts, solutions = [facts] ∧
      (∀ candidate, candidate ∈ solutions → candidate = facts) ∧
      solveExactAuxiliaryDescriptorDependencies result mol maxEvidenceSize fuel seed =
        facts.foldl RawDescriptorState.insertIfAbsent seed := by
  dsimp only
  rcases solveExactAuxiliaryDescriptorDependencies_eq_seed_or_unique
      result mol maxEvidenceSize fuel seed with unchanged | ⟨facts, solutions, output⟩
  · exact False.elim (changed unchanged)
  · refine ⟨facts, solutions, ?_, output⟩
    intro candidate member
    rw [solutions] at member
    simpa using member

/-- Chemistry-facing uniqueness statement: whenever the circular solver commits new facts, there
is exactly one simultaneously self-consistent Rules-3--6 descriptor environment for the unresolved
centers in the finite sense-and-case search space. -/
theorem solveExactAuxiliaryDescriptorDependencies_unique_fixedPoint_of_ne_seed
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (seed : RawDescriptorState)
    (changed :
      solveExactAuxiliaryDescriptorDependencies result mol maxEvidenceSize fuel seed ≠ seed) :
    let unresolved :=
      (rawAnnotatedCenters result).filter fun center => (seed.factAt? center).isNone
    ∃ facts,
      IsExactAuxiliaryDescriptorSolution result mol maxEvidenceSize fuel seed unresolved facts ∧
      (∀ candidate,
        IsExactAuxiliaryDescriptorSolution result mol maxEvidenceSize fuel seed unresolved candidate →
          candidate = facts) ∧
      solveExactAuxiliaryDescriptorDependencies result mol maxEvidenceSize fuel seed =
        facts.foldl RawDescriptorState.insertIfAbsent seed := by
  dsimp only
  rcases solveExactAuxiliaryDescriptorDependencies_unique_solution_of_ne_seed
      result mol maxEvidenceSize fuel seed changed with
    ⟨facts, solutions, uniqueMember, output⟩
  have factsMember : facts ∈ exactAuxiliaryDescriptorSolutions result mol
      maxEvidenceSize fuel seed
      ((rawAnnotatedCenters result).filter fun center => (seed.factAt? center).isNone) := by
    rw [solutions]
    simp
  refine ⟨facts,
    (mem_exactAuxiliaryDescriptorSolutions_iff result mol maxEvidenceSize fuel seed _ facts).mp
      factsMember, ?_, output⟩
  intro candidate consistent
  apply uniqueMember candidate
  exact (mem_exactAuxiliaryDescriptorSolutions_iff result mol maxEvidenceSize fuel seed _
    candidate).mpr consistent

/-- Transport a projected lowercase Rule-5 fact through two independently re-rooted cyclic anchors.

This is an occurrence-frame calculation, not a molecule-size or center-count special case.  Both
anchors must be unique nearest cyclic occurrences on adjacent tied ligand positions, at equal
distance, with valid stored four-ligand orders.  The path into an anchor may contain an acyclic
linker; cyclicity belongs to the uniquely identified target stereogenic unit, not every atom on its
incoming path.  Promoting each incoming edge supplies its carrier parity.  Composing the two
re-rooted frames at the acyclic root includes the exchange of the two tied carrier axes, so the
total transport is odd exactly when the two promotion parities agree. -/
def normalizeTwoCyclicRule6AnchorCarrier (mol : RawMolecule) (fuel : ℕ)
    (state : RawDescriptorState) : RawDescriptorState :=
  state.map fun fact =>
    match exactTwoCyclicAnchorCarrierWitness? mol state fuel fact.atom fact with
    | some true => { fact with descriptor := RS.swap fact.descriptor }
    | _ => fact


def retainLastStableRawDescriptorState (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel remaining : ℕ) (stable proposal : RawDescriptorState) :
    RawDescriptorState :=
  if proposal == stable then stable else
    (stabilizedRawDescriptorState? result mol maxEvidenceSize fuel remaining proposal).getD stable


theorem retainLastStableRawDescriptorState_fixed
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel remaining : ℕ) (stable proposal : RawDescriptorState)
    (stableFixed :
      runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel stable = stable) :
    runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel
        (retainLastStableRawDescriptorState result mol maxEvidenceSize fuel remaining stable proposal) =
      retainLastStableRawDescriptorState result mol maxEvidenceSize fuel remaining stable proposal := by
  unfold retainLastStableRawDescriptorState
  split <;> rename_i unchanged
  · exact stableFixed
  · cases accepted : stabilizedRawDescriptorState? result mol maxEvidenceSize fuel remaining
        proposal with
    | none => simpa [accepted] using stableFixed
    | some fixed =>
        simpa [accepted] using
          stabilizedRawDescriptorState_fixed result mol maxEvidenceSize fuel remaining proposal fixed
            accepted



theorem retainLastStableRawDescriptorState_eq_or_stabilized
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel remaining : ℕ) (stable proposal : RawDescriptorState) :
    retainLastStableRawDescriptorState result mol maxEvidenceSize fuel remaining stable proposal =
        stable ∨
      ∃ fixed,
        retainLastStableRawDescriptorState result mol maxEvidenceSize fuel remaining stable proposal =
            fixed ∧
          stabilizedRawDescriptorState? result mol maxEvidenceSize fuel remaining proposal =
            some fixed := by
  unfold retainLastStableRawDescriptorState
  split
  · exact Or.inl rfl
  · cases accepted : stabilizedRawDescriptorState? result mol maxEvidenceSize fuel remaining
        proposal with
    | none => exact Or.inl (by simp)
    | some fixed => exact Or.inr ⟨fixed, by simp, rfl⟩

/-- A terminal exact auxiliary result is certified by its stable seed and a unique simultaneous
Rules-3--6 solution. -/
def IsUniqueExactAuxiliaryExtension (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (source : RawDescriptorState) : Prop :=
  ∃ seed facts,
    runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed = seed ∧
    let unresolved :=
      (rawAnnotatedCenters result).filter fun center => (seed.factAt? center).isNone
    IsExactAuxiliaryDescriptorSolution result mol maxEvidenceSize fuel seed unresolved facts ∧
      (∀ candidate,
        IsExactAuxiliaryDescriptorSolution result mol maxEvidenceSize fuel seed unresolved candidate →
          candidate = facts) ∧
      source = facts.foldl RawDescriptorState.insertIfAbsent seed

/-- Complete a stable constructive state with the cap-free exact auxiliary solver whenever its
chemical applicability condition is met. -/
def finishRawDescriptorSource (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel : ℕ) (stable : RawDescriptorState) : RawDescriptorState :=
  let remaining := (rawAnnotatedCenters result).filter fun center =>
    (stable.factAt? center).isNone
  let emptyGeometryPair :=
    stable.isEmpty && remaining.length == 2 && remaining.all fun center =>
      (mol.ligandsWithLonePair center).any fun ligand =>
        !(result.rule3GeometryOccurrencesOnBranch mol center ligand).isEmpty
  if stable.isEmpty && !emptyGeometryPair then stable else
    solveExactAuxiliaryDescriptorDependencies result mol 100 fuel stable

/-- Finishing a stable constructive state either preserves a fixed point or commits the unique
simultaneous auxiliary solution. -/
theorem finishRawDescriptorSource_certified
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (fuel : ℕ)
    (stable : RawDescriptorState)
    (stableFixed : runRawDescriptorDiscoveryPass result mol 100 fuel stable = stable) :
    runRawDescriptorDiscoveryPass result mol 100 fuel
        (finishRawDescriptorSource result mol fuel stable) =
      finishRawDescriptorSource result mol fuel stable ∨
    IsUniqueExactAuxiliaryExtension result mol 100 fuel
      (finishRawDescriptorSource result mol fuel stable) := by
  unfold finishRawDescriptorSource
  dsimp only
  split
  · exact Or.inl stableFixed
  · rename_i applicable
    by_cases unchanged :
        solveExactAuxiliaryDescriptorDependencies result mol 100 fuel stable = stable
    · rw [unchanged]
      exact Or.inl stableFixed
    · right
      rcases solveExactAuxiliaryDescriptorDependencies_unique_fixedPoint_of_ne_seed
          result mol 100 fuel stable unchanged with ⟨facts, consistent, unique, output⟩
      exact ⟨stable, facts, stableFixed, consistent, unique, output⟩

/-- Exact provenance of the finishing stage: it either leaves the constructive fixed point
unchanged or commits the uniquely self-consistent simultaneous extension. -/
theorem finishRawDescriptorSource_eq_or_unique
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (fuel : ℕ)
    (stable : RawDescriptorState)
    (stableFixed : runRawDescriptorDiscoveryPass result mol 100 fuel stable = stable) :
    finishRawDescriptorSource result mol fuel stable = stable ∨
      IsUniqueExactAuxiliaryExtension result mol 100 fuel
        (finishRawDescriptorSource result mol fuel stable) := by
  unfold finishRawDescriptorSource
  dsimp only
  split
  · exact Or.inl rfl
  · by_cases unchanged :
        solveExactAuxiliaryDescriptorDependencies result mol 100 fuel stable = stable
    · exact Or.inl unchanged
    · right
      rcases solveExactAuxiliaryDescriptorDependencies_unique_fixedPoint_of_ne_seed
          result mol 100 fuel stable unchanged with ⟨facts, consistent, unique, output⟩
      exact ⟨stable, facts, stableFixed, consistent, unique, output⟩

/-- A pre-normalization source is admissible exactly when it reports nothing, is constructively
stable, or is the unique accepted member of one of the bounded simultaneous searches. -/
def IsCertifiedRawDescriptorSource (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel : ℕ) (source : RawDescriptorState) : Prop :=
  source = [] ∨
  runRawDescriptorDiscoveryPass result mol 100 fuel source = source ∨
  exactCircularPositionSolutions result mol fuel (rawAnnotatedCenters result) = [source] ∨
  exactFourCenterCircularPositionSolutions result mol fuel (rawAnnotatedCenters result) = [source] ∨
  IsUniqueExactAuxiliaryExtension result mol 100 fuel source

/-- Strong production provenance.  A constructive source records the actual stabilization gate
that accepted it; the remaining branches record the unique bounded simultaneous solution. -/
def IsCanonicalRawDescriptorSource (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel : ℕ) (source : RawDescriptorState) : Prop :=
  source = [] ∨
  (∃ seed,
    stabilizedRawDescriptorState? result mol 100 fuel (result.parsed.atomCount + 1) seed =
      some source) ∨
  exactCircularPositionSolutions result mol fuel (rawAnnotatedCenters result) = [source] ∨
  exactFourCenterCircularPositionSolutions result mol fuel (rawAnnotatedCenters result) = [source] ∨
  IsUniqueExactAuxiliaryExtension result mol 100 fuel source

/-- Mathematical uniqueness content of a production source.  Constructive results are unique fixed
points on a recorded deterministic orbit; simultaneous-search results retain their singleton or
unique-extension certificates. -/
def IsUniqueRawDescriptorSource (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel : ℕ) (source : RawDescriptorState) : Prop :=
  source = [] ∨
  (∃ seed,
    IsReachableRawDescriptorFixedPoint result mol 100 fuel seed source ∧
      ∀ candidate,
        IsReachableRawDescriptorFixedPoint result mol 100 fuel seed candidate →
          candidate = source) ∨
  exactCircularPositionSolutions result mol fuel (rawAnnotatedCenters result) = [source] ∨
  exactFourCenterCircularPositionSolutions result mol fuel (rawAnnotatedCenters result) = [source] ∨
  IsUniqueExactAuxiliaryExtension result mol 100 fuel source

/-- Canonical provenance entails the corresponding mathematical uniqueness statement. -/
theorem IsCanonicalRawDescriptorSource.isUnique
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (fuel : ℕ)
    {source : RawDescriptorState}
    (canonical : IsCanonicalRawDescriptorSource result mol fuel source) :
    IsUniqueRawDescriptorSource result mol fuel source := by
  rcases canonical with empty | canonical
  · exact Or.inl empty
  rcases canonical with ⟨seed, accepted⟩ | canonical
  · rcases stabilizedRawDescriptorState_unique_reachable_fixedPoint result mol 100 fuel
      (result.parsed.atomCount + 1) seed source accepted with ⟨fixed, unique⟩
    exact Or.inr (Or.inl ⟨seed, fixed, unique⟩)
  rcases canonical with twoCenter | canonical
  · exact Or.inr (Or.inr (Or.inl twoCenter))
  rcases canonical with fourCenter | unique
  · exact Or.inr (Or.inr (Or.inr (Or.inl fourCenter)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr unique)))

/-- Strong canonical provenance implies the earlier termination-safety certificate. -/
theorem IsCanonicalRawDescriptorSource.isCertified
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (fuel : ℕ)
    {source : RawDescriptorState}
    (canonical : IsCanonicalRawDescriptorSource result mol fuel source) :
    IsCertifiedRawDescriptorSource result mol fuel source := by
  rcases canonical with empty | canonical
  · exact Or.inl empty
  rcases canonical with ⟨seed, accepted⟩ | canonical
  · exact Or.inr (Or.inl
      (stabilizedRawDescriptorState_fixed result mol 100 fuel
        (result.parsed.atomCount + 1) seed source accepted))
  rcases canonical with twoCenter | canonical
  · exact Or.inr (Or.inr (Or.inl twoCenter))
  rcases canonical with fourCenter | unique
  · exact Or.inr (Or.inr (Or.inr (Or.inl fourCenter)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr unique)))

/-- Proof-erased computation performed by the constructive production selector.  Keeping the
value outside the dependent provenance payload makes projection cheap for downstream concrete
certificates while preserving exactly the same branch structure. -/
def constructiveRawDescriptorSourceValue (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel : ℕ) (initial : RawDescriptorState) : RawDescriptorState :=
  match stabilizedRawDescriptorState? result mol 100 fuel
      (result.parsed.atomCount + 1) initial with
  | none => []
  | some expansive =>
      let firstAux := solveAuxiliaryDescriptorDependencies result mol 100 fuel expansive
      match stabilizedRawDescriptorState? result mol 100 fuel
          (result.parsed.atomCount + 1) firstAux with
      | none => expansive
      | some resumed =>
          let secondAux := solveAuxiliaryDescriptorDependencies result mol 100 fuel resumed
          let stable := retainLastStableRawDescriptorState result mol 100 fuel
            (result.parsed.atomCount + 1) resumed secondAux
          finishRawDescriptorSource result mol fuel stable

/-- Certified constructive selection from a given Rules-1--3 seed. -/
def certifiedConstructiveRawDescriptorSource (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel : ℕ) (initial : RawDescriptorState) :
    { source //
      source = [] ∨
      (∃ seed,
        stabilizedRawDescriptorState? result mol 100 fuel
          (result.parsed.atomCount + 1) seed = some source) ∨
      IsUniqueExactAuxiliaryExtension result mol 100 fuel source } :=
  let source := constructiveRawDescriptorSourceValue result mol fuel initial
  have provenance :
      source = [] ∨
      (∃ seed,
        stabilizedRawDescriptorState? result mol 100 fuel
          (result.parsed.atomCount + 1) seed = some source) ∨
      IsUniqueExactAuxiliaryExtension result mol 100 fuel source := by
    dsimp only [source]
    unfold constructiveRawDescriptorSourceValue
    split <;> rename_i firstAccepted
    · exact Or.inl rfl
    · rename_i expansive
      let firstAux := solveAuxiliaryDescriptorDependencies result mol 100 fuel expansive
      dsimp only
      split <;> rename_i resumedAccepted
      · exact Or.inr (Or.inl ⟨initial, firstAccepted⟩)
      · rename_i resumed
        have resumedFixed := stabilizedRawDescriptorState_fixed result mol 100 fuel
          (result.parsed.atomCount + 1) firstAux resumed resumedAccepted
        let secondAux := solveAuxiliaryDescriptorDependencies result mol 100 fuel resumed
        let stable := retainLastStableRawDescriptorState result mol 100 fuel
          (result.parsed.atomCount + 1) resumed secondAux
        have stableFixed := retainLastStableRawDescriptorState_fixed result mol 100 fuel
          (result.parsed.atomCount + 1) resumed secondAux resumedFixed
        have stableProvenance :
            ∃ seed,
              stabilizedRawDescriptorState? result mol 100 fuel
                (result.parsed.atomCount + 1) seed = some stable := by
          rcases retainLastStableRawDescriptorState_eq_or_stabilized result mol 100 fuel
              (result.parsed.atomCount + 1) resumed secondAux with retained | accepted
          · refine ⟨firstAux, ?_⟩
            change stabilizedRawDescriptorState? result mol 100 fuel
              (result.parsed.atomCount + 1) firstAux =
                some (retainLastStableRawDescriptorState result mol 100 fuel
                  (result.parsed.atomCount + 1) resumed secondAux)
            rw [retained]
            exact resumedAccepted
          · rcases accepted with ⟨fixed, retained, fixedAccepted⟩
            refine ⟨secondAux, ?_⟩
            change stabilizedRawDescriptorState? result mol 100 fuel
              (result.parsed.atomCount + 1) secondAux =
                some (retainLastStableRawDescriptorState result mol 100 fuel
                  (result.parsed.atomCount + 1) resumed secondAux)
            rw [retained]
            exact fixedAccepted
        have finished := finishRawDescriptorSource_eq_or_unique result mol fuel stable stableFixed
        rcases finished with unchanged | unique
        · right; left
          rcases stableProvenance with ⟨seed, accepted⟩
          refine ⟨seed, ?_⟩
          change stabilizedRawDescriptorState? result mol 100 fuel
            (result.parsed.atomCount + 1) seed =
              some (finishRawDescriptorSource result mol fuel stable)
          rw [unchanged]
          exact accepted
        · exact Or.inr (Or.inr unique)
  ⟨source, provenance⟩

/-- The production source together with its machine-checked provenance certificate. -/
def certifiedRawDescriptorSource (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel : ℕ) : { source // IsCanonicalRawDescriptorSource result mol fuel source } :=
  let initial := initialRawDescriptorState result mol fuel
  let annotated := rawAnnotatedCenters result
  if initial.isEmpty then
    match twoAccepted : solveExactCircularPositionDependencies? result mol fuel annotated with
    | some facts =>
        let unique :=
          (solveExactCircularPositionDependencies?_eq_some_iff result mol fuel annotated facts).mp
            twoAccepted
        ⟨facts, Or.inr (Or.inr (Or.inl unique))⟩
    | none =>
        match fourAccepted : solveExactFourCenterCircularDependencies? result mol fuel annotated with
        | some facts =>
            let unique :=
              (solveExactFourCenterCircularDependencies?_unique result mol fuel annotated facts
                fourAccepted).1
            ⟨facts, Or.inr (Or.inr (Or.inr (Or.inl unique)))⟩
        | none =>
            let selected := certifiedConstructiveRawDescriptorSource result mol fuel initial
            ⟨selected.val, by
              rcases selected.property with empty | fixed | unique
              · exact Or.inl empty
              · exact Or.inr (Or.inl fixed)
              · exact Or.inr (Or.inr (Or.inr (Or.inr unique)))⟩
  else
    let selected := certifiedConstructiveRawDescriptorSource result mol fuel initial
    ⟨selected.val, by
      rcases selected.property with empty | fixed | unique
      · exact Or.inl empty
      · exact Or.inr (Or.inl fixed)
      · exact Or.inr (Or.inr (Or.inr (Or.inr unique)))⟩






def discoverRawDescriptorSource (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel : ℕ) : RawDescriptorState :=
  (certifiedRawDescriptorSource result mol fuel).val

/-- Every production source is either unreported, constructively idempotent, or the unique member
of a bounded simultaneous positional/descriptor search. -/
theorem discoverRawDescriptorSource_certified (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel : ℕ) :
    IsCertifiedRawDescriptorSource result mol fuel
      (discoverRawDescriptorSource result mol fuel) :=
  (certifiedRawDescriptorSource result mol fuel).property.isCertified result mol fuel




theorem discoverRawDescriptorSource_canonical (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel : ℕ) :
    IsCanonicalRawDescriptorSource result mol fuel
      (discoverRawDescriptorSource result mol fuel) :=
  (certifiedRawDescriptorSource result mol fuel).property

/-- The full pre-normalization production output is empty or carries a machine-checked uniqueness
certificate appropriate to the algorithmic branch that produced it. -/
theorem discoverRawDescriptorSource_unique (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel : ℕ) :
    IsUniqueRawDescriptorSource result mol fuel
      (discoverRawDescriptorSource result mol fuel) :=
  (discoverRawDescriptorSource_canonical result mol fuel).isUnique result mol fuel

/-- Molecule-wide descriptor-dependent fixed point, followed by occurrence-frame normalization. -/
def discoverRawDescriptors (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel : ℕ) : RawDescriptorState :=
  normalizeTwoCyclicRule6AnchorCarrier mol fuel
    (discoverRawDescriptorSource result mol fuel)

/-- Top-level production boundary: the reported list is the occurrence-frame normalization of a
source that is either empty, constructively idempotent, or uniquely accepted by a simultaneous
positional/descriptor fixed-point search.  Fuel exhaustion has no reporting branch. -/
theorem discoverRawDescriptors_certified (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel : ℕ) :
    ∃ source,
      discoverRawDescriptors result mol fuel =
          normalizeTwoCyclicRule6AnchorCarrier mol fuel source ∧
        IsCertifiedRawDescriptorSource result mol fuel source := by
  refine ⟨discoverRawDescriptorSource result mol fuel, rfl, ?_⟩
  exact discoverRawDescriptorSource_certified result mol fuel

/-- Strengthened top-level boundary: the reported descriptor list is the deterministic
occurrence-frame normalization of a source whose producing branch carries a uniqueness proof. -/
theorem discoverRawDescriptors_unique (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (fuel : ℕ) :
    ∃ source,
      discoverRawDescriptors result mol fuel =
          normalizeTwoCyclicRule6AnchorCarrier mol fuel source ∧
        IsUniqueRawDescriptorSource result mol fuel source := by
  refine ⟨discoverRawDescriptorSource result mol fuel, rfl, ?_⟩
  exact discoverRawDescriptorSource_unique result mol fuel

/-- Result of checking whether a double bond has two distinguishable substituents at each end. -/
inductive DoubleBondStereogenicity where
  | stereogenic
  | notStereogenic
  | unresolved
  deriving DecidableEq, Repr

/-- Whether a double bond could carry `E/Z` at all.

Both ends must bear two substituents that the ranking can tell apart.  A carbonyl oxygen has none,
and a terminal `=CH₂` has two identical hydrogens; neither is a stereogenic unit, and reporting them
as refusals would bury the real results under noise.  `mol` is expected to have explicit
hydrogens. -/
def doubleBondStereogenicity (mol : RawMolecule) (_fuel left right : ℕ) :
    DoubleBondStereogenicity :=
  let endStatus : ℕ → ℕ → DoubleBondStereogenicity := fun atom partner =>
    match (mol.writtenNeighbors atom).filter (fun other => other != partner) with
    | [a, b] =>
        match mol.compareBranchesAuthoritativeStatus atom a b with
        | .lower | .higher =>
            DoubleBondStereogenicity.stereogenic
        | .tied => DoubleBondStereogenicity.notStereogenic
        | .unresolved => DoubleBondStereogenicity.unresolved
    | [_] =>
        if mol.doubleBondEndpointHasLonePairSide atom partner then
          DoubleBondStereogenicity.stereogenic
        else
          DoubleBondStereogenicity.notStereogenic
    | _ => DoubleBondStereogenicity.notStereogenic
  match endStatus left right, endStatus right left with
  | DoubleBondStereogenicity.notStereogenic, _
  | _, DoubleBondStereogenicity.notStereogenic => DoubleBondStereogenicity.notStereogenic
  | DoubleBondStereogenicity.unresolved, _
  | _, DoubleBondStereogenicity.unresolved => DoubleBondStereogenicity.unresolved
  | DoubleBondStereogenicity.stereogenic, DoubleBondStereogenicity.stereogenic =>
      DoubleBondStereogenicity.stereogenic

/-! ### Extended and coupled geometrical units -/

/-- Double-bond neighbours of an atom in the localized molecular graph. -/
def RawMolecule.doubleBondNeighbors (mol : RawMolecule) (atom : ℕ) : List ℕ :=
  (mol.bonds.filterMap fun bond =>
    if bond.kind != ParsedBondKind.double then none
    else if bond.source == atom then some bond.target
    else if bond.target == atom then some bond.source
    else none).eraseDups

/-- Follow a nonbranching cumulated-double-bond chain away from an endpoint. -/
def RawMolecule.walkCumulatedChain (mol : RawMolecule) : ℕ → ℕ → ℕ → List ℕ
  | 0, _, current => [current]
  | fuel + 1, previous, current =>
      match (mol.doubleBondNeighbors current).filter fun atom => atom != previous with
      | [next] => current :: mol.walkCumulatedChain fuel current next
      | _ => [current]

/-- Maximal cumulated-double-bond chains, represented once in endpoint order.

A chain with two atoms is an ordinary alkene and is deliberately omitted here.  Longer chains are
extended geometrical units whose terminal atoms, rather than each internal double bond, carry the
configuration. -/
def RawMolecule.extendedDoubleBondChains (mol : RawMolecule) : List (List ℕ) :=
  (List.range mol.atomCount).filterMap fun endpoint =>
    match mol.doubleBondNeighbors endpoint with
    | [next] =>
        let chain := endpoint :: mol.walkCumulatedChain (mol.atomCount + 1) endpoint next
        match chain.getLast? with
        | some other =>
            if 2 < chain.length && endpoint < other &&
                (mol.doubleBondNeighbors other).length == 1 then some chain else none
        | none => none
    | _ => none

/-- An odd-length cumulene whose middle atom carries OpenSMILES extended-tetrahedral parity.

The parity-bearing middle atom is not an ordinary tetrahedral center: it has the two axis bonds as
its only written neighbours.  The terminal atoms carry the stereogenic-unit occurrences seen by
the hierarchical digraph. -/
structure ExtendedTetrahedralParityCarrier where
  left : ℕ
  leftPartner : ℕ
  parityCarrier : ℕ
  rightPartner : ℕ
  right : ℕ
  path : List ℕ
  parity : TetrahedralInputParity
  deriving DecidableEq, Repr

/-- Parser-visible extended-tetrahedral parity carriers with an even number of cumulated double
bonds. -/
def RawMolecule.extendedTetrahedralParityCarriers (mol : RawMolecule) :
    List ExtendedTetrahedralParityCarrier :=
  mol.extendedDoubleBondChains.filterMap fun chain =>
    if chain.length % 2 != 1 then none else do
      let middle := chain.length / 2
      let parityCarrier := chain.getD middle 0
      let towardStart := chain.getD (middle - 1) 0
      let towardFinish := chain.getD (middle + 1) 0
      let spec ← mol.atomAt? parityCarrier
      let parity ← spec.tetrahedral?
      -- The maximal-chain enumerator orients endpoints by atom index, while OpenSMILES parity
      -- is expressed in the central atom's written-neighbour order.  Orient the entire path by
      -- the latter so renumbering cannot silently reverse the collapsed-tetrahedron frame.
      match mol.writtenNeighbors parityCarrier with
      | [writtenFirst, writtenSecond] =>
          if !((writtenFirst == towardStart && writtenSecond == towardFinish) ||
              (writtenFirst == towardFinish && writtenSecond == towardStart)) then none else
          let oriented := if writtenFirst == towardStart then chain else chain.reverse
          let reversed := oriented.reverse
          some { left := oriented.getD 0 0
                 leftPartner := oriented.getD 1 0
                 parityCarrier := parityCarrier
                 rightPartner := reversed.getD 1 0
                 right := reversed.getD 0 0
                 path := oriented
                 parity := parity }
      | _ => none

/-- Whether an annotated atom is an extended-tetrahedral parity carrier rather than a tetrahedral
center to be reported on its own. -/
def RawMolecule.isExtendedTetrahedralParityCarrier (mol : RawMolecule) (atom : ℕ) : Bool :=
  mol.extendedTetrahedralParityCarriers.any fun carrier => carrier.parityCarrier == atom

/-- Assign `Rₐ/Sₐ` to an OpenSMILES extended-tetrahedral allene carrier.

OpenSMILES defines the parity by collapsing the allene-like system to one tetrahedral carrier.
The virtual written-neighbor order is the two off-axis substituents at the first written axis end,
followed by the two at the second.  IUPAC axial perception requires only a strict priority within
each endpoint pair.  The resulting pairwise priority permutation is therefore fed through the same
parity convention as the collapsed tetrahedron. -/
def extendedTetrahedralAxialOutcome (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel : ℕ)
    (carrier : ExtendedTetrahedralParityCarrier) : StereoOutcome :=
  let leftLigands := (mol.writtenNeighbors carrier.left).filter fun atom =>
    atom != carrier.leftPartner
  let rightLigands := (mol.writtenNeighbors carrier.right).filter fun atom =>
    atom != carrier.rightPartner
  match leftLigands, rightLigands with
  | [leftFirst, leftSecond], [rightFirst, rightSecond] =>
      match compareBranchesThroughOfficialContext? result mol state fuel carrier.left
          leftFirst leftSecond,
        compareBranchesThroughOfficialContext? result mol state fuel carrier.right
          rightFirst rightSecond with
      | some Ordering.eq, _ | _, some Ordering.eq =>
          StereoOutcome.refused StereoRefusal.notStereogenic
      | none, _ | _, none =>
          StereoOutcome.refused StereoRefusal.rankingUnresolved
      | some leftDecision, some rightDecision =>
          let leftHigh := if leftDecision == Ordering.gt then 0 else 1
          let leftLow := if leftHigh == 0 then 1 else 0
          let rightHigh := if rightDecision == Ordering.gt then 2 else 3
          let rightLow := if rightHigh == 2 then 3 else 2
          let sense := RawMolecule.descriptorOfParity carrier.parity
            (RawMolecule.permutationIsEven [leftHigh, leftLow, rightHigh, rightLow])
          StereoOutcome.axial (match sense with | RS.R => .Ra | RS.S => .Sa)
  | _, _ => StereoOutcome.refused StereoRefusal.rankingUnresolved

/-- Public assignment carried by one parser-perceived extended-tetrahedral axis.  Naming this
adapter separately lets the conformance layer prove the unit identity and the axial outcome
without unfolding the whole normalized analyzer. -/
def extendedTetrahedralAxialAssignment (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel : ℕ)
    (carrier : ExtendedTetrahedralParityCarrier) : StereoAssignment :=
  { unit := StereoUnit.axis carrier.left carrier.right
    outcome := extendedTetrahedralAxialOutcome result mol state fuel carrier }

/-- Lowercase axial `m/p` evidence at one real terminal occurrence of an extended tetrahedron.

Both terminals are interpreted in the parity carrier's written-axis frame.  Moving the occurrence
from one end of that axis to the other reverses its local view, as does exchanging the selected
off-axis substituent.  The descriptor is kept in the official `m/p` family throughout; it is never
encoded as tetrahedral `R/S`. -/
def extendedTetrahedralPseudoOccurrenceDescriptor? (mol : RawMolecule)
    (node : RawMolecule.CanonicalBranchNode) :
    Option OfficialPseudoasymmetricDescriptor := do
  if node.provenance != RawMolecule.CanonicalNodeProvenance.realAtom then none else
  let carrier ← mol.extendedTetrahedralParityCarriers.find? fun candidate =>
    candidate.left == node.atom || candidate.right == node.atom
  let axisPartner := if node.atom == carrier.left then carrier.leftPartner else carrier.rightPartner
  let offAxis := (mol.writtenNeighbors node.atom).filter fun atom =>
    atom != axisPartner
  if offAxis.length != 2 then none else
  let first := offAxis.getD 0 0
  let second := offAxis.getD 1 0
  if !mol.hasConstitutionAutomorphismSwapping node.atom first second then none else
  let parentIsFirst ←
    if node.parent == first then some true
    else if node.parent == second then some false
    else none
  let evenOccurrence := (node.atom == carrier.right) == parentIsFirst
  match carrier.parity with
  | TetrahedralInputParity.anticlockwise =>
      some (if evenOccurrence then OfficialPseudoasymmetricDescriptor.p
        else OfficialPseudoasymmetricDescriptor.m)
  | TetrahedralInputParity.clockwise =>
      some (if evenOccurrence then OfficialPseudoasymmetricDescriptor.m
        else OfficialPseudoasymmetricDescriptor.p)

/-- Exact occurrence-local lowercase axial sequence on one ligand branch.

The caller accepts only a singleton on each side.  Multiple axial occurrences therefore remain
unresolved until their positional hierarchy is implemented instead of being flattened. -/
def branchExtendedTetrahedralPseudoSequenceCapFree? (mol : RawMolecule) (center ligand : ℕ) :
    Option (List OfficialPseudoasymmetricDescriptor) := do
  let nodes ← collectCanonicalTreeAuthoritative mol (mol.atomCount + 1)
    [RawMolecule.canonicalRoot center ligand]
  some (nodes.filterMap (extendedTetrahedralPseudoOccurrenceDescriptor? mol))

/-- Public axial occurrence sequence routed through cap-free occurrence collection. -/
def branchExtendedTetrahedralPseudoSequence? (mol : RawMolecule) (center ligand : ℕ) :
    Option (List OfficialPseudoasymmetricDescriptor) :=
  branchExtendedTetrahedralPseudoSequenceCapFree? mol center ligand

/-- Compare the sole corresponding extended-tetrahedral `m/p` occurrence on two tied branches. -/
def compareBranchesThroughExtendedTetrahedralPseudo? (mol : RawMolecule)
    (center left right : ℕ) : Option Ordering := do
  let leftDescriptors ← branchExtendedTetrahedralPseudoSequence? mol center left
  let rightDescriptors ← branchExtendedTetrahedralPseudoSequence? mol center right
  match leftDescriptors, rightDescriptors with
  | [leftDescriptor], [rightDescriptor] =>
      OfficialPseudoasymmetricDescriptor.compare? leftDescriptor rightDescriptor
  | _, _ => none

/-- A center ranking that records whether lowercase extended-tetrahedral evidence was consumed. -/
structure ExtendedTetrahedralPseudoRanking where
  positions : List ℕ
  usedPseudoOccurrence : Bool
  deriving DecidableEq, Repr

/-- Rank an ordinary tetrahedral center through one guarded occurrence-local `m/p` boundary. -/
def rankBranchPositionsThroughExtendedTetrahedralPseudoAuthoritative? (mol : RawMolecule)
    (center : ℕ) (ligands : List ℕ) : Option ExtendedTetrahedralPseudoRanking := do
  if ligands.length != 4 then none else
  let atomOf := fun position => ligands.getD position 0
  let compareAt := fun left right =>
    match mol.compareBranchesAuthoritativeStatus center (atomOf left) (atomOf right) with
    | RawMolecule.BranchComparisonStatus.lower => some (Ordering.lt, false)
    | RawMolecule.BranchComparisonStatus.higher => some (Ordering.gt, false)
    | RawMolecule.BranchComparisonStatus.unresolved => none
    | RawMolecule.BranchComparisonStatus.tied => do
        let decision ← compareBranchesThroughExtendedTetrahedralPseudo? mol center
          (atomOf left) (atomOf right)
        some (decision, decision != Ordering.eq)
  let positions := sortDescBy (fun left right =>
    (compareAt left right).map Prod.fst != some Ordering.lt) (List.range ligands.length)
  let adjacent ← (List.range (positions.length - 1)).mapM fun rank => do
    let left ← positions[rank]?
    let right ← positions[rank + 1]?
    compareAt left right
  if !(adjacent.all fun decision => decision.1 != Ordering.eq) then none else
    some { positions := positions
           usedPseudoOccurrence := adjacent.any Prod.snd }

/-- Public extended-tetrahedral pseudo ranking through the width-unbounded comparator. -/
def rankBranchPositionsThroughExtendedTetrahedralPseudo? (mol : RawMolecule)
    (_fuel center : ℕ) (ligands : List ℕ) : Option ExtendedTetrahedralPseudoRanking :=
  rankBranchPositionsThroughExtendedTetrahedralPseudoAuthoritative? mol center ligands

/-- Descriptor fact produced from an exact lowercase axial occurrence comparison. -/
def tetrahedralFactThroughExtendedTetrahedralPseudo? (mol : RawMolecule)
    (fuel idx : ℕ) : Option RawDescriptorFact := do
  let spec ← mol.atomAt? idx
  let parity ← spec.tetrahedral?
  let ligands := mol.ligandsWithLonePair idx
  let ranking ← rankBranchPositionsThroughExtendedTetrahedralPseudo? mol fuel idx ligands
  if !ranking.usedPseudoOccurrence then none else
  some { atom := idx
         descriptor := RawMolecule.descriptorOfParity parity
           (RawMolecule.permutationIsEven ranking.positions)
         uppercase := false
         evidenceSize := 1
         decisiveRule? := some CIPRuleFamily.pseudoasymmetricDescriptor
         descriptorDependentPairs := 1
         priorityPositions := ranking.positions }

/-- Stereo of an extended cumulated unit from the CIP-senior substituent side at each terminal. -/
def ChemistryNormalizationResult.extendedDoubleBondStereo?
    (result : ChemistryNormalizationResult) (chain : List ℕ) : Option DoubleBondStereo :=
  match chain, chain.reverse with
  | left :: leftPartner :: _, right :: rightPartner :: _ =>
      match result.seniorSideAt? left leftPartner, result.seniorSideAt? right rightPartner with
      | some leftSide, some rightSide =>
          some (StereobondSemantics.stereoFromDirectionalMarkers leftSide rightSide)
      | _, _ => none
  | _, _ => none

/-- Senior substituent using the width-unbounded constitutional comparator followed by the
descriptor-rich official context.

The one-substituent case is the direct atom-versus-implicit-hydrogen/lone-pair rule implemented by
`seniorAlkeneSubstituent?`.  A two-substituent endpoint never accepts that legacy helper's bounded
strict branch result: it is decided only by `compareBranchesThroughOfficialContext?`. -/
def seniorAlkeneSubstituentThroughOfficialContext? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel carbon partner : ℕ) : Option ℕ :=
  match mol.alkeneSubstituents carbon partner with
  | [_] => mol.seniorAlkeneSubstituent? fuel carbon partner
  | [left, right] =>
      match compareBranchesThroughOfficialContext? result mol state fuel carbon left right with
      | some Ordering.gt => some left
      | some Ordering.lt => some right
      | _ => none
  | _ => none

/-- Whether an alkene endpoint is separated only by the Rule-5 enantiomorphic tiebreak.

When exactly one endpoint has this property, the geometrical unit uses the reflection-variant
`seqCis/seqTrans` family rather than ordinary `E/Z`. -/
def alkeneEndpointUsesPseudoasymmetricTiebreak (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel carbon partner : ℕ) : Bool :=
  match mol.alkeneSubstituents carbon partner with
  | [left, right] =>
      decisiveOfficialFamilyForBranches? result mol state fuel carbon left right ==
        some CIPRuleFamily.pseudoasymmetricTiebreak
  | _ => false

/-- Nearest uppercase carrier identities on one alkene substituent branch. -/
def nearestUppercaseCarrierAtoms (mol : RawMolecule) (state : RawDescriptorState)
    (carbon branch : ℕ) : List ℕ :=
  let candidates := state.filterMap fun fact =>
    if !fact.uppercase then none else
      (mol.rule6ReferenceDistance? carbon fact.atom (mol.atomCount + 1) 0 [branch] [branch]).map
        fun distance => (distance, fact.atom)
  match candidates with
  | [] => []
  | first :: rest =>
      let nearest := rest.foldl (fun distance candidate => Nat.min distance candidate.1) first.1
      (candidates.filterMap fun candidate =>
        if candidate.1 == nearest then some candidate.2 else none).eraseDups

/-- Whether Rule 5 was decided by two occurrences of one unique nearest carrier center.

Merely finding some uppercase fact reachable through both ring arms is insufficient: an unrelated
deeper center may be common to both branches after the actual Rule-5 boundary.  Require the same
single carrier to be nearest on each side and independently verify that Rule 5 is the endpoint's
decisive official comparison. -/
def alkeneEndpointUsesSharedOccurrenceCarrier (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel carbon partner : ℕ) : Bool :=
  match mol.alkeneSubstituents carbon partner with
  | [left, right] =>
      decisiveOfficialFamilyForBranches? result mol state fuel carbon left right ==
          some CIPRuleFamily.pseudoasymmetricTiebreak &&
        match nearestUppercaseCarrierAtoms mol state carbon left,
            nearestUppercaseCarrierAtoms mol state carbon right with
        | [leftCarrier], [rightCarrier] => leftCarrier == rightCarrier
        | _, _ => false
  | _ => false

/-- Transport terminal geometry through one legacy coupled-network endpoint frame.

This helper is retained only for the coupled-network adapter.  Direct senior-side comparisons,
including odd cumulenes, already inhabit the final terminal reference frame and must not be
transported merely because one endpoint is decided by Rule 5. -/
def transportPseudoGeometry (stereo : DoubleBondStereo) (pseudo : Bool) : DoubleBondStereo :=
  if !pseudo then stereo else
    match stereo with
    | DoubleBondStereo.E => DoubleBondStereo.Z
    | DoubleBondStereo.Z => DoubleBondStereo.E
    | DoubleBondStereo.unspecified => DoubleBondStereo.unspecified

/-- Side of a descriptor-rich CIP-senior substituent at one double-bond endpoint. -/
def seniorSideThroughOfficialContext? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel carbon partner : ℕ) :
    Option DirectionalBondMarker :=
  match seniorAlkeneSubstituentThroughOfficialContext? result mol state fuel carbon partner with
  | none => none
  | some senior =>
      let seniorMarker? := result.stereobonds.substituentSideMarker? carbon senior
      let otherMarker? :=
        match (mol.alkeneSubstituents carbon partner).filter fun atom => atom != senior with
        | [other] => result.stereobonds.substituentSideMarker? carbon other
        | _ => none
      match seniorMarker?, otherMarker? with
      | some seniorSide, some otherSide =>
          if seniorSide == otherSide.flip then some seniorSide else none
      | some seniorSide, none => some seniorSide
      | none, some otherSide => some otherSide.flip
      | none, none => none

/-- Stereo of a geometrical unit whose terminal ligand priority depends on Rules 3–5. -/
def ChemistryNormalizationResult.cipDoubleBondStereoThroughOfficialContext?
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (fuel left right : ℕ) : Option DoubleBondStereo :=
  match seniorSideThroughOfficialContext? result mol state fuel left right,
      seniorSideThroughOfficialContext? result mol state fuel right left with
  | some leftSide, some rightSide =>
      some (StereobondSemantics.stereoFromDirectionalMarkers leftSide rightSide)
  | _, _ => none

/-- Perceived double-bond geometry on the authoritative priority path.  A specified stored
assignment is direct geometry evidence; otherwise the sides of the two Rules-1a--5 senior
substituents determine `E/Z`. -/
def ChemistryNormalizationResult.perceivedDoubleBondStereoThroughOfficialContext?
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (fuel left right : ℕ) : Option DoubleBondStereo :=
  Option.first (result.stereobonds.storedDoubleBondStereo? left right)
    (result.cipDoubleBondStereoThroughOfficialContext? mol state fuel left right)

/-- One connected network of geometrical units coupled through a proved Rule-3 perfect matching. -/
structure CoupledGeometryNetwork where
  carrier? : Option ℕ := none
  units : List (ℕ × ℕ)
  stereo : DoubleBondStereo
  rule6Pseudo : Bool
  deriving DecidableEq, Repr

/-- Compile one ordered coupled-geometry network around its shared topology carrier.

The perfect-matching witness proves that exactly two physical units partition the carrier's four
constitutionally tied ligand occurrences.  Units are retained in that occurrence order, and every
one must have usable marker evidence at both endpoints.  Thus unrelated geometrical units elsewhere
in the molecule cannot enter this network or alter its parity. -/
def coupledGeometryNetworkAt? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : ℕ) : Option CoupledGeometryNetwork := do
  if !result.hasCoupledRule3PerfectMatching mol fuel center then none else
  let occurrences := (mol.ligandsWithLonePair center).flatMap fun ligand =>
    result.rule3GeometryOccurrencesOnBranch mol center ligand
  let units := (occurrences.map fun occurrence =>
    (occurrence.left, occurrence.right)).eraseDups
  let assignments ← units.mapM fun unit =>
    result.stereobonds.doubleBondAssignments.find? fun assignment =>
      min assignment.1 assignment.2.1 == unit.1 && max assignment.1 assignment.2.1 == unit.2
  if assignments.length < 2 || !(assignments.all fun assignment =>
      doubleBondStereogenicity mol fuel assignment.1 assignment.2.1 ==
          DoubleBondStereogenicity.notStereogenic &&
        !(result.stereobonds.directionalMarkersAtSide assignment.1 assignment.2.1).isEmpty &&
        !(result.stereobonds.directionalMarkersAtSide assignment.2.1 assignment.1).isEmpty) then
    none
  else
    let terminalMarkers := assignments.flatMap fun assignment =>
      [ result.stereobonds.directionalMarkersAtSide assignment.1 assignment.2.1,
        result.stereobonds.directionalMarkersAtSide assignment.2.1 assignment.1 ].filterMap
          fun markers => match markers with | [marker] => some marker | _ => none
    match terminalMarkers with
    | [first, last] =>
        let terminalStereo :=
          StereobondSemantics.stereoFromDirectionalMarkers first last
        let stereo :=
          if assignments.length % 2 == 1 then
            match terminalStereo with
            | DoubleBondStereo.E => DoubleBondStereo.Z
            | DoubleBondStereo.Z => DoubleBondStereo.E
            | DoubleBondStereo.unspecified => DoubleBondStereo.unspecified
          else terminalStereo
        let rule6Pseudo := (state.factAt? center).any fun fact =>
          fact.uppercase && fact.evidenceSize == 1 && fact.decisiveRule?.isNone &&
            mol.atomLiesInCycle fuel center
        if stereo == DoubleBondStereo.unspecified then none else
          some { carrier? := some center, units := units, stereo := stereo,
                 rule6Pseudo := rule6Pseudo }
    | _ => none

/-- Endpoint sides that continue into another unit of a marker-coupled geometry chain. -/
def coupledInternalMarkerEndpoints (result : ChemistryNormalizationResult)
    (assignment : ℕ × ℕ × DoubleBondStereo) : List ℕ :=
  [assignment.1, assignment.2.1].filter fun endpoint =>
    let partner := if endpoint == assignment.1 then assignment.2.1 else assignment.1
    (result.stereobonds.directionalMarkersAtSide endpoint partner).length != 1

/-- Reachability while excluding every atom in a bounded forbidden set. -/
def RawMolecule.reachesAvoidingAtoms (mol : RawMolecule) (forbidden : List ℕ) (target : ℕ) :
    ℕ → List ℕ → List ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, frontier, seen =>
      if frontier.contains target then true else
        let next := (frontier.flatMap fun atom =>
          (mol.incidentAtoms atom).filter fun neighbor =>
            !forbidden.contains neighbor && !seen.contains neighbor).eraseDups
        if next.isEmpty then false else
          mol.reachesAvoidingAtoms forbidden target fuel next (seen ++ next)

/-- Whether two endpoints lie in one cyclic connector block.

Two distinct first steps from `left` that can still reach `right` after `left` is removed witness
the two ring arms needed to transport a coupled geometrical frame.  Endpoints belonging to other
candidate units are forbidden, so a more distant unit cannot jump across an intervening one. -/
def coupledEndpointsShareCycle (mol : RawMolecule) (forbidden : List ℕ)
    (left right : ℕ) : Bool :=
  if left == right then false else
    (((mol.incidentAtoms left).filter fun neighbor => !forbidden.contains neighbor).countP
      fun neighbor =>
        mol.reachesAvoidingAtoms (left :: forbidden) right (mol.atomCount + 1)
          [neighbor] [neighbor]) ≥ 2

/-- Two coupled units meet through a common substituent or one cyclic connector block. -/
def coupledAssignmentsAdjacent (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (candidates : List (ℕ × ℕ × DoubleBondStereo))
    (left right : ℕ × ℕ × DoubleBondStereo) : Bool :=
  let forbidden := (candidates.filter fun candidate => candidate != left && candidate != right).flatMap
    fun candidate => [candidate.1, candidate.2.1]
  (coupledInternalMarkerEndpoints result left).any fun leftEndpoint =>
    (coupledInternalMarkerEndpoints result right).any fun rightEndpoint =>
      ((mol.incidentAtoms leftEndpoint).any fun connector =>
        !forbidden.contains connector && (mol.incidentAtoms rightEndpoint).contains connector) ||
        coupledEndpointsShareCycle mol forbidden leftEndpoint rightEndpoint

/-- Bounded reachability in the candidate-unit adjacency graph. -/
def collectCoupledAssignmentComponent (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (candidates : List (ℕ × ℕ × DoubleBondStereo)) :
    ℕ → List (ℕ × ℕ × DoubleBondStereo) → List (ℕ × ℕ × DoubleBondStereo) →
      List (ℕ × ℕ × DoubleBondStereo)
  | 0, _, seen => seen
  | fuel + 1, frontier, seen =>
      let next := candidates.filter fun candidate =>
        !seen.contains candidate && frontier.any fun current =>
          coupledAssignmentsAdjacent result mol candidates current candidate
      if next.isEmpty then seen else
        collectCoupledAssignmentComponent result mol candidates fuel next (seen ++ next)

/-- Compile a single ordered path network directly from its marker junctions.

Exactly two degree-one units and degree-two internal units make the connected candidate graph a
path.  This covers cyclic coupled geometries without a tetrahedral carrier while rejecting an
unrelated second marker component. -/
def markerCoupledGeometryNetwork? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (candidates : List (ℕ × ℕ × DoubleBondStereo)) :
    Option CoupledGeometryNetwork := do
  if candidates.length < 2 then none else
  let degrees := candidates.map fun candidate =>
    (candidates.filter fun other =>
      other != candidate && coupledAssignmentsAdjacent result mol candidates candidate other).length
  let internalDegreesMatch := (candidates.zip degrees).all fun entry =>
    let internalCount := (coupledInternalMarkerEndpoints result entry.1).length
    (internalCount == 1 || internalCount == 2) && entry.2 == internalCount
  if !internalDegreesMatch || degrees.count 1 != 2 then none else
  let first ← candidates.head?
  let connected := collectCoupledAssignmentComponent result mol candidates
    (candidates.length + 1) [first] [first]
  if connected.length != candidates.length then none else
  let terminalMarkers := candidates.flatMap fun assignment =>
    [ result.stereobonds.directionalMarkersAtSide assignment.1 assignment.2.1,
      result.stereobonds.directionalMarkersAtSide assignment.2.1 assignment.1 ].filterMap
        fun markers => match markers with | [marker] => some marker | _ => none
  match terminalMarkers with
  | [firstMarker, lastMarker] =>
      let terminalStereo :=
        StereobondSemantics.stereoFromDirectionalMarkers firstMarker lastMarker
      let stereo :=
        if candidates.length % 2 == 1 then
          match terminalStereo with
          | DoubleBondStereo.E => DoubleBondStereo.Z
          | DoubleBondStereo.Z => DoubleBondStereo.E
          | DoubleBondStereo.unspecified => DoubleBondStereo.unspecified
        else terminalStereo
      if stereo == DoubleBondStereo.unspecified then none else
        some { units := candidates.map fun assignment =>
                 (min assignment.1 assignment.2.1, max assignment.1 assignment.2.1)
               stereo := stereo, rule6Pseudo := false }
  | _ => none

/-- The ligand frame admitted by descriptor-independent, connectivity-only tetrahedral
perception.

Four *atom* ligands provide a constitutional tetrahedral-center candidate after hydrogen
materialization.  A three-coordinate heteroatom does not: adding a phantom lone-pair position is
valid only after trigonal-pyramidal geometry has been established by configuration or geometry
evidence.  In particular, connectivity alone must not turn the trigonal-planar nitrogen of an
ordinary amide into a tetrahedral stereogenic unit.  Explicit `@`/`@@` assignment continues to use
`ligandsWithLonePair`, because that path carries a written configuration observation. -/
def connectivityOnlyTetrahedralLigands?
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (idx : ℕ) :
    Option (List ℕ) :=
  match result.parsed.atomAt? idx with
  | none => none
  | some spec =>
      if !RawMolecule.centreElementSupported spec.element ||
          mol.isExtendedTetrahedralParityCarrier idx then
        none
      else
        let ligands := mol.writtenNeighbors idx
        if ligands.length == 4 then some ligands else none

/-- A proved terminal constitutional tie in a four-atom tetrahedral frame. -/
def hasTerminalTetrahedralTie (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel idx : ℕ)
    (ligands : List ℕ) : Bool :=
  (List.range ligands.length).any fun left =>
    (List.range ligands.length).any fun right =>
      left < right &&
        mol.canonicalTerminal (RawMolecule.canonicalRoot idx
          (ligands.getD left 0)) &&
        mol.canonicalTerminal (RawMolecule.canonicalRoot idx
          (ligands.getD right 0)) &&
        compareBranchesThroughOfficialContext? result mol state fuel idx
          (ligands.getD left 0) (ligands.getD right 0) == some Ordering.eq

/-- Perceive an ordinary tetrahedral stereogenic unit without consulting input parity.

This separates the chemical question "are the four ligand positions distinguishable under the
complete currently encoded sequence-rule environment?" from the geometric question needed to
choose `R` or `S`. -/
def tetrahedralStereogenicity (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel idx : ℕ) :
    TetrahedralStereogenicity :=
  match connectivityOnlyTetrahedralLigands? result mol idx with
  | none => .notCandidate
  | some ligands =>
      match rankBranchPositionsThroughOfficialContext? result mol state fuel idx ligands with
      | some _ => .stereogenic
      | none =>
          if hasTerminalTetrahedralTie result mol state fuel idx ligands then
            .notStereogenic
          else
            match tetrahedralRule6Stereogenicity? result mol state fuel idx with
            | some true => .stereogenic
            | some false => .notStereogenic
            | none => .unresolved

/-- Perceive an ordinary tetrahedral stereogenic center even when no input parity was supplied.

This is deliberately a perception function, not a descriptor function: without coordinates,
wedge/hash bonds, or an `@`/`@@` carrier the absolute configuration is unavailable.  A strict
four-ligand order through the stabilized Rules 1--5 environment or the checked Rule-6 carrier is
nevertheless sufficient to establish that the constitutional center is stereogenic, so the public
analyzer reports the unit as configuration-unspecified instead of omitting it.  Exhausted
comparisons are reported as unresolved; only a proved nonstereogenic result is omitted. -/
def unannotatedTetrahedralOutcome? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel idx : ℕ) : Option StereoOutcome :=
  match result.parsed.atomAt? idx with
  | none => none
  | some spec =>
      if spec.tetrahedral?.isSome then none
      else
        match tetrahedralStereogenicity result mol state fuel idx with
        | .stereogenic => some (StereoOutcome.refused StereoRefusal.notSpecified)
        | .unresolved => some (StereoOutcome.refused StereoRefusal.rankingUnresolved)
        | .notStereogenic | .notCandidate => none

/-- Public outcome conversion for a stabilized descriptor fact. -/
def rawDescriptorFactOutcome (fact : RawDescriptorFact) : StereoOutcome :=
  if fact.uppercase then StereoOutcome.tetrahedral fact.descriptor
  else StereoOutcome.pseudoTetrahedral
    (match fact.descriptor with | RS.R => PseudoRS.r | RS.S => PseudoRS.s)

/-- Analyze one annotated ordinary tetrahedral center without accepting a bounded comparator's
strict result as authoritative.

A stabilized Rules-3--6 fact wins when present.  Otherwise Rules 1--5 are ranked through the
width-unbounded official-context comparator.  Failure after that point is fail-closed: a checked
Rule-6 nonstereogenic result is retained, while every other inconclusive case is reported as
ranking-unresolved rather than emitting an unverified `R/S`. -/
def annotatedTetrahedralOutcome? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel idx : Nat) : Option StereoOutcome := do
  let spec ← result.parsed.atomAt? idx
  let parity ← spec.tetrahedral?
  if mol.isExtendedTetrahedralParityCarrier idx then none else
  match Option.first (state.factAt? idx)
      (tetrahedralFactThroughExtendedTetrahedralPseudo? mol fuel idx) with
  | some fact => some (rawDescriptorFactOutcome fact)
  | none =>
      if !RawMolecule.centreElementSupported spec.element then
        some (StereoOutcome.refused StereoRefusal.unsupportedCentreElement)
      else
        let ligands := mol.ligandsWithLonePair idx
        if ligands.length != 4 then
          some (StereoOutcome.refused (StereoRefusal.wrongLigandCount ligands.length))
        else
          match rankBranchPositionsThroughOfficialContext?
              result mol state fuel idx ligands with
          | some positions =>
              some (StereoOutcome.tetrahedral
                (RawMolecule.descriptorOfParity parity
                  (RawMolecule.permutationIsEven positions)))
          | none =>
              match tetrahedralRule6Stereogenicity? result mol state fuel idx with
              | some false => some (StereoOutcome.refused StereoRefusal.notStereogenic)
              | some true | none =>
                  some (StereoOutcome.refused StereoRefusal.rankingUnresolved)

/-- Assignment adapter for one annotated ordinary tetrahedral center. -/
def annotatedTetrahedralAssignment? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel idx : Nat) :
    Option StereoAssignment :=
  (annotatedTetrahedralOutcome? result mol state fuel idx).map fun outcome =>
    { unit := StereoUnit.tetrahedral idx, outcome := outcome }

/-- Analyze one parsed atom through the annotated or unannotated ordinary-tetrahedral branch
selected by its input parity evidence. -/
def tetrahedralAssignment? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel idx : Nat) :
    Option StereoAssignment :=
  match result.parsed.atomAt? idx with
  | none => none
  | some spec =>
      match spec.tetrahedral? with
      | none =>
          (unannotatedTetrahedralOutcome? result mol state fuel idx).map fun outcome =>
            ({ unit := StereoUnit.tetrahedral idx, outcome := outcome } : StereoAssignment)
      | some _ => annotatedTetrahedralAssignment? result mol state fuel idx

/-- The complete ordinary-tetrahedral output sublist of the normalized analyzer. -/
def tetrahedralAssignments (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel : Nat) :
    List StereoAssignment :=
  (List.range result.parsed.atomCount).filterMap
    (tetrahedralAssignment? result mol state fuel)

/-- Analyze one parsed ordinary double-bond record through authoritative endpoint priorities and
senior-substituent geometry.  Naming this branch makes its P-92 perception and P-93 final
descriptor obligations independently stateable. -/
def ordinaryDoubleBondAssignment? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel : Nat)
    (assignment : Nat × Nat × DoubleBondStereo) : Option StereoAssignment :=
  let left := assignment.1
  let right := assignment.2.1
  match doubleBondStereogenicity mol fuel left right with
  | DoubleBondStereogenicity.notStereogenic => none
  | DoubleBondStereogenicity.unresolved =>
      some { unit := StereoUnit.doubleBond left right
             outcome := StereoOutcome.refused StereoRefusal.rankingUnresolved }
  | DoubleBondStereogenicity.stereogenic =>
      let outcome :=
        match result.perceivedDoubleBondStereoThroughOfficialContext?
            mol state fuel left right with
        | some DoubleBondStereo.unspecified =>
            StereoOutcome.refused StereoRefusal.markerEvidenceUnusable
        | some value => StereoOutcome.alkene value
        | none =>
            if (result.stereobonds.directionalMarkersAtSide left right).isEmpty &&
                (result.stereobonds.directionalMarkersAtSide right left).isEmpty then
              StereoOutcome.refused StereoRefusal.notSpecified
            else
              StereoOutcome.refused StereoRefusal.rankingUnresolved
      some { unit := StereoUnit.doubleBond left right, outcome := outcome }

/-- The complete ordinary-double-bond output sublist of the normalized analyzer. -/
def ordinaryDoubleBondAssignments (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel : Nat) :
    List StereoAssignment :=
  result.stereobonds.doubleBondAssignments.filterMap
    (ordinaryDoubleBondAssignment? result mol state fuel)

/-- The two terminal atoms and their inward partners in a maximal cumulated chain. -/
def cumulatedChainTerminalFrame? (chain : List Nat) : Option (Nat × Nat × Nat × Nat) :=
  match chain, chain.reverse with
  | left :: leftPartner :: _, right :: rightPartner :: _ =>
      some (left, leftPartner, right, rightPartner)
  | _, _ => none

theorem cumulatedChainTerminalFrame?_eq_some_length_at_least_two
    (chain : List Nat) (frame : Nat × Nat × Nat × Nat)
    (computed : cumulatedChainTerminalFrame? chain = some frame) :
    2 ≤ chain.length := by
  cases chain with
  | nil => simp [cumulatedChainTerminalFrame?] at computed
  | cons first rest =>
      cases rest with
      | nil => simp [cumulatedChainTerminalFrame?] at computed
      | cons second tail => simp

/-- Analyze one maximal cumulated chain in the P-93.4.2.3 planar parity class.

The chain contains one more atom than physical double bonds, so an even atom count selects an odd
number of cumulated double bonds.  The two CIP-senior terminal sides determine together/opposite
geometry.  If exactly one terminal ranking is decided by Rule 5, P-92 requires the
reflection-variant `seqCis/seqTrans` family; otherwise P-93 uses ordinary `Z/E`. -/
def oddCumuleneDoubleBondAssignment? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel : Nat)
    (chain : List Nat) : Option StereoAssignment :=
  if chain.length % 2 != 0 then none else
  match cumulatedChainTerminalFrame? chain with
  | some (left, leftPartner, right, rightPartner) =>
      let leftEnantiomorphic :=
        alkeneEndpointUsesPseudoasymmetricTiebreak result mol state fuel left leftPartner
      let rightEnantiomorphic :=
        alkeneEndpointUsesPseudoasymmetricTiebreak result mol state fuel right rightPartner
      match seniorSideThroughOfficialContext? result mol state fuel left leftPartner,
        seniorSideThroughOfficialContext? result mol state fuel right rightPartner with
      | some leftSide, some rightSide =>
          let geometry :=
            StereobondSemantics.stereoFromDirectionalMarkers leftSide rightSide
          let enantiomorphic := leftEnantiomorphic != rightEnantiomorphic
          some { unit := StereoUnit.doubleBond left right
                 outcome :=
                   if enantiomorphic then sequenceDoubleBondOutcomeOfGeometry geometry
                   else StereoOutcome.alkene geometry }
      | _, _ => none
  | none => none

/-- Complete P-93.4.2.3-parity sublist over parser-perceived maximal cumulated chains. -/
def oddCumuleneDoubleBondAssignments (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel : Nat) :
    List StereoAssignment :=
  result.parsed.extendedDoubleBondChains.filterMap
    (oddCumuleneDoubleBondAssignment? result mol state fuel)

/-- Analyze one ordinary physical double bond whose terminal ligand order becomes strict only in
the descriptor-bearing official context.

Both terminal sides returned by `cipDoubleBondStereoThroughOfficialContext?` already belong to the
CIP-senior ligands.  Their together/opposite relation is therefore the final P-92/P-93 reference
geometry: a Rule-5 endpoint changes the descriptor family to `seqCis/seqTrans`, but it does not
reverse that geometry a second time.  Network-coupled marker frames are handled separately. -/
def descriptorDependentDoubleBondAssignment? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel : Nat)
    (assignment : Nat × Nat × DoubleBondStereo) : Option StereoAssignment :=
  let left := assignment.1
  let right := assignment.2.1
  let leftEnantiomorphic :=
    alkeneEndpointUsesPseudoasymmetricTiebreak result mol state fuel left right
  let rightEnantiomorphic :=
    alkeneEndpointUsesPseudoasymmetricTiebreak result mol state fuel right left
  match result.cipDoubleBondStereoThroughOfficialContext? mol state fuel left right with
  | some geometry =>
      let enantiomorphic := leftEnantiomorphic != rightEnantiomorphic
      some { unit := StereoUnit.doubleBond left right
             outcome :=
               if enantiomorphic then sequenceDoubleBondOutcomeOfGeometry geometry
               else StereoOutcome.alkene geometry }
  | none => none

/-- Route one physical double-bond record after the ordinary branch has run.

Compiled coupled-marker networks are observations used while comparing ligand occurrences under
Rule 3; they are not themselves final stereogenic double-bond units.  In particular, their
compiler intentionally selects records whose descriptor-independent double-bond perception is
`notStereogenic`.  A network must therefore never override the final per-bond assignment path.
After the ordinary branch, the only admissible final assignment is the direct P-92/P-93
descriptor-dependent senior-side adapter.  The retained network parameter makes this safety
boundary explicit at the former routing site and avoids conflating internal ranking evidence with
a public stereodescriptor. -/
def coupledOrDescriptorDependentDoubleBondAssignment?
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat)
    (ordinaryAssignments : List StereoAssignment)
    (_networks : List CoupledGeometryNetwork)
    (assignment : Nat × Nat × DoubleBondStereo) : Option StereoAssignment :=
  let left := assignment.1
  let right := assignment.2.1
  if ordinaryAssignments.any fun reported =>
      reported.unit == StereoUnit.doubleBond left right then none else
  descriptorDependentDoubleBondAssignment? result mol state fuel assignment

/-- Public per-bond emission is invariant under every change to the compiled coupled-network
collection.  This theorem is the executable safety boundary between internal Rule-3 observations
and final stereodescriptors. -/
theorem coupledOrDescriptorDependentDoubleBondAssignment?_network_irrelevant
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat)
    (ordinaryAssignments : List StereoAssignment)
    (leftNetworks rightNetworks : List CoupledGeometryNetwork)
    (assignment : Nat × Nat × DoubleBondStereo) :
    coupledOrDescriptorDependentDoubleBondAssignment?
        result mol state fuel ordinaryAssignments leftNetworks assignment =
      coupledOrDescriptorDependentDoubleBondAssignment?
        result mol state fuel ordinaryAssignments rightNetworks assignment := by
  rfl

/-- Descriptor state used by geometry-dependent normalized branches.

When fixed-point discovery is empty, input-annotated centers contribute tentative auxiliary
facts; otherwise the stabilized state is used unchanged.  Naming the state prevents the public
branch theorem from relying on a duplicated local `let` expression. -/
def normalizedGeometryDescriptorState
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel : Nat) (descriptorState : RawDescriptorState) : RawDescriptorState :=
  if descriptorState.isEmpty then
    (rawAnnotatedCenters result).foldl (fun state center =>
      match tentativeAuxiliaryFactAt? mol fuel center with
      | some fact => state.insertIfAbsent fact
      | none => state) descriptorState
  else descriptorState

/-- All coupled marker networks considered by the normalized post-ordinary router. -/
def normalizedCoupledGeometryNetworks
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat) : List CoupledGeometryNetwork :=
  let markerCandidates := result.stereobonds.doubleBondAssignments.filter fun assignment =>
    !(result.stereobonds.directionalMarkersAtSide assignment.1 assignment.2.1).isEmpty &&
      !(result.stereobonds.directionalMarkersAtSide assignment.2.1 assignment.1).isEmpty
  let hasInternalMarkerJunction := markerCandidates.any fun assignment =>
    (result.stereobonds.directionalMarkersAtSide assignment.1 assignment.2.1).length != 1 ||
      (result.stereobonds.directionalMarkersAtSide assignment.2.1 assignment.1).length != 1
  if markerCandidates.length < 2 || !hasInternalMarkerJunction then [] else
    let candidates := markerCandidates.filter fun assignment =>
      doubleBondStereogenicity mol fuel assignment.1 assignment.2.1 ==
        DoubleBondStereogenicity.notStereogenic
    let carrierNetworks := state.filterMap fun fact =>
      coupledGeometryNetworkAt? result mol state fuel fact.atom
    let markerNetworks :=
      (markerCoupledGeometryNetwork? result mol candidates).toList
    carrierNetworks ++ markerNetworks.filter fun network =>
      !(carrierNetworks.any fun existing => existing.units == network.units)

/-- The five disjoint list segments assembled by the normalized public analyzer.

The first two fields have independent P-92/P-93 judgments.  The final three fields are named here
so that the conformance layer can expose their remaining family-specific proof obligations exactly,
rather than hiding all five segments behind one undifferentiated legacy-output disjunct. -/
structure NormalizedStereoAnalysisBranches where
  tetrahedral : List StereoAssignment
  ordinaryDoubleBond : List StereoAssignment
  coupledDoubleBond : List StereoAssignment
  oddCumuleneDoubleBond : List StereoAssignment
  extendedAxial : List StereoAssignment

/-- Compute the five output segments of `analyzeNormalized` without applying its two molecule-wide
admission guards.  The computation and ordering are exactly the former local `let` bindings of the
public analyzer. -/
def normalizedStereoAnalysisBranches
    (result : ChemistryNormalizationResult) : NormalizedStereoAnalysisBranches :=
  let expanded := result.parsed.withExplicitHydrogens
  let fuel := analysisFuel expanded
  let descriptorState := discoverRawDescriptors result expanded fuel
  let geometryDescriptorState :=
    normalizedGeometryDescriptorState result expanded fuel descriptorState
  let coupledNetworks :=
    normalizedCoupledGeometryNetworks result expanded geometryDescriptorState fuel
  let centers :=
    tetrahedralAssignments result expanded descriptorState fuel
  let bonds :=
    ordinaryDoubleBondAssignments result expanded descriptorState fuel
  let coupledBonds :=
    result.stereobonds.doubleBondAssignments.filterMap
      (coupledOrDescriptorDependentDoubleBondAssignment?
        result expanded geometryDescriptorState fuel bonds coupledNetworks)
  let extendedBonds :=
    oddCumuleneDoubleBondAssignments result expanded geometryDescriptorState fuel
  let axes := expanded.extendedTetrahedralParityCarriers.map
    (extendedTetrahedralAxialAssignment result expanded geometryDescriptorState fuel)
  { tetrahedral := centers
    ordinaryDoubleBond := bonds
    coupledDoubleBond := coupledBonds
    oddCumuleneDoubleBond := extendedBonds
    extendedAxial := axes }

@[simp] theorem normalizedStereoAnalysisBranches_tetrahedral
    (result : ChemistryNormalizationResult) :
    (normalizedStereoAnalysisBranches result).tetrahedral =
      tetrahedralAssignments result result.parsed.withExplicitHydrogens
        (discoverRawDescriptors result result.parsed.withExplicitHydrogens
          (analysisFuel result.parsed.withExplicitHydrogens))
        (analysisFuel result.parsed.withExplicitHydrogens) := by
  rfl

@[simp] theorem normalizedStereoAnalysisBranches_ordinaryDoubleBond
    (result : ChemistryNormalizationResult) :
    (normalizedStereoAnalysisBranches result).ordinaryDoubleBond =
      ordinaryDoubleBondAssignments result result.parsed.withExplicitHydrogens
        (discoverRawDescriptors result result.parsed.withExplicitHydrogens
          (analysisFuel result.parsed.withExplicitHydrogens))
        (analysisFuel result.parsed.withExplicitHydrogens) := by
  rfl

theorem normalizedStereoAnalysisBranches_coupledDoubleBond
    (result : ChemistryNormalizationResult) :
    (normalizedStereoAnalysisBranches result).coupledDoubleBond =
      let expanded := result.parsed.withExplicitHydrogens
      let fuel := analysisFuel expanded
      let descriptorState := discoverRawDescriptors result expanded fuel
      let geometryDescriptorState :=
        normalizedGeometryDescriptorState result expanded fuel descriptorState
      let ordinaryAssignments :=
        ordinaryDoubleBondAssignments result expanded descriptorState fuel
      let networks :=
        normalizedCoupledGeometryNetworks result expanded geometryDescriptorState fuel
      result.stereobonds.doubleBondAssignments.filterMap
        (coupledOrDescriptorDependentDoubleBondAssignment?
          result expanded geometryDescriptorState fuel ordinaryAssignments networks) := by
  rfl

@[simp] theorem normalizedStereoAnalysisBranches_oddCumuleneDoubleBond
    (result : ChemistryNormalizationResult) :
    (normalizedStereoAnalysisBranches result).oddCumuleneDoubleBond =
      let expanded := result.parsed.withExplicitHydrogens
      let fuel := analysisFuel expanded
      let descriptorState := discoverRawDescriptors result expanded fuel
      let geometryDescriptorState :=
        normalizedGeometryDescriptorState result expanded fuel descriptorState
      oddCumuleneDoubleBondAssignments result expanded geometryDescriptorState fuel := by
  rfl

theorem normalizedStereoAnalysisBranches_extendedAxial
    (result : ChemistryNormalizationResult) :
    (normalizedStereoAnalysisBranches result).extendedAxial =
      let expanded := result.parsed.withExplicitHydrogens
      let fuel := analysisFuel expanded
      let descriptorState := discoverRawDescriptors result expanded fuel
      let geometryDescriptorState :=
        normalizedGeometryDescriptorState result expanded fuel descriptorState
      expanded.extendedTetrahedralParityCarriers.map
        (extendedTetrahedralAxialAssignment
          result expanded geometryDescriptorState fuel) := by
  rfl

/-- Analyse every stereogenic unit of a normalized molecule.

Tetrahedral centres are read from parsed parity annotations; double bonds are read from the parsed
double-bond list.  Both rank branches with the same hierarchical digraph over the same hydrogen-materialised
molecule, so the two halves of the analysis cannot disagree about priority. -/
def analyzeNormalized (result : ChemistryNormalizationResult) : List StereoAssignment :=
  if !result.parsed.rule2MassesKnown? then [] else
  if !result.expandedStereochemicalAdmissible? then [] else
  let branches := normalizedStereoAnalysisBranches result
  branches.tetrahedral ++ branches.ordinaryDoubleBond ++ branches.coupledDoubleBond ++
    branches.oddCumuleneDoubleBond ++ branches.extendedAxial

/-- Every public assignment produced from a normalized molecule was computed over an exact,
structurally admitted hydrogen-expanded ranking graph.  This is a fail-closed safety theorem; the
separate preservation target is to prove that expansion never rejects a stereochemically
admissible input. -/
theorem analyzeNormalized_member_expandedStereochemicalAdmissible
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeNormalized result) :
    result.ExpandedStereochemicalAdmissible := by
  apply (result.expandedStereochemicalAdmissible?_eq_true_iff).mp
  by_contra guardNotTrue
  have guardFalse : result.expandedStereochemicalAdmissible? = false :=
    Bool.eq_false_of_not_eq_true guardNotTrue
  simp [analyzeNormalized, guardFalse] at member

/-- The one descriptor-independent early refusal that can bypass molecule-wide discovery.

The guard proves that the normalized molecule exposes exactly one annotated tetrahedral candidate
and no ordinary, coupled, or extended double-bond candidate.  A wrong ligand count is decided
before branch ranking in `tetrahedralOutcome`.  A `notStereogenic` result is also invariant when
that sole center is acyclic: there is no Rule-3 geometry, other descriptor source, or Rule-6
topology that could break its constitutional tie.  Thus no reported unit can depend on the
descriptor fixed point in either accepted case. -/
def singleInvariantEarlyAssignment? (result : ChemistryNormalizationResult) :
    Option StereoAssignment :=
  if !result.stereobonds.doubleBondAssignments.isEmpty ||
      !result.parsed.extendedDoubleBondChains.isEmpty then none else
  match rawAnnotatedCenters result with
  | [center] =>
      let expanded := result.parsed.withExplicitHydrogens
      if !result.expandedStereochemicalAdmissible? then none else
      match expanded.tetrahedralOutcome (analysisFuel expanded) center with
      | StereoOutcome.refused (StereoRefusal.wrongLigandCount found) =>
          some { unit := StereoUnit.tetrahedral center
                 outcome := StereoOutcome.refused (StereoRefusal.wrongLigandCount found) }
      | StereoOutcome.refused StereoRefusal.notStereogenic =>
          let fuel := analysisFuel expanded
          if expanded.atomLiesInCycle fuel center then none else
            some { unit := StereoUnit.tetrahedral center
                   outcome := StereoOutcome.refused StereoRefusal.notStereogenic }
      | _ => none
  | _ => none

/-- Analyse every stereogenic unit of an OpenSMILES string.

This is the whole tool in one call: a string in, a list of units with descriptors or typed refusals
out, or a parse error. -/
def analyzeSmiles (input : String) : Except ParserError (List StereoAssignment) :=
  match parseOpenSMILES input with
  | Except.error message => Except.error message
  | Except.ok mol =>
      if !mol.rule2MassesKnown? then
        Except.error "unsupported element or isotope: no frozen IUPAC Rule-2 mass datum"
      else
        let result := normalizeRawMolecule mol
        match result.certify? with
        | none =>
            Except.error "normalized molecule failed structural or valence admission"
        | some certified =>
            if !certified.result.expandedStereochemicalAdmissible? then
              Except.error "hydrogen-expanded molecule failed structural stereochemical admission"
            else
              match singleInvariantEarlyAssignment? certified.result with
              | some assignment => Except.ok [assignment]
              | none => Except.ok (analyzeNormalized certified.result)

/-- A plain-text report, one line per stereogenic unit. -/
def analyzeSmilesReport (input : String) : String :=
  match analyzeSmiles input with
  | Except.error message => "parse error: " ++ message
  | Except.ok [] => "no stereogenic units found"
  | Except.ok assignments =>
      String.intercalate "\n" (assignments.map StereoAssignment.label)

/-- Read an `R/S` result from one already hydrogen-expanded molecule. -/
def expandedTetrahedralDescriptorAt? (expanded : RawMolecule) (idx : ℕ) : Option RS :=
  if !expanded.rule2MassesKnown? then none else
    match expanded.tetrahedralOutcome (analysisFuel expanded) idx with
    | StereoOutcome.tetrahedral value => some value
    | _ => none

/-- Assign `R/S` at one tetrahedral centre of an already parsed OpenSMILES molecule. -/
def parsedTetrahedralDescriptorAt? (mol : RawMolecule) (idx : ℕ) : Option RS :=
  expandedTetrahedralDescriptorAt?
    mol.normalizeUnspecifiedBonds.withExplicitHydrogens idx

/-- Assign `R/S` at one parsed tetrahedral centre of an OpenSMILES string. -/
def smilesTetrahedralDescriptorAt? (input : String) (idx : ℕ) : Option RS :=
  match parseOpenSMILES input with
  | Except.error _ => none
  | Except.ok mol => parsedTetrahedralDescriptorAt? mol idx

/-- Every stereogenic unit of an OpenSMILES string that received a descriptor. -/
def smilesAssignedDescriptors (input : String) : List StereoAssignment :=
  match analyzeSmiles input with
  | Except.error _ => []
  | Except.ok assignments => assignments.filter fun a => a.outcome.assigned

end OneCenter
end TetraStereo
