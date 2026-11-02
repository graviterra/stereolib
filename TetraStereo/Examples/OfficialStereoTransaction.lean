import TetraStereo.Engine.OfficialStereoTransaction
import TetraStereo.OneCenter.CIPValidationFixtures
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace OfficialStereoTransaction

open OneCenter

noncomputable section

















/-- Six-carbon raw molecule used only to fix the normalized atom universe. -/
def starRawMolecule : RawMolecule where
  atoms :=
    List.replicate 6 (AtomSpec.aliphatic Element.C)
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.single }
    , { source := 0, target := 2, kind := ParsedBondKind.single }
    , { source := 0, target := 3, kind := ParsedBondKind.single }
    , { source := 0, target := 4, kind := ParsedBondKind.single }
    ]

/-- Normalized host molecule packet used by the public official-stereo request. -/
def starNormalized : ChemistryNormalizationResult :=
  normalizeRawMolecule starRawMolecule

/-- Variant raw molecule whose first ligand is oxygen, used to test graph-key priority. -/
def heteroRawMolecule : RawMolecule where
  atoms :=
    [ AtomSpec.aliphatic Element.C
    , AtomSpec.aliphatic Element.O
    , AtomSpec.aliphatic Element.C
    , AtomSpec.aliphatic Element.C
    , AtomSpec.aliphatic Element.C
    , AtomSpec.aliphatic Element.C
    ]
  bonds := starRawMolecule.bonds

/-- Normalized host molecule packet for the graph-key official-stereo request. -/
def heteroNormalized : ChemistryNormalizationResult :=
  normalizeRawMolecule heteroRawMolecule

/-- Variant raw molecule whose first ligand is double-bonded to the center. -/
def multipleBondRawMolecule : RawMolecule where
  atoms :=
    List.replicate 6 (AtomSpec.aliphatic Element.C)
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.double }
    , { source := 0, target := 2, kind := ParsedBondKind.single }
    , { source := 0, target := 3, kind := ParsedBondKind.single }
    , { source := 0, target := 4, kind := ParsedBondKind.single }
    ]

/-- Normalized host molecule packet for the multiple-bond duplicate-node request. -/
def multipleBondNormalized : ChemistryNormalizationResult :=
  normalizeRawMolecule multipleBondRawMolecule

/-- Proof-facing atom type for the star example. -/
abbrev Atom := Fin 6

/-- Center plus four ligand atoms; atom `5` is available for non-center annotation support. -/
def starBond (u v : Atom) : BondOrder :=
  if (u = 0 ∧ (v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4)) ∨
      (v = 0 ∧ (u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4)) then
    1
  else
    0

/-- Proof-facing molecule matching the star graph. -/
def starMol : MoleculeGraph Atom where
  atomZ := fun _ => 6
  atomMass := fun _ => 0
  bond := starBond
  bond_symm := by
    intro u v
    fin_cases u <;> fin_cases v <;> simp [starBond]
  bond_self := by
    intro u
    fin_cases u <;> simp [starBond]

/-- Proof-facing molecule where ligand `1` is oxygen and ligand `2` is carbon. -/
def heteroMol : MoleculeGraph Atom where
  atomZ := fun atom => if atom = 1 then 8 else 6
  atomMass := fun _ => 0
  bond := starBond
  bond_symm := by
    intro u v
    exact starMol.bond_symm u v
  bond_self := by
    intro u
    exact starMol.bond_self u

/-- Bond matrix with a double bond from the center to ligand `1`. -/
def multipleBondBond (u v : Atom) : BondOrder :=
  if (u = 0 ∧ v = 1) ∨ (v = 0 ∧ u = 1) then
    2
  else
    starBond u v

/-- Proof-facing molecule where a generated multiple-bond duplicate distinguishes branch `0`. -/
def multipleBondMol : MoleculeGraph Atom where
  atomZ := fun _ => 6
  atomMass := fun _ => 0
  bond := multipleBondBond
  bond_symm := by
    intro u v
    fin_cases u <;> fin_cases v <;> simp [multipleBondBond, starBond]
  bond_self := by
    intro u
    fin_cases u <;> simp [multipleBondBond, starBond]

/-- The single stereocenter's ligand enumeration. -/
def starLigandAtom : Fin 4 → Atom
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4

/-- One-center wrapper for the star molecule. -/
def starOne : OneCenterMolecule Atom where
  mol := starMol
  center := 0
  ligandAtom := starLigandAtom
  ligandAtom_adj := by
    intro i
    fin_cases i <;> simp [MoleculeGraph.Adj, starMol, starBond, starLigandAtom]
  ligandAtom_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [starLigandAtom] at hij ⊢
  ligandAtom_surjective := by
    intro v hv
    fin_cases v <;> simp [MoleculeGraph.Adj, starMol, starBond, starLigandAtom] at hv ⊢
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

/-- One-center wrapper for the heteroatom graph-key example. -/
def heteroOne : OneCenterMolecule Atom where
  mol := heteroMol
  center := 0
  ligandAtom := starLigandAtom
  ligandAtom_adj := by
    intro i
    fin_cases i <;> simp [MoleculeGraph.Adj, heteroMol, starBond, starLigandAtom]
  ligandAtom_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [starLigandAtom] at hij ⊢
  ligandAtom_surjective := by
    intro v hv
    fin_cases v <;> simp [MoleculeGraph.Adj, heteroMol, starBond, starLigandAtom] at hv ⊢
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

/-- One-center wrapper for the multiple-bond duplicate-node example. -/
def multipleBondOne : OneCenterMolecule Atom where
  mol := multipleBondMol
  center := 0
  ligandAtom := starLigandAtom
  ligandAtom_adj := by
    intro i
    fin_cases i <;> simp [MoleculeGraph.Adj, multipleBondMol, multipleBondBond, starBond,
      starLigandAtom]
  ligandAtom_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [starLigandAtom] at hij ⊢
  ligandAtom_surjective := by
    intro v hv
    fin_cases v <;> simp [MoleculeGraph.Adj, multipleBondMol, multipleBondBond, starBond,
      starLigandAtom] at hv ⊢
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

/-- Multi-center wrapper with one distinguished tetrahedral center. -/
def starMulti : MultiCenterMolecule Atom :=
  starOne.toMultiCenterMolecule

/-- Multi-center wrapper for the heteroatom graph-key example. -/
def heteroMulti : MultiCenterMolecule Atom :=
  heteroOne.toMultiCenterMolecule

/-- Multi-center wrapper for the multiple-bond duplicate-node example. -/
def multipleBondMulti : MultiCenterMolecule Atom :=
  multipleBondOne.toMultiCenterMolecule

/-- The unique center in the star example. -/
def starCenter : starMulti.Center :=
  ⟨0, by simp [starMulti, starOne, OneCenterMolecule.toMultiCenterMolecule]⟩

/-- The unique center in the heteroatom graph-key example. -/
def heteroCenter : heteroMulti.Center :=
  ⟨0, by simp [heteroMulti, heteroOne, OneCenterMolecule.toMultiCenterMolecule]⟩

/-- The unique center in the multiple-bond duplicate-node example. -/
def multipleBondCenter : multipleBondMulti.Center :=
  ⟨0, by simp [multipleBondMulti, multipleBondOne, OneCenterMolecule.toMultiCenterMolecule]⟩

/-! ### Concrete rule-major keys for the example graphs

The public transaction consumes the bounded rule-major certificate
`cipOfficialCompareWithFuel`, whose child enumeration is noncomputable (`Finset.toList`).  The
lemmas below therefore establish the actual compiled keys structurally, instead of attempting to
evaluate the enumeration.  At the supplied fuels (`0`, `1`, `2`, and `7`) every single-bonded
ligand root is terminal, while the multiple-bonded ligand contributes one generated duplicate
leaf. -/

/-- Ligand `1` of the star graph sees only the stereocenter. -/
private theorem star_neighborFinset_one :
    starMol.neighborFinset (1 : Atom) = {0} := by
  ext atom
  fin_cases atom <;> simp [MoleculeGraph.neighborFinset, MoleculeGraph.Adj, starMol, starBond]

/-- Ligand `2` of the star graph sees only the stereocenter. -/
private theorem star_neighborFinset_two :
    starMol.neighborFinset (2 : Atom) = {0} := by
  ext atom
  fin_cases atom <;> simp [MoleculeGraph.neighborFinset, MoleculeGraph.Adj, starMol, starBond]

/-- Ligand `1` of the heteroatom graph sees only the stereocenter. -/
private theorem hetero_neighborFinset_one :
    heteroMol.neighborFinset (1 : Atom) = {0} := by
  ext atom
  fin_cases atom <;> simp [MoleculeGraph.neighborFinset, MoleculeGraph.Adj, heteroMol, starBond]

/-- Ligand `2` of the heteroatom graph sees only the stereocenter. -/
private theorem hetero_neighborFinset_two :
    heteroMol.neighborFinset (2 : Atom) = {0} := by
  ext atom
  fin_cases atom <;> simp [MoleculeGraph.neighborFinset, MoleculeGraph.Adj, heteroMol, starBond]

/-- The star root at ligand `1` is terminal: the parent edge is the unique neighbor copy. -/
private theorem star_children_eq_nil_one :
    starMol.officialCIPChildren
        (OfficialCIPNode.rootFromEdge (V := Atom) 0 1) = [] := by
  unfold MoleculeGraph.officialCIPChildren MoleculeGraph.officialChildCopies
    MoleculeGraph.officialNeighborCopies
  simp [OfficialCIPNode.rootFromEdge]
  rw [star_neighborFinset_one]
  simp [Finset.toList_singleton, starMol, starBond,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNode.parent?]

/-- The star root at ligand `2` is terminal. -/
private theorem star_children_eq_nil_two :
    starMol.officialCIPChildren
        (OfficialCIPNode.rootFromEdge (V := Atom) 0 2) = [] := by
  unfold MoleculeGraph.officialCIPChildren MoleculeGraph.officialChildCopies
    MoleculeGraph.officialNeighborCopies
  simp [OfficialCIPNode.rootFromEdge]
  rw [star_neighborFinset_two]
  simp [Finset.toList_singleton, starMol, starBond,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNode.parent?]

/-- The heteroatom root at ligand `1` is terminal. -/
private theorem hetero_children_eq_nil_one :
    heteroMol.officialCIPChildren
        (OfficialCIPNode.rootFromEdge (V := Atom) 0 1) = [] := by
  unfold MoleculeGraph.officialCIPChildren MoleculeGraph.officialChildCopies
    MoleculeGraph.officialNeighborCopies
  simp [OfficialCIPNode.rootFromEdge]
  rw [hetero_neighborFinset_one]
  simp [Finset.toList_singleton, heteroMol, starBond,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNode.parent?]

/-- The heteroatom root at ligand `2` is terminal. -/
private theorem hetero_children_eq_nil_two :
    heteroMol.officialCIPChildren
        (OfficialCIPNode.rootFromEdge (V := Atom) 0 2) = [] := by
  unfold MoleculeGraph.officialCIPChildren MoleculeGraph.officialChildCopies
    MoleculeGraph.officialNeighborCopies
  simp [OfficialCIPNode.rootFromEdge]
  rw [hetero_neighborFinset_two]
  simp [Finset.toList_singleton, heteroMol, starBond,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNode.parent?]

/-- The rule-major root key of a terminal star ligand. -/
private def starRootKey (ligand : Atom) : OfficialRuleMajorKey Atom :=
  starMol.officialRuleMajorRootKey
    (OfficialCIPNode.rootFromEdge (V := Atom) 0 ligand) true

/-- The rule-major root key of a terminal heteroatom ligand. -/
private def heteroRootKey (ligand : Atom) : OfficialRuleMajorKey Atom :=
  heteroMol.officialRuleMajorRootKey
    (OfficialCIPNode.rootFromEdge (V := Atom) 0 ligand) true

/-- At every fuel, the terminal star ligand `1` root compiles to its complete root key. -/
private theorem star_build_eq_one (fuel : ℕ) :
    starMol.buildOfficialRuleMajorKey starMol.officialCIPChildren fuel
        (OfficialCIPNode.rootFromEdge (V := Atom) 0 1) =
      some (starRootKey 1) := by
  cases fuel with
  | zero =>
      simp [MoleculeGraph.buildOfficialRuleMajorKey, star_children_eq_nil_one, starRootKey]
  | succ fuel =>
      simp [MoleculeGraph.buildOfficialRuleMajorKey, star_children_eq_nil_one, starRootKey]

/-- At every fuel, the terminal star ligand `2` root compiles to its complete root key. -/
private theorem star_build_eq_two (fuel : ℕ) :
    starMol.buildOfficialRuleMajorKey starMol.officialCIPChildren fuel
        (OfficialCIPNode.rootFromEdge (V := Atom) 0 2) =
      some (starRootKey 2) := by
  cases fuel with
  | zero =>
      simp [MoleculeGraph.buildOfficialRuleMajorKey, star_children_eq_nil_two, starRootKey]
  | succ fuel =>
      simp [MoleculeGraph.buildOfficialRuleMajorKey, star_children_eq_nil_two, starRootKey]

/-- At every fuel, the terminal heteroatom ligand `1` root compiles to its complete root key. -/
private theorem hetero_build_eq_one (fuel : ℕ) :
    heteroMol.buildOfficialRuleMajorKey heteroMol.officialCIPChildren fuel
        (OfficialCIPNode.rootFromEdge (V := Atom) 0 1) =
      some (heteroRootKey 1) := by
  cases fuel with
  | zero =>
      simp [MoleculeGraph.buildOfficialRuleMajorKey, hetero_children_eq_nil_one, heteroRootKey]
  | succ fuel =>
      simp [MoleculeGraph.buildOfficialRuleMajorKey, hetero_children_eq_nil_one, heteroRootKey]

/-- At every fuel, the terminal heteroatom ligand `2` root compiles to its complete root key. -/
private theorem hetero_build_eq_two (fuel : ℕ) :
    heteroMol.buildOfficialRuleMajorKey heteroMol.officialCIPChildren fuel
        (OfficialCIPNode.rootFromEdge (V := Atom) 0 2) =
      some (heteroRootKey 2) := by
  cases fuel with
  | zero =>
      simp [MoleculeGraph.buildOfficialRuleMajorKey, hetero_children_eq_nil_two, heteroRootKey]
  | succ fuel =>
      simp [MoleculeGraph.buildOfficialRuleMajorKey, hetero_children_eq_nil_two, heteroRootKey]

/-- Same-atom, same-provenance star roots tie constitutionally. -/
private theorem starRootKey_compare_eq :
    OfficialRuleMajorKey.compare? (starRootKey 1) (starRootKey 2) =
      some Ordering.eq := by
  decide

/-- The tied star pair has a tied constitutional rule-major trace. -/
private theorem starRootKey_trace_outcome_eq :
    cipTraceOutcome (OfficialRuleMajorKey.compareTrace (starRootKey 1) (starRootKey 2)) =
      Ordering.eq := by
  decide

/-- Oxygen at ligand `1` outranks carbon at ligand `2` by Rule 1a. -/
private theorem heteroRootKey_compare_gt :
    OfficialRuleMajorKey.compare? (heteroRootKey 1) (heteroRootKey 2) =
      some Ordering.gt := by
  decide

/-- The strict Rule-1a difference is the first decisive constitutional rule. -/
private theorem heteroRootKey_trace_outcome_gt :
    cipTraceOutcome (OfficialRuleMajorKey.compareTrace (heteroRootKey 1) (heteroRootKey 2)) =
      Ordering.gt := by
  decide

/-- Once both actual roots have compiled to keys that pass the completed-key gate, the public
transaction certificate is the context certificate built from the rule-major trace of those very
keys.  This is the transaction-level analogue of the localized `compareAt_eq_some_of_compare?`
lemma; it never unfolds the noncomputable child enumeration. -/
private theorem certificate_eq_some_of_keys {request : Engine.OfficialStereoRequest}
    (leftKey rightKey : OfficialRuleMajorKey (Fin request.normalized.parsed.atomCount))
    {outcome : Ordering}
    (leftComputed :
      request.oneCenter.mol.buildOfficialRuleMajorKey
        request.oneCenter.mol.officialCIPChildren request.graphFuel
        (OfficialCIPNode.rootFromEdge request.oneCenter.center
          (request.oneCenter.ligandAtom request.left)) = some leftKey)
    (rightComputed :
      request.oneCenter.mol.buildOfficialRuleMajorKey
        request.oneCenter.mol.officialCIPChildren request.graphFuel
        (OfficialCIPNode.rootFromEdge request.oneCenter.center
          (request.oneCenter.ligandAtom request.right)) = some rightKey)
    (compared : OfficialRuleMajorKey.compare? leftKey rightKey = some outcome) :
    request.certificate =
      some (CIPRuleEngine.compareDigraphThenOfficialCertificate
        (OfficialRuleMajorKey.compareTrace leftKey rightKey)
        (request.branchContext request.left) (request.branchContext request.right)) := by
  simp only [Engine.OfficialStereoRequest.certificate,
    OneCenterMolecule.cipOfficialCompareWithFuel,
    Engine.OfficialStereoRequest.compareContext,
    MoleculeGraph.compareRuleMajorRootsWithFuel,
    MoleculeGraph.ruleMajorConstitutionalTraceWithFuel,
    leftComputed, rightComputed, compared, Option.map_some]

/-- External detector annotations: ligand `1` carries helical `M`, ligand `2` carries helical `P`. -/
def helicalBranchAnnotations : IndexedNoncenterStereoAnnotations where
  helices :=
    [ { helixPath := [1, 0, 5]
        frontReference := 1
        backReference := 5
        descriptor := HelicalDescriptor.M }
    , { helixPath := [2, 0, 5]
        frontReference := 2
        backReference := 5
        descriptor := HelicalDescriptor.P }
    ]


def helicalBranchTheoremPlan : Engine.PublicOfficialStereoTheoremPlan where
  imports :=
    [ "TetraStereo.Engine.OfficialStereoTransaction"
    , "TetraStereo.Examples.OfficialStereoTransaction"
    ]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "helical_branch_detector_official_comparison"
  requestExpr := "TetraStereo.Examples.OfficialStereoTransaction.helicalBranchRequest"
  proofTerm :=
    "  exact TetraStereo.Examples.OfficialStereoTransaction.helicalBranchRequest_outcome_eq_gt"

/-- Public engine request for the detector-backed helical branch comparison. -/
def helicalBranchRequest : Engine.OfficialStereoRequest where
  normalized := starNormalized
  annotations := helicalBranchAnnotations
  molecule := starMulti
  profile := DescriptorSourcePolicyProfile.exactDistance
  graphFuel := 0
  scheduleFuel := 0
  branchFuel := 0
  center := starCenter
  localMolecule := starOne
  left := 0
  right := 1
  theoremPlan := helicalBranchTheoremPlan

/-- The detector registry contains four automatic conformational candidates plus two external
helical units. -/
theorem helicalBranchRequest_detection_length :
    helicalBranchRequest.detection.units.length = 6 :=
  rfl

/-- The public official-stereo transaction is detector-ready. -/
theorem helicalBranchRequest_detectorReady :
    helicalBranchRequest.detectorReady = true :=
  rfl

/-- The two compared helical branches have branch-relevant context-producing sources. -/
theorem helicalBranchRequest_comparedBranchesComplete :
    helicalBranchRequest.detectorBranchesComplete = true :=
  rfl

/-- The left detector-fed branch context carries helical `M`. -/
theorem helicalBranchRequest_left_rule5 :
    (starMulti.officialBranchContextFromDescriptorSourceDetectorWithin
      helicalBranchRequest.output helicalBranchRequest.policy 0 0 starCenter 0).rule5Descriptor? =
        some OfficialRule5Descriptor.descriptorM :=
  rfl

/-- The right detector-fed branch context carries helical `P`. -/
theorem helicalBranchRequest_right_rule5 :
    (starMulti.officialBranchContextFromDescriptorSourceDetectorWithin
      helicalBranchRequest.output helicalBranchRequest.policy 0 0 starCenter 1).rule5Descriptor? =
        some OfficialRule5Descriptor.descriptorP :=
  rfl

/-- The bounded constitutional certificate of the helical request, constructed from the two
terminal complete root keys at the request's supplied fuel. -/
private def helicalBranchRequestCertificateValue : CIPTraceCertificate :=
  CIPRuleEngine.compareDigraphThenOfficialCertificate
    (OfficialRuleMajorKey.compareTrace (starRootKey 1) (starRootKey 2))
    (helicalBranchRequest.branchContext helicalBranchRequest.left)
    (helicalBranchRequest.branchContext helicalBranchRequest.right)

private theorem helicalBranchRequest_certificate :
    helicalBranchRequest.certificate = some helicalBranchRequestCertificateValue := by
  apply certificate_eq_some_of_keys (request := helicalBranchRequest)
    (leftKey := starRootKey 1) (rightKey := starRootKey 2) (outcome := Ordering.eq)
  · simpa [helicalBranchRequest, Engine.OfficialStereoRequest.oneCenter, starOne,
      starLigandAtom, starRootKey] using star_build_eq_one 0
  · simpa [helicalBranchRequest, Engine.OfficialStereoRequest.oneCenter, starOne,
      starLigandAtom, starRootKey] using star_build_eq_two 0
  · exact starRootKey_compare_eq

/-- The detector-fed contexts outrank `M` over `P` at Rule 5, after Rules 3 and 4a tie. -/
private theorem helicalBranchRequest_context_outcome :
    cipTraceOutcome (CIPRuleEngine.compareOfficialContextTrace
      (helicalBranchRequest.branchContext helicalBranchRequest.left)
      (helicalBranchRequest.branchContext helicalBranchRequest.right)) = Ordering.gt := by
  decide

private theorem helicalBranchRequestCertificateValue_outcome :
    helicalBranchRequestCertificateValue.outcome = Ordering.gt := by
  unfold helicalBranchRequestCertificateValue
  rw [CIPRuleEngine.compareDigraphThenOfficialCertificate_outcome,
    CIPRuleEngine.compareDigraphThenOfficialTrace_outcome_of_digraph_eq starRootKey_trace_outcome_eq]
  exact helicalBranchRequest_context_outcome

/-- Detector-backed official Rule-5 comparison: helical `M` outranks helical `P`. -/
theorem helicalBranchRequest_outcome_eq_gt :
    helicalBranchRequest.outcome = some Ordering.gt := by
  simp [Engine.OfficialStereoRequest.outcome, helicalBranchRequest_certificate,
    helicalBranchRequestCertificateValue_outcome]

/-- The constitutional trace of this request contains no decisive graph decision: all three
constitutional decisions tie, so resolution came from the detector branch context. -/
private theorem helicalBranchRequest_graphResolved_eq_false :
    helicalBranchRequest.graphResolved = false := by
  unfold Engine.OfficialStereoRequest.graphResolved
  rw [helicalBranchRequest_certificate]
  decide

/-- The helical transaction is resolved by detector-fed branch context, not graph key. -/
theorem helicalBranchRequest_resolutionSource :
    helicalBranchRequest.resolutionSource =
      Engine.OfficialCIPResolutionSource.detectorBranchContext := by
  have hdec : helicalBranchRequest.outcomeDecisive = true := by
    unfold Engine.OfficialStereoRequest.outcomeDecisive
    rw [helicalBranchRequest_outcome_eq_gt]
    simp [Engine.OfficialStereoRequest.orderingDecisive]
  exact Engine.OfficialStereoRequest.resolutionSource_eq_detectorBranchContext_of_not_graphResolved
    helicalBranchRequest helicalBranchRequest_graphResolved_eq_false hdec

/-- Total public engine decision for the helical branch request. -/
def helicalBranchDecision : Engine.OfficialStereoDecision helicalBranchRequest :=
  Engine.decideOfficialStereo helicalBranchRequest

/-- The public decision exposes the expected comparison result. -/
theorem helicalBranchDecision_outcome_eq_some_gt :
    helicalBranchDecision.outcome? = some Ordering.gt := by
  unfold helicalBranchDecision
  have hne : helicalBranchRequestCertificateValue.outcome ≠ Ordering.eq := by
    rw [helicalBranchRequestCertificateValue_outcome]
    decide
  simpa [helicalBranchRequestCertificateValue_outcome] using
    Engine.OfficialStereoRequest.decideOfficialStereo_outcome_eq_some_of_ne_eq
      helicalBranchRequest helicalBranchRequest_certificate hne

/-- Named checked certificate for the helical branch transaction. -/
def helicalBranchCertificate :
    Engine.CertifiedOfficialStereoComparison helicalBranchRequest where
  expected := Ordering.gt
  proof := helicalBranchRequest_outcome_eq_gt
  artifact :=
    Engine.compileOfficialStereoTransaction helicalBranchRequest Ordering.gt
      helicalBranchRequest_outcome_eq_gt
  artifact_eq := rfl

/-- The compiled public official-stereo artifact is Lean-checked. -/
theorem helicalBranchCertificate_checked :
    helicalBranchCertificate.artifact.claim :=
  helicalBranchCertificate.artifact_checked

/-- Validation fixture backed by the public helical-branch official-stereo transaction. -/
def helicalBranchValidationFixture : CIPValidationFixture where
  id := "public-transaction-helical-M-before-P"
  name := "Public official-stereo transaction: helical M outranks P"
  suite := CIPValidationSuite.officialCIPRegression
  kind := CIPValidationFixtureKind.noncenterDetectorRegistration
  source := "TetraStereo public detector-backed transaction"
  expected := Ordering.gt
  artifact := helicalBranchCertificate.artifact

/-- External-ingestion entry whose checked fixture is the public official-stereo transaction. -/
def helicalBranchValidationImport : ExternalValidationCaseImport where
  spec :=
    { id := "public-transaction-helical-M-before-P"
      name := "Public official-stereo transaction: helical M outranks P"
      suite := CIPValidationSuite.officialCIPRegression
      kind := CIPValidationFixtureKind.noncenterDetectorRegistration
      source := "TetraStereo public detector-backed transaction"
      format := ChemistryImportFormat.rawMolecule
      expected := ExternalValidationExpected.comparison Ordering.gt
      notes :=
        [ "Indexed external helical annotations feed the public official-stereo transaction."
        , "The checked fixture artifact is the transaction certificate itself."
        ] }
  checkedFixture? := some helicalBranchValidationFixture

/-- Validation ingestion batch for the public official-stereo transaction. -/
def officialStereoTransactionValidationIngestion : ExternalValidationSuiteIngestion where
  name := "Public official-stereo transaction validation"
  cases := [helicalBranchValidationImport]

/-- The public official-stereo validation ingestion batch is checked. -/
theorem officialStereoTransactionValidationIngestion_checked :
    officialStereoTransactionValidationIngestion.checkedFixtureBatch.AllClaims :=
  officialStereoTransactionValidationIngestion.checked

/-! ### Graph-key public transaction -/


def graphKeyTheoremPlan : Engine.PublicOfficialStereoTheoremPlan where
  imports :=
    [ "TetraStereo.Engine.OfficialStereoTransaction"
    , "TetraStereo.Examples.OfficialStereoTransaction"
    ]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "graph_key_official_comparison"
  requestExpr := "TetraStereo.Examples.OfficialStereoTransaction.graphKeyRequest"
  proofTerm :=
    "  exact TetraStereo.Examples.OfficialStereoTransaction.graphKeyRequest_outcome_eq_gt"

/-- Public request where the official rule-major constitutional key resolves oxygen before
carbon. -/
def graphKeyRequest : Engine.OfficialStereoRequest where
  normalized := heteroNormalized
  annotations := {}
  molecule := heteroMulti
  profile := DescriptorSourcePolicyProfile.exactDistance
  graphFuel := 1
  center := heteroCenter
  localMolecule := heteroOne
  left := 0
  right := 1
  theoremPlan := graphKeyTheoremPlan

/-- Left root node for the one-layer graph-key comparison. -/
def graphKeyLeftRoot : OfficialCIPNode Atom :=
  OfficialCIPNode.rootFromEdge 0 1

/-- Right root node for the one-layer graph-key comparison. -/
def graphKeyRightRoot : OfficialCIPNode Atom :=
  OfficialCIPNode.rootFromEdge 0 2

/-- The concrete one-layer official hierarchical-digraph trace for oxygen-vs-carbon (retained
legacy layer-major fixture, not the transaction comparison). -/
def graphKeyTrace : List CIPRuleDecision :=
  heteroMol.compareOfficialHierarchicalDigraphTrace 1 [graphKeyLeftRoot] [graphKeyRightRoot]

/-- The concrete graph-key trace resolves oxygen before carbon. -/
theorem graphKeyTrace_outcome_eq_gt :
    cipTraceOutcome graphKeyTrace = Ordering.gt := by
  norm_num [cipTraceOutcome, graphKeyTrace, graphKeyLeftRoot, graphKeyRightRoot,
    MoleculeGraph.compareOfficialHierarchicalDigraphTrace,
    MoleculeGraph.compareOfficialLayerTrace, MoleculeGraph.sortOfficialLayer,
    MoleculeGraph.compareOfficialNodeListTrace, MoleculeGraph.compareOfficialNodeTrace,
    MoleculeGraph.compareOfficialNodeProvenanceTrace,
    MoleculeGraph.duplicateRootDistanceDecision, MoleculeGraph.officialNodeAtomLabel,
    MoleculeGraph.rawCIPAtomLabel, heteroMol, OfficialCIPNode.rootFromEdge,
    CIPRuleEngine.compareAtomLabelTrace, CIPRuleEngine.priorityNatDecision,
    CIPRuleEngine.comparePriorityNat]
  simp

/-- The graph-key request has no detector annotations. -/
theorem graphKeyRequest_detectorReady_eq_false :
    graphKeyRequest.detectorReady = false :=
  rfl

/-- The bounded constitutional certificate of the graph-key request. -/
private def graphKeyRequestCertificateValue : CIPTraceCertificate :=
  CIPRuleEngine.compareDigraphThenOfficialCertificate
    (OfficialRuleMajorKey.compareTrace (heteroRootKey 1) (heteroRootKey 2))
    (graphKeyRequest.branchContext graphKeyRequest.left)
    (graphKeyRequest.branchContext graphKeyRequest.right)

private theorem graphKeyRequest_certificate :
    graphKeyRequest.certificate = some graphKeyRequestCertificateValue := by
  apply certificate_eq_some_of_keys (request := graphKeyRequest)
    (leftKey := heteroRootKey 1) (rightKey := heteroRootKey 2) (outcome := Ordering.gt)
  · simpa [graphKeyRequest, Engine.OfficialStereoRequest.oneCenter, heteroOne,
      starLigandAtom, heteroRootKey] using hetero_build_eq_one 1
  · simpa [graphKeyRequest, Engine.OfficialStereoRequest.oneCenter, heteroOne,
      starLigandAtom, heteroRootKey] using hetero_build_eq_two 1
  · exact heteroRootKey_compare_gt

private theorem graphKeyRequestCertificateValue_outcome :
    graphKeyRequestCertificateValue.outcome = Ordering.gt := by
  unfold graphKeyRequestCertificateValue
  rw [CIPRuleEngine.compareDigraphThenOfficialCertificate_outcome,
    CIPRuleEngine.compareDigraphThenOfficialTrace_outcome_of_digraph_ne_eq
      (by rw [heteroRootKey_trace_outcome_gt]; decide)]
  exact heteroRootKey_trace_outcome_gt

/-- Public official-stereo graph-key comparison: oxygen outranks carbon. -/
theorem graphKeyRequest_outcome_eq_gt :
    graphKeyRequest.outcome = some Ordering.gt := by
  simp [Engine.OfficialStereoRequest.outcome, graphKeyRequest_certificate,
    graphKeyRequestCertificateValue_outcome]

/-- Hierarchical-digraph graph-key comparison: oxygen outranks carbon.  This is the outcome
projection of the same bounded certificate. -/
theorem graphKeyRequest_digraphOutcome_eq_gt :
    graphKeyRequest.digraphOutcome = some Ordering.gt := by
  rw [Engine.OfficialStereoRequest.digraphOutcome_eq_outcome,
    graphKeyRequest_outcome_eq_gt]

/-- The official rule-major graph trace resolves the comparison. -/
theorem graphKeyRequest_graphResolved :
    graphKeyRequest.graphResolved = true := by
  unfold Engine.OfficialStereoRequest.graphResolved
  rw [graphKeyRequest_certificate]
  decide

/-- Graph-key priority alone makes the public official-stereo transaction ready. -/
theorem graphKeyRequest_certificateReady :
    graphKeyRequest.certificateReady = true := by
  apply (Engine.OfficialStereoRequest.certificateReady_eq_true_iff graphKeyRequest).2
  refine ⟨graphKeyRequestCertificateValue, graphKeyRequest_certificate, ?_⟩
  rw [graphKeyRequestCertificateValue_outcome]
  decide

/-- The graph-key transaction is resolved by the official hierarchical digraph. -/
theorem graphKeyRequest_resolutionSource :
    graphKeyRequest.resolutionSource =
      Engine.OfficialCIPResolutionSource.hierarchicalDigraphGraphKey :=
  Engine.OfficialStereoRequest.resolutionSource_eq_hierarchicalDigraphGraphKey_of_graphResolved
    graphKeyRequest graphKeyRequest_graphResolved

/-- Public official-stereo transactions mark the legacy flattened key as absent. -/
theorem graphKeyRequest_flattenedKeyFree :
    graphKeyRequest.flattenedKeyFree = true :=
  rfl

/-- Total public engine decision for the graph-key request. -/
def graphKeyDecision : Engine.OfficialStereoDecision graphKeyRequest :=
  Engine.decideOfficialStereo graphKeyRequest

/-- The graph-key public decision exposes the expected comparison result. -/
theorem graphKeyDecision_outcome_eq_some_gt :
    graphKeyDecision.outcome? = some Ordering.gt := by
  unfold graphKeyDecision
  have hne : graphKeyRequestCertificateValue.outcome ≠ Ordering.eq := by
    rw [graphKeyRequestCertificateValue_outcome]
    decide
  simpa [graphKeyRequestCertificateValue_outcome] using
    Engine.OfficialStereoRequest.decideOfficialStereo_outcome_eq_some_of_ne_eq
      graphKeyRequest graphKeyRequest_certificate hne

/-- Named checked certificate for the graph-key official-stereo transaction. -/
def graphKeyCertificate :
    Engine.CertifiedOfficialStereoComparison graphKeyRequest where
  expected := Ordering.gt
  proof := graphKeyRequest_outcome_eq_gt
  artifact :=
    Engine.compileOfficialStereoTransaction graphKeyRequest Ordering.gt
      graphKeyRequest_outcome_eq_gt
  artifact_eq := rfl

/-- The compiled graph-key public official-stereo artifact is Lean-checked. -/
theorem graphKeyCertificate_checked :
    graphKeyCertificate.artifact.claim :=
  graphKeyCertificate.artifact_checked

/-! ### Default-fuel graph-key public transaction -/


def graphKeyDefaultFuelTheoremPlan : Engine.PublicOfficialStereoTheoremPlan where
  imports :=
    [ "TetraStereo.Engine.OfficialStereoTransaction"
    , "TetraStereo.Examples.OfficialStereoTransaction"
    ]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "graph_key_default_fuel_official_comparison"
  requestExpr := "TetraStereo.Examples.OfficialStereoTransaction.graphKeyDefaultFuelRequest"
  proofTerm :=
    "  exact TetraStereo.Examples.OfficialStereoTransaction.graphKeyDefaultFuelRequest_outcome_eq_gt"

/-- Public graph-key request using the default finite atom-cardinality fuel. -/
def graphKeyDefaultFuelRequest : Engine.OfficialStereoRequest where
  normalized := heteroNormalized
  annotations := {}
  molecule := heteroMulti
  profile := DescriptorSourcePolicyProfile.exactDistance
  graphFuel := 7
  center := heteroCenter
  localMolecule := heteroOne
  left := 0
  right := 1
  theoremPlan := graphKeyDefaultFuelTheoremPlan

/-- Default-fuel graph-key trace for oxygen-vs-carbon (retained legacy layer-major fixture). -/
def graphKeyDefaultFuelTrace : List CIPRuleDecision :=
  heteroMol.compareOfficialHierarchicalDigraphTrace 7 [graphKeyLeftRoot] [graphKeyRightRoot]

/-- Default finite fuel preserves the one-layer oxygen-before-carbon graph-key decision. -/
theorem graphKeyDefaultFuelTrace_outcome_eq_gt :
    cipTraceOutcome graphKeyDefaultFuelTrace = Ordering.gt := by
  norm_num [cipTraceOutcome, graphKeyDefaultFuelTrace, graphKeyLeftRoot, graphKeyRightRoot,
    MoleculeGraph.compareOfficialHierarchicalDigraphTrace,
    MoleculeGraph.compareOfficialLayerTrace, MoleculeGraph.sortOfficialLayer,
    MoleculeGraph.compareOfficialNodeListTrace, MoleculeGraph.compareOfficialNodeTrace,
    MoleculeGraph.compareOfficialNodeProvenanceTrace,
    MoleculeGraph.duplicateRootDistanceDecision, MoleculeGraph.officialNodeAtomLabel,
    MoleculeGraph.rawCIPAtomLabel, heteroMol, OfficialCIPNode.rootFromEdge,
    CIPRuleEngine.compareAtomLabelTrace, CIPRuleEngine.priorityNatDecision,
    CIPRuleEngine.comparePriorityNat]
  simp

/-- The bounded constitutional certificate of the default-fuel graph-key request. -/
private def graphKeyDefaultFuelRequestCertificateValue : CIPTraceCertificate :=
  CIPRuleEngine.compareDigraphThenOfficialCertificate
    (OfficialRuleMajorKey.compareTrace (heteroRootKey 1) (heteroRootKey 2))
    (graphKeyDefaultFuelRequest.branchContext graphKeyDefaultFuelRequest.left)
    (graphKeyDefaultFuelRequest.branchContext graphKeyDefaultFuelRequest.right)

private theorem graphKeyDefaultFuelRequest_certificate :
    graphKeyDefaultFuelRequest.certificate =
      some graphKeyDefaultFuelRequestCertificateValue := by
  apply certificate_eq_some_of_keys (request := graphKeyDefaultFuelRequest)
    (leftKey := heteroRootKey 1) (rightKey := heteroRootKey 2) (outcome := Ordering.gt)
  · simpa [graphKeyDefaultFuelRequest, Engine.OfficialStereoRequest.oneCenter, heteroOne,
      starLigandAtom, heteroRootKey] using hetero_build_eq_one 7
  · simpa [graphKeyDefaultFuelRequest, Engine.OfficialStereoRequest.oneCenter, heteroOne,
      starLigandAtom, heteroRootKey] using hetero_build_eq_two 7
  · exact heteroRootKey_compare_gt

private theorem graphKeyDefaultFuelRequestCertificateValue_outcome :
    graphKeyDefaultFuelRequestCertificateValue.outcome = Ordering.gt := by
  unfold graphKeyDefaultFuelRequestCertificateValue
  rw [CIPRuleEngine.compareDigraphThenOfficialCertificate_outcome,
    CIPRuleEngine.compareDigraphThenOfficialTrace_outcome_of_digraph_ne_eq
      (by rw [heteroRootKey_trace_outcome_gt]; decide)]
  exact heteroRootKey_trace_outcome_gt

/-- Public default-fuel graph-key comparison: oxygen outranks carbon. -/
theorem graphKeyDefaultFuelRequest_outcome_eq_gt :
    graphKeyDefaultFuelRequest.outcome = some Ordering.gt := by
  simp [Engine.OfficialStereoRequest.outcome, graphKeyDefaultFuelRequest_certificate,
    graphKeyDefaultFuelRequestCertificateValue_outcome]

/-- Total public decision for the default-fuel graph-key request. -/
def graphKeyDefaultFuelDecision : Engine.OfficialStereoDecision graphKeyDefaultFuelRequest :=
  Engine.decideOfficialStereo graphKeyDefaultFuelRequest

/-- The default-fuel graph-key public decision exposes the expected comparison result. -/
theorem graphKeyDefaultFuelDecision_outcome_eq_some_gt :
    graphKeyDefaultFuelDecision.outcome? = some Ordering.gt := by
  unfold graphKeyDefaultFuelDecision
  have hne : graphKeyDefaultFuelRequestCertificateValue.outcome ≠ Ordering.eq := by
    rw [graphKeyDefaultFuelRequestCertificateValue_outcome]
    decide
  simpa [graphKeyDefaultFuelRequestCertificateValue_outcome] using
    Engine.OfficialStereoRequest.decideOfficialStereo_outcome_eq_some_of_ne_eq
      graphKeyDefaultFuelRequest graphKeyDefaultFuelRequest_certificate hne

/-- Named checked certificate for the default-fuel graph-key transaction. -/
def graphKeyDefaultFuelCertificate :
    Engine.CertifiedOfficialStereoComparison graphKeyDefaultFuelRequest where
  expected := Ordering.gt
  proof := graphKeyDefaultFuelRequest_outcome_eq_gt
  artifact :=
    Engine.compileOfficialStereoTransaction graphKeyDefaultFuelRequest Ordering.gt
      graphKeyDefaultFuelRequest_outcome_eq_gt
  artifact_eq := rfl

/-- The compiled default-fuel graph-key artifact is Lean-checked. -/
theorem graphKeyDefaultFuelCertificate_checked :
    graphKeyDefaultFuelCertificate.artifact.claim :=
  graphKeyDefaultFuelCertificate.artifact_checked

/-! ### Multiple-bond duplicate-node public transaction -/


def multipleBondTheoremPlan : Engine.PublicOfficialStereoTheoremPlan where
  imports :=
    [ "TetraStereo.Engine.OfficialStereoTransaction"
    , "TetraStereo.Examples.OfficialStereoTransaction"
    ]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "multiple_bond_duplicate_official_comparison"
  requestExpr := "TetraStereo.Examples.OfficialStereoTransaction.multipleBondRequest"
  proofTerm :=
    "  exact TetraStereo.Examples.OfficialStereoTransaction.multipleBondRequest_outcome_eq_gt"

/-- Public request where a multiple-bond duplicate frontier resolves branch `0` before branch `1`. -/
def multipleBondRequest : Engine.OfficialStereoRequest where
  normalized := multipleBondNormalized
  annotations := {}
  molecule := multipleBondMulti
  profile := DescriptorSourcePolicyProfile.exactDistance
  graphFuel := 2
  center := multipleBondCenter
  localMolecule := multipleBondOne
  left := 0
  right := 1
  theoremPlan := multipleBondTheoremPlan

/-- The generated duplicate child on the left branch has multiple-bond provenance. -/
theorem multipleBond_left_duplicate_provenance :
    (OfficialCIPNode.rootFromEdge (V := Atom) 0 1).childProvenance 0 1 =
      OfficialCIPNodeProvenance.multipleBondDuplicate 1 := by
  rfl

/-- A nonempty official layer outranks an exhausted layer, independently of deterministic sort order. -/
theorem compareOfficialLayerTrace_outcome_gt_of_left_nonempty_right_nil
    (m : MoleculeGraph Atom) {left : List (OfficialCIPNode Atom)} (hleft : left ≠ []) :
    cipTraceOutcome (m.compareOfficialLayerTrace left []) = Ordering.gt := by
  unfold MoleculeGraph.compareOfficialLayerTrace MoleculeGraph.sortOfficialLayer
  cases hsort : left.mergeSort m.officialNodeBefore with
  | nil =>
      have hlen := congrArg List.length hsort
      rw [List.length_mergeSort] at hlen
      exact (hleft (List.eq_nil_of_length_eq_zero hlen)).elim
  | cons head tail =>
      simp [MoleculeGraph.compareOfficialNodeListTrace,
        CIPRuleEngine.frontierExhaustionDecision]

/-- The first double-bonded ligand sees only the stereocenter as its graph neighbor. -/
theorem multipleBond_neighborFinset_one :
    multipleBondMol.neighborFinset (1 : Atom) = {0} := by
  ext u
  fin_cases u <;> simp [MoleculeGraph.neighborFinset, MoleculeGraph.Adj, multipleBondMol,
    multipleBondBond, starBond]

/-- The single-bonded comparison ligand sees only the stereocenter as its graph neighbor. -/
theorem multipleBond_neighborFinset_two :
    multipleBondMol.neighborFinset (2 : Atom) = {0} := by
  ext u
  fin_cases u <;> simp [MoleculeGraph.neighborFinset, MoleculeGraph.Adj, multipleBondMol,
    multipleBondBond, starBond]

/-- The first multiple-bond branch expands to the generated duplicate copy of the parent atom. -/
theorem multipleBond_left_nextFrontier_eq :
    multipleBondMol.officialCIPNextFrontier
      [OfficialCIPNode.rootFromEdge (V := Atom) 0 1] =
        [(OfficialCIPNode.rootFromEdge (V := Atom) 0 1).extend 0 1] := by
  unfold MoleculeGraph.officialCIPNextFrontier MoleculeGraph.officialCIPChildren
  simp only [List.flatMap_cons, List.flatMap_nil]
  unfold MoleculeGraph.officialChildCopies MoleculeGraph.officialNeighborCopies
  simp [OfficialCIPNode.rootFromEdge]
  rw [multipleBond_neighborFinset_one]
  simp [Finset.toList_singleton, multipleBondMol, multipleBondBond, starBond,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNode.parent?, OfficialCIPNode.extend,
    OfficialCIPNode.childProvenance, OfficialCIPNode.duplicateRootDistance, OfficialCIPNode.depth,
    firstIndexOf?]
  exact ⟨1, by decide⟩

/-- The first multiple-bond branch has a nonempty duplicate-node successor frontier. -/
theorem multipleBond_left_nextFrontier_nonempty :
    multipleBondMol.officialCIPNextFrontier
      [OfficialCIPNode.rootFromEdge (V := Atom) 0 1] ≠ [] := by
  rw [multipleBond_left_nextFrontier_eq]
  decide

/-- The single-bond comparison branch has no successor frontier after the parent edge is removed. -/
theorem multipleBond_right_nextFrontier_eq_nil :
    multipleBondMol.officialCIPNextFrontier
      [OfficialCIPNode.rootFromEdge (V := Atom) 0 2] = [] := by
  unfold MoleculeGraph.officialCIPNextFrontier MoleculeGraph.officialCIPChildren
  simp only [List.flatMap_cons, List.flatMap_nil]
  unfold MoleculeGraph.officialChildCopies MoleculeGraph.officialNeighborCopies
  simp [OfficialCIPNode.rootFromEdge]
  rw [multipleBond_neighborFinset_two]
  simp [Finset.toList_singleton, multipleBondMol, multipleBondBond, starBond,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNode.parent?]

/-- The same-depth real-atom roots tie under the total Rule-1b observation before the generated
duplicate frontier is inspected. -/
theorem multipleBondRootLayer_outcome_eq :
    cipTraceOutcome
      (multipleBondMol.compareOfficialLayerTrace
        [OfficialCIPNode.rootFromEdge (V := Atom) 0 1]
        [OfficialCIPNode.rootFromEdge (V := Atom) 0 2]) = Ordering.eq := by
  norm_num [MoleculeGraph.compareOfficialLayerTrace, MoleculeGraph.sortOfficialLayer,
    MoleculeGraph.compareOfficialNodeListTrace, MoleculeGraph.compareOfficialNodeTrace,
    MoleculeGraph.compareOfficialNodeProvenanceTrace,
    MoleculeGraph.duplicateRootDistanceDecision, MoleculeGraph.officialNodeAtomLabel,
    MoleculeGraph.rawCIPAtomLabel, multipleBondMol, OfficialCIPNode.rootFromEdge,
    OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.depth,
    CIPRuleEngine.compareAtomLabelTrace, CIPRuleEngine.priorityNatDecision,
    CIPRuleEngine.comparePriorityNat]

/-- Concrete legacy layer-major graph trace for the multiple-bond duplicate frontier comparison. -/
def multipleBondTrace : List CIPRuleDecision :=
  multipleBondMol.compareOfficialHierarchicalDigraphTrace 2
    [OfficialCIPNode.rootFromEdge 0 1] [OfficialCIPNode.rootFromEdge 0 2]

/-- A generated multiple-bond duplicate frontier makes branch `0` outrank the exhausted branch. -/
theorem multipleBondTrace_outcome_eq_gt :
    cipTraceOutcome multipleBondTrace = Ordering.gt := by
  rw [multipleBondTrace, MoleculeGraph.compareOfficialHierarchicalDigraphTrace]
  simp [multipleBondRootLayer_outcome_eq,
    cipTraceOutcome_append_of_left_eq multipleBondRootLayer_outcome_eq,
    MoleculeGraph.compareOfficialHierarchicalDigraphTrace_one,
    multipleBond_right_nextFrontier_eq_nil]
  exact compareOfficialLayerTrace_outcome_gt_of_left_nonempty_right_nil multipleBondMol
    multipleBond_left_nextFrontier_nonempty

/-! #### Rule-major keys for the multiple-bond request -/

/-- The single-bonded comparison ligand of the multiple-bond graph is terminal. -/
private theorem multipleBond_children_eq_nil_two :
    multipleBondMol.officialCIPChildren
        (OfficialCIPNode.rootFromEdge (V := Atom) 0 2) = [] := by
  unfold MoleculeGraph.officialCIPChildren MoleculeGraph.officialChildCopies
    MoleculeGraph.officialNeighborCopies
  simp [OfficialCIPNode.rootFromEdge]
  rw [multipleBond_neighborFinset_two]
  simp [Finset.toList_singleton, multipleBondMol, multipleBondBond, starBond,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNode.parent?]

/-- At every fuel, the terminal single-bonded multiple-bond-graph ligand compiles to its root key. -/
private theorem multipleBond_build_eq_two (fuel : ℕ) :
    multipleBondMol.buildOfficialRuleMajorKey multipleBondMol.officialCIPChildren fuel
        (OfficialCIPNode.rootFromEdge (V := Atom) 0 2) =
      some (multipleBondMol.officialRuleMajorRootKey
        (OfficialCIPNode.rootFromEdge (V := Atom) 0 2) true) := by
  cases fuel with
  | zero =>
      simp [MoleculeGraph.buildOfficialRuleMajorKey, multipleBond_children_eq_nil_two]
  | succ fuel =>
      simp [MoleculeGraph.buildOfficialRuleMajorKey, multipleBond_children_eq_nil_two]

/-- Root node of the double-bonded left branch. -/
private def multipleBondLeftRoot : OfficialCIPNode Atom :=
  OfficialCIPNode.rootFromEdge (V := Atom) 0 1

/-- Generated duplicate child of the double-bonded left branch. -/
private def multipleBondLeftChild : OfficialCIPNode Atom :=
  multipleBondLeftRoot.extend 0 1

/-- Right (single-bonded) comparison root. -/
private def multipleBondRightRoot : OfficialCIPNode Atom :=
  OfficialCIPNode.rootFromEdge (V := Atom) 0 2

/-- The generated multiple-bond copy is a duplicate leaf and therefore has no children. -/
private theorem multipleBond_child_children_eq_nil :
    multipleBondMol.officialCIPChildren multipleBondLeftChild = [] := by
  unfold MoleculeGraph.officialCIPChildren
  simp [multipleBondLeftChild, multipleBondLeftRoot, OfficialCIPNode.isDuplicateLeaf,
    OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
    OfficialCIPNodeProvenance.isDuplicateLeaf]

/-- The duplicate child compiles to its complete root key at every fuel. -/
private theorem multipleBond_child_build (fuel : ℕ) :
    multipleBondMol.buildOfficialRuleMajorKey multipleBondMol.officialCIPChildren fuel
        multipleBondLeftChild =
      some (multipleBondMol.officialRuleMajorRootKey multipleBondLeftChild true) := by
  cases fuel with
  | zero =>
      simp [MoleculeGraph.buildOfficialRuleMajorKey, multipleBond_child_children_eq_nil]
  | succ fuel =>
      simp [MoleculeGraph.buildOfficialRuleMajorKey, multipleBond_child_children_eq_nil]

/-- The double-bonded root's child enumeration is exactly the generated duplicate. -/
private theorem multipleBond_left_children_eq :
    multipleBondMol.officialCIPChildren multipleBondLeftRoot =
      [multipleBondLeftChild] := by
  have frontier := multipleBond_left_nextFrontier_eq
  simpa [multipleBondLeftRoot, multipleBondLeftChild,
    MoleculeGraph.officialCIPNextFrontier, List.flatMap_cons, List.flatMap_nil] using frontier

/-- At fuel two the double-bonded root has assembled its generated duplicate branch. -/
private def multipleBondLeftKey : OfficialRuleMajorKey Atom :=
  OfficialRuleMajorKey.assemble
    (multipleBondMol.officialRuleMajorRootKey multipleBondLeftRoot false)
    [multipleBondMol.officialRuleMajorRootKey multipleBondLeftChild true]

/-- The single-bonded comparison root key. -/
private def multipleBondRightKey : OfficialRuleMajorKey Atom :=
  multipleBondMol.officialRuleMajorRootKey multipleBondRightRoot true

/-- The singleton child compilation step at the inner fuel. -/
private theorem multipleBond_left_childKeys :
    ([multipleBondLeftChild] : List (OfficialCIPNode Atom)).mapM
        (multipleBondMol.buildOfficialRuleMajorKey
          multipleBondMol.officialCIPChildren 1) =
      some [multipleBondMol.officialRuleMajorRootKey multipleBondLeftChild true] := by
  simp [multipleBond_child_build, List.mapM_cons, List.mapM_nil,
    Option.bind_some, Option.pure_def]

/-- Sorting a singleton key list is definitionally the identity: the empty tail is already
sorted, and insertion into the empty list returns the key itself. -/
private theorem multipleBond_sort?_singleton (key : OfficialRuleMajorKey Atom) :
    OfficialRuleMajorKey.sort? [key] = some [key] :=
  rfl

private theorem multipleBond_left_build_two :
    multipleBondMol.buildOfficialRuleMajorKey multipleBondMol.officialCIPChildren 2
        multipleBondLeftRoot = some multipleBondLeftKey := by
  unfold MoleculeGraph.buildOfficialRuleMajorKey
  dsimp only
  rw [multipleBond_left_children_eq]
  rw [if_neg (by simp)]
  rw [multipleBond_left_childKeys]
  rfl

/-- The assembled duplicate branch outranks the exhausted single-bond branch by Rule 1a. -/
private theorem multipleBond_compare_gt :
    OfficialRuleMajorKey.compare? multipleBondLeftKey multipleBondRightKey =
      some Ordering.gt := by
  decide

/-- The assembled-key trace is decisively `gt` at its Rule-1a decision. -/
private theorem multipleBond_trace_outcome_gt :
    cipTraceOutcome (OfficialRuleMajorKey.compareTrace multipleBondLeftKey multipleBondRightKey) =
      Ordering.gt := by
  decide

/-- The bounded rule-major certificate of the multiple-bond request. -/
private def multipleBondRequestCertificateValue : CIPTraceCertificate :=
  CIPRuleEngine.compareDigraphThenOfficialCertificate
    (OfficialRuleMajorKey.compareTrace multipleBondLeftKey multipleBondRightKey)
    (multipleBondRequest.branchContext multipleBondRequest.left)
    (multipleBondRequest.branchContext multipleBondRequest.right)

private theorem multipleBondRequest_certificate :
    multipleBondRequest.certificate = some multipleBondRequestCertificateValue := by
  apply certificate_eq_some_of_keys (request := multipleBondRequest)
    (leftKey := multipleBondLeftKey) (rightKey := multipleBondRightKey)
    (outcome := Ordering.gt)
  · simpa [multipleBondRequest, Engine.OfficialStereoRequest.oneCenter, multipleBondOne,
      starLigandAtom, multipleBondLeftRoot, multipleBondLeftKey] using
      multipleBond_left_build_two
  · simpa [multipleBondRequest, Engine.OfficialStereoRequest.oneCenter, multipleBondOne,
      starLigandAtom, multipleBondRightRoot, multipleBondRightKey] using
      multipleBond_build_eq_two 2
  · exact multipleBond_compare_gt

private theorem multipleBondRequestCertificateValue_outcome :
    multipleBondRequestCertificateValue.outcome = Ordering.gt := by
  unfold multipleBondRequestCertificateValue
  rw [CIPRuleEngine.compareDigraphThenOfficialCertificate_outcome,
    CIPRuleEngine.compareDigraphThenOfficialTrace_outcome_of_digraph_ne_eq
      (by rw [multipleBond_trace_outcome_gt]; decide)]
  exact multipleBond_trace_outcome_gt

/-- Public multiple-bond duplicate-node comparison. -/
theorem multipleBondRequest_outcome_eq_gt :
    multipleBondRequest.outcome = some Ordering.gt := by
  simp [Engine.OfficialStereoRequest.outcome, multipleBondRequest_certificate,
    multipleBondRequestCertificateValue_outcome]

/-- Total public decision for the multiple-bond duplicate-node request. -/
def multipleBondDecision : Engine.OfficialStereoDecision multipleBondRequest :=
  Engine.decideOfficialStereo multipleBondRequest

/-- The multiple-bond public decision exposes the expected comparison result. -/
theorem multipleBondDecision_outcome_eq_some_gt :
    multipleBondDecision.outcome? = some Ordering.gt := by
  unfold multipleBondDecision
  have hne : multipleBondRequestCertificateValue.outcome ≠ Ordering.eq := by
    rw [multipleBondRequestCertificateValue_outcome]
    decide
  simpa [multipleBondRequestCertificateValue_outcome] using
    Engine.OfficialStereoRequest.decideOfficialStereo_outcome_eq_some_of_ne_eq
      multipleBondRequest multipleBondRequest_certificate hne

/-- Named checked certificate for the multiple-bond duplicate-node transaction. -/
def multipleBondCertificate :
    Engine.CertifiedOfficialStereoComparison multipleBondRequest where
  expected := Ordering.gt
  proof := multipleBondRequest_outcome_eq_gt
  artifact :=
    Engine.compileOfficialStereoTransaction multipleBondRequest Ordering.gt
      multipleBondRequest_outcome_eq_gt
  artifact_eq := rfl

/-- The compiled multiple-bond duplicate-node artifact is Lean-checked. -/
theorem multipleBondCertificate_checked :
    multipleBondCertificate.artifact.claim :=
  multipleBondCertificate.artifact_checked

/-! ### Virtual auxiliary-node public transaction -/

/-- External annotations for virtual-node routing: auxiliary `R/S` plus phantom/lone-pair nodes. -/
def virtualNodeAnnotations : IndexedNoncenterStereoAnnotations where
  auxiliaryRule5Nodes :=
    [ { anchor := 1
        support := [1]
        descriptor := OfficialRule5Descriptor.descriptorR
        rootDistance? := some 0 }
    , { anchor := 2
        support := [2]
        descriptor := OfficialRule5Descriptor.descriptorS
        rootDistance? := some 1 }
    ]
  phantomNodes :=
    [ { anchor := 3
        support := [3]
        rootDistance? := some 2 } ]
  lonePairNodes :=
    [ { anchor := 4
        support := [4]
        rootDistance? := some 3 } ]

/-- Virtual official nodes supplied to the descriptor-source branch policy. -/
def virtualOfficialNodesAtDepth (_center : starMulti.Center) (branch : Fin 4) (depth : ℕ) :
    List (OfficialCIPNode Atom) :=
  if depth = 0 then
    if branch = 0 then
      [OfficialCIPNode.auxiliary (V := Atom) 0]
    else if branch = 1 then
      [OfficialCIPNode.auxiliary (V := Atom) 1]
    else
      []
  else
    []


def virtualAuxiliaryTheoremPlan : Engine.PublicOfficialStereoTheoremPlan where
  imports :=
    [ "TetraStereo.Engine.OfficialStereoTransaction"
    , "TetraStereo.Examples.OfficialStereoTransaction"
    ]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "virtual_auxiliary_official_comparison"
  requestExpr := "TetraStereo.Examples.OfficialStereoTransaction.virtualAuxiliaryRequest"
  proofTerm :=
    "  exact TetraStereo.Examples.OfficialStereoTransaction.virtualAuxiliaryRequest_outcome_eq_gt"

/-- Public request where virtual auxiliary nodes route Rule-5 descriptors into branch contexts. -/
def virtualAuxiliaryRequest : Engine.OfficialStereoRequest where
  normalized := starNormalized
  annotations := virtualNodeAnnotations
  molecule := starMulti
  profile := DescriptorSourcePolicyProfile.exactDistance
  officialNodesAtDepth := virtualOfficialNodesAtDepth
  graphFuel := 0
  scheduleFuel := 0
  branchFuel := 0
  center := starCenter
  localMolecule := starOne
  left := 0
  right := 1
  theoremPlan := virtualAuxiliaryTheoremPlan

/-- The left virtual auxiliary node routes to auxiliary `R`. -/
theorem virtualAuxiliaryRequest_left_rule5 :
    (virtualAuxiliaryRequest.branchContext 0).rule5Descriptor? =
      some OfficialRule5Descriptor.descriptorR.asAuxiliary :=
  rfl

/-- The right virtual auxiliary node routes to auxiliary `S`. -/
theorem virtualAuxiliaryRequest_right_rule5 :
    (virtualAuxiliaryRequest.branchContext 1).rule5Descriptor? =
      some OfficialRule5Descriptor.descriptorS.asAuxiliary :=
  rfl

/-- The public policy can route the registered phantom node by exact virtual-node distance. -/
theorem virtualAuxiliaryRequest_phantom_routes :
    (virtualAuxiliaryRequest.policy.unitsAtOfficialNode
      (OfficialCIPNode.phantom (V := Atom) 2)).length = 1 :=
  rfl

/-- The public policy can route the registered lone-pair node by exact virtual-node distance. -/
theorem virtualAuxiliaryRequest_lonePair_routes :
    (virtualAuxiliaryRequest.policy.unitsAtOfficialNode
      (OfficialCIPNode.lonePair (V := Atom) 3)).length = 1 :=
  rfl

/-- The virtual-node transaction records exact virtual-node placement policy. -/
theorem virtualAuxiliaryRequest_exactVirtualPlacementPolicy :
    virtualAuxiliaryRequest.exactVirtualPlacementPolicy = true :=
  rfl


theorem virtualAuxiliaryRequest_left_audit_auxiliary :
    (virtualAuxiliaryRequest.branchAudit 0).auxiliarySources = true :=
  rfl

/-- The bounded constitutional certificate of the virtual auxiliary-node request. -/
private def virtualAuxiliaryRequestCertificateValue : CIPTraceCertificate :=
  CIPRuleEngine.compareDigraphThenOfficialCertificate
    (OfficialRuleMajorKey.compareTrace (starRootKey 1) (starRootKey 2))
    (virtualAuxiliaryRequest.branchContext virtualAuxiliaryRequest.left)
    (virtualAuxiliaryRequest.branchContext virtualAuxiliaryRequest.right)

private theorem virtualAuxiliaryRequest_certificate :
    virtualAuxiliaryRequest.certificate = some virtualAuxiliaryRequestCertificateValue := by
  apply certificate_eq_some_of_keys (request := virtualAuxiliaryRequest)
    (leftKey := starRootKey 1) (rightKey := starRootKey 2) (outcome := Ordering.eq)
  · simpa [virtualAuxiliaryRequest, Engine.OfficialStereoRequest.oneCenter, starOne,
      starLigandAtom, starRootKey] using star_build_eq_one 0
  · simpa [virtualAuxiliaryRequest, Engine.OfficialStereoRequest.oneCenter, starOne,
      starLigandAtom, starRootKey] using star_build_eq_two 0
  · exact starRootKey_compare_eq

/-- Auxiliary `R` outranks auxiliary `S` at Rule 5 after earlier context rules tie. -/
private theorem virtualAuxiliaryRequest_context_outcome :
    cipTraceOutcome (CIPRuleEngine.compareOfficialContextTrace
      (virtualAuxiliaryRequest.branchContext virtualAuxiliaryRequest.left)
      (virtualAuxiliaryRequest.branchContext virtualAuxiliaryRequest.right)) = Ordering.gt := by
  decide

private theorem virtualAuxiliaryRequestCertificateValue_outcome :
    virtualAuxiliaryRequestCertificateValue.outcome = Ordering.gt := by
  unfold virtualAuxiliaryRequestCertificateValue
  rw [CIPRuleEngine.compareDigraphThenOfficialCertificate_outcome,
    CIPRuleEngine.compareDigraphThenOfficialTrace_outcome_of_digraph_eq starRootKey_trace_outcome_eq]
  exact virtualAuxiliaryRequest_context_outcome

/-- Public virtual auxiliary-node comparison: auxiliary `R` outranks auxiliary `S`. -/
theorem virtualAuxiliaryRequest_outcome_eq_gt :
    virtualAuxiliaryRequest.outcome = some Ordering.gt := by
  simp [Engine.OfficialStereoRequest.outcome, virtualAuxiliaryRequest_certificate,
    virtualAuxiliaryRequestCertificateValue_outcome]

/-- Total public decision for the virtual auxiliary-node request. -/
def virtualAuxiliaryDecision : Engine.OfficialStereoDecision virtualAuxiliaryRequest :=
  Engine.decideOfficialStereo virtualAuxiliaryRequest

/-- The virtual auxiliary public decision exposes the expected comparison result. -/
theorem virtualAuxiliaryDecision_outcome_eq_some_gt :
    virtualAuxiliaryDecision.outcome? = some Ordering.gt := by
  unfold virtualAuxiliaryDecision
  have hne : virtualAuxiliaryRequestCertificateValue.outcome ≠ Ordering.eq := by
    rw [virtualAuxiliaryRequestCertificateValue_outcome]
    decide
  simpa [virtualAuxiliaryRequestCertificateValue_outcome] using
    Engine.OfficialStereoRequest.decideOfficialStereo_outcome_eq_some_of_ne_eq
      virtualAuxiliaryRequest virtualAuxiliaryRequest_certificate hne

/-- Named checked certificate for the virtual auxiliary-node transaction. -/
def virtualAuxiliaryCertificate :
    Engine.CertifiedOfficialStereoComparison virtualAuxiliaryRequest where
  expected := Ordering.gt
  proof := virtualAuxiliaryRequest_outcome_eq_gt
  artifact :=
    Engine.compileOfficialStereoTransaction virtualAuxiliaryRequest Ordering.gt
      virtualAuxiliaryRequest_outcome_eq_gt
  artifact_eq := rfl

/-- The compiled virtual auxiliary-node artifact is Lean-checked. -/
theorem virtualAuxiliaryCertificate_checked :
    virtualAuxiliaryCertificate.artifact.claim :=
  virtualAuxiliaryCertificate.artifact_checked

/-- Empty detector annotations force the public official-stereo transaction to refuse. -/
def emptyDetectorRequest : Engine.OfficialStereoRequest where
  normalized := starNormalized
  annotations := {}
  molecule := starMulti
  profile := DescriptorSourcePolicyProfile.exactDistance
  graphFuel := 0
  scheduleFuel := 0
  branchFuel := 0
  center := starCenter
  localMolecule := starOne
  left := 0
  right := 1
  theoremPlan :=
    { helicalBranchTheoremPlan with
      theoremName := "empty_detector_official_stereo_refusal"
      requestExpr := "TetraStereo.Examples.OfficialStereoTransaction.emptyDetectorRequest"
      proofTerm :=
        "  exact TetraStereo.Examples.OfficialStereoTransaction.emptyDetectorRequest_refusal_claim" }

/-- The bounded constitutional certificate of the empty-detector request.  The constitutional
comparison completes and ties; the empty contexts cannot break the tie. -/
private def emptyDetectorRequestCertificateValue : CIPTraceCertificate :=
  CIPRuleEngine.compareDigraphThenOfficialCertificate
    (OfficialRuleMajorKey.compareTrace (starRootKey 1) (starRootKey 2))
    (emptyDetectorRequest.branchContext emptyDetectorRequest.left)
    (emptyDetectorRequest.branchContext emptyDetectorRequest.right)

private theorem emptyDetectorRequest_certificate :
    emptyDetectorRequest.certificate = some emptyDetectorRequestCertificateValue := by
  apply certificate_eq_some_of_keys (request := emptyDetectorRequest)
    (leftKey := starRootKey 1) (rightKey := starRootKey 2) (outcome := Ordering.eq)
  · simpa [emptyDetectorRequest, Engine.OfficialStereoRequest.oneCenter, starOne,
      starLigandAtom, starRootKey] using star_build_eq_one 0
  · simpa [emptyDetectorRequest, Engine.OfficialStereoRequest.oneCenter, starOne,
      starLigandAtom, starRootKey] using star_build_eq_two 0
  · exact starRootKey_compare_eq

/-- With no detector facts both branch contexts are empty, so every later rule ties as well. -/
private theorem emptyDetectorRequest_context_outcome :
    cipTraceOutcome (CIPRuleEngine.compareOfficialContextTrace
      (emptyDetectorRequest.branchContext emptyDetectorRequest.left)
      (emptyDetectorRequest.branchContext emptyDetectorRequest.right)) = Ordering.eq := by
  decide

private theorem emptyDetectorRequestCertificateValue_outcome_eq :
    emptyDetectorRequestCertificateValue.outcome = Ordering.eq := by
  unfold emptyDetectorRequestCertificateValue
  rw [CIPRuleEngine.compareDigraphThenOfficialCertificate_outcome,
    CIPRuleEngine.compareDigraphThenOfficialTrace_outcome_of_digraph_eq starRootKey_trace_outcome_eq]
  exact emptyDetectorRequest_context_outcome

/-- The request's own bounded certificate exists and ties, so it is not certificate-ready. -/
private theorem emptyDetectorRequest_certificateReady_eq_false :
    emptyDetectorRequest.certificateReady = false := by
  apply (Engine.OfficialStereoRequest.certificateReady_eq_false_iff emptyDetectorRequest).2
  exact Or.inr ⟨emptyDetectorRequestCertificateValue, emptyDetectorRequest_certificate,
    emptyDetectorRequestCertificateValue_outcome_eq⟩

/-- The request's optional outcome is the completed constitutional/context tie. -/
private theorem emptyDetectorRequest_outcome_eq :
    emptyDetectorRequest.outcome = some Ordering.eq := by
  simp [Engine.OfficialStereoRequest.outcome, emptyDetectorRequest_certificate,
    emptyDetectorRequestCertificateValue_outcome_eq]

/-- The reason this request justifies is exactly the unresolved-official-priorities reason. -/
theorem emptyDetectorRequest_officialRefusalReason :
    emptyDetectorRequest.officialRefusalReason? =
      some Engine.RefusalReason.unresolvedOfficialPriorities :=
  Engine.OfficialStereoRequest.officialRefusalReason_eq_some_unresolvedOfficialPriorities_of_outcome_eq
    emptyDetectorRequest emptyDetectorRequest_outcome_eq

/-- Empty detector annotations are not ready for a detector-backed official-stereo certificate, and
the certificate's declared reason matches the one the request justifies. -/
theorem emptyDetectorRequest_refusal_claim :
    Engine.OfficialStereoRefusalClaim emptyDetectorRequest
      Engine.RefusalReason.unresolvedOfficialPriorities :=
  ⟨emptyDetectorRequest_certificateReady_eq_false,
    emptyDetectorRequest_officialRefusalReason⟩

/-- A refusal certificate cannot advertise a reason the request does not exhibit.

This is the regression that the pinned refusal claim buys.  While `OfficialStereoRefusalClaim`
ignored its reason argument, this proposition was *false*: all four `RefusalReason` values produced
the identical claim, so a certificate could truthfully be titled with the wrong cause. -/
theorem emptyDetectorRequest_not_refusal_claim_unsupportedInput :
    ¬ Engine.OfficialStereoRefusalClaim emptyDetectorRequest
        Engine.RefusalReason.unsupportedInput := by
  rintro ⟨-, hreason⟩
  rw [emptyDetectorRequest_officialRefusalReason] at hreason
  exact absurd hreason (by decide)

/-- The same holds for `unsupportedStereoElement`. -/
theorem emptyDetectorRequest_not_refusal_claim_unsupportedStereoElement :
    ¬ Engine.OfficialStereoRefusalClaim emptyDetectorRequest
        Engine.RefusalReason.unsupportedStereoElement := by
  rintro ⟨-, hreason⟩
  rw [emptyDetectorRequest_officialRefusalReason] at hreason
  exact absurd hreason (by decide)

/-- And for `unresolvedDescriptorPriorities`, which is the sibling reason the one-center descriptor
engine uses.  That makes all three wrong reasons covered: an official-stereo refusal cannot borrow
the descriptor engine's cause. -/
theorem emptyDetectorRequest_not_refusal_claim_unresolvedDescriptorPriorities :
    ¬ Engine.OfficialStereoRefusalClaim emptyDetectorRequest
        Engine.RefusalReason.unresolvedDescriptorPriorities := by
  rintro ⟨-, hreason⟩
  rw [emptyDetectorRequest_officialRefusalReason] at hreason
  exact absurd hreason (by decide)

/-- Empty detector annotations leave the official-CIP resolution source unresolved. -/
theorem emptyDetectorRequest_resolutionSource :
    emptyDetectorRequest.resolutionSource = Engine.OfficialCIPResolutionSource.unresolved :=
  Engine.OfficialStereoRequest.resolutionSource_eq_unresolved_of_outcome_eq
    emptyDetectorRequest emptyDetectorRequest_certificate
    emptyDetectorRequestCertificateValue_outcome_eq


theorem emptyDetectorRequest_officialCompletenessReady_eq_false :
    emptyDetectorRequest.officialCompletenessReady = false := by
  simp [Engine.OfficialStereoRequest.officialCompletenessReady,
    emptyDetectorRequest_certificateReady_eq_false]

/-- Total public decision for the empty detector request. -/
def emptyDetectorDecision : Engine.OfficialStereoDecision emptyDetectorRequest :=
  Engine.decideOfficialStereo emptyDetectorRequest

/-- The public transaction refuses when no detector descriptor facts are registered. -/
theorem emptyDetectorDecision_outcome_eq_none :
    emptyDetectorDecision.outcome? = none := by
  unfold emptyDetectorDecision
  exact Engine.OfficialStereoRequest.decideOfficialStereo_outcome_eq_none_of_eq
    emptyDetectorRequest emptyDetectorRequest_certificate
    emptyDetectorRequestCertificateValue_outcome_eq

/-- Named checked refusal certificate for the empty detector transaction. -/
def emptyDetectorRefusal :
    Engine.CertifiedOfficialStereoRefusal emptyDetectorRequest where
  reason := Engine.RefusalReason.unresolvedOfficialPriorities
  proof := emptyDetectorRequest_refusal_claim
  artifact :=
    Engine.compileOfficialStereoRefusal emptyDetectorRequest
      Engine.RefusalReason.unresolvedOfficialPriorities emptyDetectorRequest_refusal_claim
  artifact_eq := rfl

/-- The compiled public official-stereo refusal artifact is Lean-checked. -/
theorem emptyDetectorRefusal_checked :
    emptyDetectorRefusal.artifact.claim :=
  emptyDetectorRefusal.artifact_checked

end
end OfficialStereoTransaction
end Examples
end TetraStereo
