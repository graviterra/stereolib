import TetraStereo.OneCenter.DeclarativeCIPMolecularEvidenceNaturality
import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Key
import TetraStereo.OneCenter.LocalizedRerootCompoundRule4bcKey
import TetraStereo.OneCenter.LocalizedOutwardDecoratedSourceFaithfulness
import TetraStereo.OneCenter.LocalizedOuterDigraphPhysicalObservations
import TetraStereo.OneCenter.LocalizedActualKeyTiePhysicalTransport
import TetraStereo.KernelOnly

set_option autoImplicit false














































namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput)

/-! ## Stage keys built with the actual internal-node equations -/

/-- One constitutional key shared by constitutionally identical occurrences. -/
def uniformConstitutional : OfficialRuleMajorKey input.Atom :=
  { rule1a := [], rule1b := [], rule2 := [], sourceNodes := [], complete := true }

/-- The actual leaf equation of `buildLocalizedRerootCumulativeRule45Key?`. -/
def stageLeaf (stage : LocalizedCumulativeRule45Stage) (label : Option LocalizedAuxiliaryLabel) :
    input.LocalizedRerootCumulativeRule45Key :=
  { constitutional := input.uniformConstitutional
    descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
    labels := [[([], label)]]
    rankedLabels := [[([], label)]] }

/-- The actual internal-node equation of `buildLocalizedRerootCumulativeRule45Key?`: sort the child
keys with the actual comparator, then merge beneath the sorted sibling slots. -/
def stageNode (stage : LocalizedCumulativeRule45Stage) (label : Option LocalizedAuxiliaryLabel)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.LocalizedRerootCumulativeRule45Key :=
  let sorted := input.sortLocalizedRerootCumulativeRule45Keys children
  { constitutional := input.uniformConstitutional
    descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
      input.mergeLocalizedRerootDescriptorChildren sorted
    labels := [[([], label)]] ++ input.mergeLocalizedRerootLabelChildren sorted
    rankedLabels := [[([], label)]] ++ input.mergeLocalizedRerootRankedLabelChildren sorted }

def labelR : Option LocalizedAuxiliaryLabel := some (.chiral RS.R)
def labelS : Option LocalizedAuxiliaryLabel := some (.chiral RS.S)

/-- Left ligand `R(R(-, R), S(R, R))` at a stage. -/
def stageLeft (stage : LocalizedCumulativeRule45Stage) : input.LocalizedRerootCumulativeRule45Key :=
  input.stageNode stage labelR
    [input.stageNode stage labelR [input.stageLeaf stage none, input.stageLeaf stage labelR],
     input.stageNode stage labelS [input.stageLeaf stage labelR, input.stageLeaf stage labelR]]

/-- Right ligand `R(R(S, S), S(-, R))` at a stage. -/
def stageRight (stage : LocalizedCumulativeRule45Stage) : input.LocalizedRerootCumulativeRule45Key :=
  input.stageNode stage labelR
    [input.stageNode stage labelR [input.stageLeaf stage labelS, input.stageLeaf stage labelS],
     input.stageNode stage labelS [input.stageLeaf stage none, input.stageLeaf stage labelR]]

/-- The two ligands tie under the actual stage-`rule4a` comparison. -/
theorem stageWitness_rule4a_tie :
    input.compareLocalizedRerootCumulativeRule45Keys (input.stageLeft .rule4a)
      (input.stageRight .rule4a) = .eq := by
  rfl

/-- Both select the unique Rule-4b reference `R` from their actual stage-`rule4a` ranked labels. -/
theorem stageWitness_references :
    localizedRule4bReferencesFromRankedLabels (input.stageLeft .rule4a).rankedLabels = [RS.R] ∧
      localizedRule4bReferencesFromRankedLabels (input.stageRight .rule4a).rankedLabels =
        [RS.R] := by
  constructor <;> rfl

/-- **The actual stage-`rule4b` comparison ranks the left ligand higher.** -/
theorem stageWitness_rule4b_gt :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      (input.stageLeft (.rule4b RS.R)).descriptor (input.stageRight (.rule4b RS.R)).descriptor =
        .gt := by
  rfl

/-! ## The rule-major order on the same observations -/

/-- Component `index` of every cumulative node vector. -/
def projectCumulative (index : Nat) (layers : List (List (OfficialSparseEntry (List Nat)))) :
    List (List (OfficialSparseEntry Nat)) :=
  layers.map (List.map fun entry => (entry.1, entry.2.getD index 0))

/-- **Proposed repair.**  Constitutional key, then each cumulative component over the whole
hierarchy, in rule order. -/
def compareRuleMajorCumulativeDescriptor (width : Nat)
    (left right : input.LocalizedRerootCumulativeRule45Key) : Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.constitutional) OfficialRuleMajorKey.compare)
    (fun left right =>
      List.compareLex compare
        ((List.range width).map fun index =>
          OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            (projectCumulative index left.descriptor) (projectCumulative index right.descriptor))
        ((List.range width).map fun _ => Ordering.eq))
    left right

/-- Descending insertion by an arbitrary comparator (the shape of
`insertLocalizedRerootCumulativeRule45Key`). -/
def insertKeyBy {α : Type*} (cmp : α → α → Ordering) (key : α) : List α → List α
  | [] => [key]
  | head :: tail =>
      match cmp key head with
      | .lt => head :: insertKeyBy cmp key tail
      | .eq | .gt => key :: head :: tail

/-- Descending insertion sort by an arbitrary comparator (the shape of
`sortLocalizedRerootCumulativeRule45Keys`). -/
def sortKeysBy {α : Type*} (cmp : α → α → Ordering) : List α → List α
  | [] => []
  | key :: keys => insertKeyBy cmp key (sortKeysBy cmp keys)

/-- The internal-node equation with the repaired sibling comparator. -/
def ruleMajorNode (stage : LocalizedCumulativeRule45Stage) (width : Nat)
    (label : Option LocalizedAuxiliaryLabel)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.LocalizedRerootCumulativeRule45Key :=
  let sorted := sortKeysBy (input.compareRuleMajorCumulativeDescriptor width) children
  { constitutional := input.uniformConstitutional
    descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
      input.mergeLocalizedRerootDescriptorChildren sorted
    labels := [[([], label)]] ++ input.mergeLocalizedRerootLabelChildren sorted
    rankedLabels := [[([], label)]] ++ input.mergeLocalizedRerootRankedLabelChildren sorted }

def ruleMajorLeft (stage : LocalizedCumulativeRule45Stage) (width : Nat) :
    input.LocalizedRerootCumulativeRule45Key :=
  input.ruleMajorNode stage width labelR
    [input.ruleMajorNode stage width labelR [input.stageLeaf stage none, input.stageLeaf stage labelR],
     input.ruleMajorNode stage width labelS [input.stageLeaf stage labelR, input.stageLeaf stage labelR]]

def ruleMajorRight (stage : LocalizedCumulativeRule45Stage) (width : Nat) :
    input.LocalizedRerootCumulativeRule45Key :=
  input.ruleMajorNode stage width labelR
    [input.ruleMajorNode stage width labelR [input.stageLeaf stage labelS, input.stageLeaf stage labelS],
     input.ruleMajorNode stage width labelS [input.stageLeaf stage none, input.stageLeaf stage labelR]]

set_option maxHeartbeats 4000000 in
/-- Under the rule-major layout the Rule-4a projections still tie. -/
theorem ruleMajorWitness_rule4a_tie :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (projectCumulative 0 (input.ruleMajorLeft (.rule4b RS.R) 2).descriptor)
      (projectCumulative 0 (input.ruleMajorRight (.rule4b RS.R) 2).descriptor) = .eq := by
  rfl

set_option maxHeartbeats 4000000 in
/-- **The rule-major Rule-4b comparison of the same observations ranks the right ligand higher.** -/
theorem ruleMajorWitness_rule4b_lt :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (projectCumulative 1 (input.ruleMajorLeft (.rule4b RS.R) 2).descriptor)
      (projectCumulative 1 (input.ruleMajorRight (.rule4b RS.R) 2).descriptor) = .lt := by
  rfl

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.stageWitness_rule4a_tie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.stageWitness_references
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.stageWitness_rule4b_gt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorWitness_rule4a_tie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorWitness_rule4b_lt

/-! ## The concrete reader and its identification with the molecular evidence -/

namespace TetraStereo.OneCenter

namespace DeclarativeCIP

universe u

/-- The localized auxiliary label of a tetrahedral descriptor.  Other descriptor families have no
localized auxiliary label. -/
def Descriptor.toLocalizedLabel : Descriptor → Option CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel
  | .R => some (.chiral RS.R)
  | .S => some (.chiral RS.S)
  | .r => some (.pseudoasymmetric PseudoRS.r)
  | .s => some (.pseudoasymmetric PseudoRS.s)
  | _ => none

/-- Tetrahedral descriptor values, the only ones the localized runtime represents. -/
def Descriptor.IsTetrahedral : Descriptor → Prop
  | .R | .S | .r | .s => True
  | _ => False

def OccurrenceReading.toLocalizedLabel :
    OccurrenceReading → Option CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel
  | .descriptor value => value.toLocalizedLabel
  | _ => none

def OccurrenceReading.IsTetrahedral : OccurrenceReading → Prop
  | .descriptor value => value.IsTetrahedral
  | _ => True

/-- Rule-4a priority of a reading's observation (`0` when nothing is read). -/
def OccurrenceReading.kindPriority : OccurrenceReading → ℕ
  | .descriptor value => value.unitKind.priority
  | _ => 0

/-- Rule-4c value of a reading's observation (`0 = absent`, `1 = s`, `2 = r`). -/
def OccurrenceReading.pseudoValue : OccurrenceReading → ℕ
  | .descriptor value => senseValue value.pseudoSense
  | _ => 0

/-- Rule-5 value of a reading's observation (`0 = absent`, `1 = S`, `2 = R`). -/
def OccurrenceReading.chiralValue : OccurrenceReading → ℕ
  | .descriptor value => senseValue value.chiralSense
  | _ => 0

/-- Sense of a uppercase runtime descriptor. -/
def rsSense : RS → DescriptorSense
  | .R => .senior
  | .S => .junior

section Walk

variable {Atom : Type u} [DecidableEq Atom]

omit [DecidableEq Atom] in
theorem incomingAtom?_mem (root : Atom) (path : List Atom) {atom : Atom}
    (h : incomingAtom? root path = some atom) : atom ∈ root :: path := by
  rw [incomingAtom?] at h
  split at h
  · simp at h
  · cases h
    exact List.mem_cons_self
  · rename_i _ incoming _ hreverse
    cases h
    have : atom ∈ path.reverse := by rw [hreverse]; simp
    exact List.mem_cons_of_mem _ (List.mem_reverse.1 this)

/-- An outward walk along a simple atom path never returns to a carrier parent. -/
theorem rerootWalk_eq_append (root : Atom) :
    ∀ (rest start : List Atom), (root :: (start ++ rest)).Nodup →
      rerootWalk root start rest = start ++ rest
  | [], start, _ => by simp [rerootWalk]
  | next :: rest, start, h => by
      have hdisjoint : (root :: start).Disjoint (next :: rest) :=
        List.disjoint_of_nodup_append (show ((root :: start) ++ (next :: rest)).Nodup from h)
      have hnext : next ∉ root :: start := fun hmem => hdisjoint hmem List.mem_cons_self
      have hstep : rerootStep root start next = start ++ [next] := by
        unfold rerootStep
        rw [if_neg]
        intro hincoming
        exact hnext (incomingAtom?_mem root start hincoming)
      show rerootWalk root (rerootStep root start next) rest = start ++ next :: rest
      rw [hstep, rerootWalk_eq_append root rest (start ++ [next]) (by simpa using h)]
      simp

end Walk

section TopContext

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))

/-- At a top occurrence (empty path), an outward simple ancestor path is read at the occurrence
with exactly that path. -/
theorem readContext_top_toLocalizedLabel (unit : DetectedOccurrence molecule)
    (hpath : unit.1.path = []) (steps : List Atom) (hsimple : (unit.1.root :: steps).Nodup)
    (hne : steps ≠ []) :
    (readContext molecule descriptorMap unit steps).toLocalizedLabel =
      if h : IsDetectedCenter molecule (OccurrenceUnit.atom ⟨unit.1.root, steps⟩) then
        (descriptorMap ⟨⟨unit.1.root, steps⟩, h⟩).bind Descriptor.toLocalizedLabel
      else none := by
  have hwalk : rerootWalk unit.1.root unit.1.path steps = steps := by
    rw [hpath]
    simpa using rerootWalk_eq_append unit.1.root steps [] (by simpa using hsimple)
  have hlength : unit.1.path.length < steps.length := by
    rw [hpath]
    exact List.length_pos_of_ne_nil hne
  unfold readContext contextOccurrence
  simp only [hwalk]
  by_cases hcenter : IsDetectedCenter molecule (OccurrenceUnit.atom ⟨unit.1.root, steps⟩)
  · rw [dif_pos ⟨hlength, hcenter⟩, dif_pos hcenter]
    dsimp only
    cases descriptorMap ⟨⟨unit.1.root, steps⟩, hcenter⟩ <;> rfl
  · rw [dif_neg (fun h => hcenter h.2), dif_neg hcenter]
    rfl

end TopContext

/-! ### Stage values against observation values -/

theorem kindPriority_eq_runtime (reading : OccurrenceReading) (htetrahedral : reading.IsTetrahedral) :
    CertifiedLocalizedCIPInput.localizedRule4aPriority reading.toLocalizedLabel =
      reading.kindPriority := by
  cases reading with
  | descriptor value => cases value <;> first | rfl | exact htetrahedral.elim
  | _ => rfl

/-- The runtime Rule-4b bit under reference `reference` is the declarative like/unlike priority at
an eligible reading and `0` elsewhere. -/
theorem rule4bBit_eq_runtime (reference : RS) (reading : OccurrenceReading)
    (htetrahedral : reading.IsTetrahedral) :
    CertifiedLocalizedCIPInput.localizedRule4bPriority reference reading.toLocalizedLabel =
      match reading with
      | .descriptor value =>
          match value.chiralSense with
          | some observed => (DescriptorPairKind.ofSenses (rsSense reference) observed).priority
          | none => 0
      | _ => 0 := by
  cases reading with
  | descriptor value =>
      cases reference <;> cases value <;> first | rfl | exact htetrahedral.elim
  | _ => rfl

/-- Under equal Rule-4a kinds, the runtime Rule-4c bit orders readings exactly as the declarative
Rule-4c value. -/
theorem rule4cOrder_eq_runtime (left right : OccurrenceReading)
    (hleft : left.IsTetrahedral) (hright : right.IsTetrahedral)
    (hkind : left.kindPriority = right.kindPriority) :
    compare (CertifiedLocalizedCIPInput.localizedRule4cPriority left.toLocalizedLabel)
        (CertifiedLocalizedCIPInput.localizedRule4cPriority right.toLocalizedLabel) =
      compare left.pseudoValue right.pseudoValue := by
  cases left with
  | descriptor first =>
      cases right with
      | descriptor second =>
          cases first <;> cases second <;> first | rfl | exact hleft.elim | exact hright.elim |
            exact absurd hkind (by decide)
      | _ => cases first <;> first | rfl | exact hleft.elim | exact absurd hkind (by decide)
  | _ =>
      cases right with
      | descriptor second =>
          cases second <;> first | rfl | exact hright.elim | exact absurd hkind (by decide)
      | _ => rfl

/-- Under equal Rule-4a kinds, the runtime common-`R` Rule-5 bit orders readings exactly as the
declarative Rule-5 value.  (The common-`S` reading only feeds the pseudoasymmetry flag of
`compareLocalizedRerootCompoundThroughRule5`; the ordering uses common `R`.) -/
theorem rule5Order_eq_runtime (left right : OccurrenceReading)
    (hleft : left.IsTetrahedral) (hright : right.IsTetrahedral)
    (hkind : left.kindPriority = right.kindPriority) :
    compare (CertifiedLocalizedCIPInput.localizedRule5Priority RS.R left.toLocalizedLabel)
        (CertifiedLocalizedCIPInput.localizedRule5Priority RS.R right.toLocalizedLabel) =
      compare left.chiralValue right.chiralValue := by
  cases left with
  | descriptor first =>
      cases right with
      | descriptor second =>
          cases first <;> cases second <;> first | rfl | exact hleft.elim | exact hright.elim |
            exact absurd hkind (by decide)
      | _ => cases first <;> first | rfl | exact hleft.elim | exact absurd hkind (by decide)
  | _ =>
      cases right with
      | descriptor second =>
          cases second <;> first | rfl | exact hright.elim | exact absurd hkind (by decide)
      | _ => rfl

end DeclarativeCIP

namespace CertifiedLocalizedCIPInput

open DeclarativeCIP

variable (input : CertifiedLocalizedCIPInput)

/-- **The runtime source-context adapter.**  A runtime frame stores its atom history most recent
first, ending at the original root; the occurrence unit is the original root and the path after
it. -/
def molecularFrameUnit (frame : input.LocalizedCIPOccurrenceFrame) : OccurrenceUnit input.Atom :=
  ⟨frame.root, frame.node.history.reverse.tail⟩

/-- The dependency view read from the fixed descriptor map.  Only real-atom occurrences read a
descriptor: duplicate and placeholder occurrences carry none, as in the molecular evidence (a
multiple-bond duplicate shares its real sibling's atom history, so an atom-history lookup alone
would otherwise give it that sibling's descriptor). -/
noncomputable def molecularView
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) : input.LocalizedDependencyView target :=
  fun source _ =>
    if source.1.node.provenance = .realAtom then
      if h : IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit source.1).atom then
        (descriptorMap ⟨input.molecularFrameUnit source.1, h⟩).bind Descriptor.toLocalizedLabel
      else none
    else none

/-- **The concrete reader** obtained from the fixed descriptor map: the production dependency
reader `localizedDependencyLabel` specialized to `molecularView`. -/
noncomputable def molecularReader
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) :
    input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel :=
  input.localizedDependencyLabel target (input.molecularView descriptorMap target)

/-- **Pointwise identification.**  At a cursor of a top unit's hierarchy whose atom history is an
outward simple path from the unit, the concrete reader returns exactly the localized label of the
molecular evidence's reading at that path. -/
theorem molecularReader_eq_readContext
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (cursor : input.LocalizedRerootCursor fuel)
    (unit : DetectedOccurrence input.moleculeGraph) (hpath : unit.1.path = [])
    (htargetRoot : target.1.root = unit.1.root) (htargetAddress : target.1.address = [])
    (hroot : cursor.occurrence.1.root = unit.1.root) (haddress : cursor.occurrence.1.address ≠ [])
    (hreal : cursor.occurrence.1.node.provenance = .realAtom) (steps : List input.Atom)
    (hhistory : cursor.occurrence.1.node.history = (unit.1.root :: steps).reverse)
    (hsimple : (unit.1.root :: steps).Nodup) (hne : steps ≠ []) :
    input.molecularReader descriptorMap target cursor =
      (readContext input.moleculeGraph descriptorMap unit steps).toLocalizedLabel := by
  have hdependency : input.LocalizedDepthDependency cursor.occurrence target :=
    ⟨hroot.trans htargetRoot.symm, by rw [htargetAddress]; exact List.length_pos_of_ne_nil haddress⟩
  have hunit : input.molecularFrameUnit cursor.occurrence.1 = ⟨unit.1.root, steps⟩ := by
    simp [molecularFrameUnit, hroot, hhistory]
  rw [readContext_top_toLocalizedLabel input.moleculeGraph descriptorMap unit hpath steps hsimple hne]
  unfold molecularReader localizedDependencyLabel molecularView
  rw [dif_pos hdependency, if_pos hreal]
  simp only [hunit]

/-- Duplicate and placeholder occurrences read no descriptor. -/
theorem molecularReader_eq_none_of_not_real
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (cursor : input.LocalizedRerootCursor fuel)
    (hnotReal : cursor.occurrence.1.node.provenance ≠ .realAtom) :
    input.molecularReader descriptorMap target cursor = none := by
  unfold molecularReader localizedDependencyLabel molecularView
  split
  · rfl
  · rfl

/-- **Supported-case builder success.**  With the concrete reader, the actual cumulative builder
succeeds at every stage on the canonical ligand root of every detected center, with its exact
build equation, and the actual decorated tree erases to a faithful exact expansion. -/
theorem molecularReader_ligandRoot_build
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (center : input.TetrahedralCenter) (index : Fin 4) (stage : LocalizedCumulativeRule45Stage) :
    ∃ key : input.LocalizedRerootCumulativeRule45Key,
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
          (input.molecularReader descriptorMap target)
          (2 * (input.certified.input.molecule.atomCount + 1 + 1))
          (input.localizedLigandRootCursor center index) = some key ∧
        ∃ tree : LocalizedCumulativeDecoratedTree input
            (input.certified.input.molecule.atomCount + 1),
          tree.source = input.localizedLigandRootCursor center index ∧
            LocalizedCumulativeTreeTableMatch stage tree key ∧
              LocalizedCumulativeTreeRealizes input (input.molecularReader descriptorMap target) tree ∧
                RootedDigraph.FaithfulExactExpansion input.moleculeGraph center.1
                  (input.canonicalLigandAtom center index)
                  (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).toDeclarativeDigraph := by
  obtain ⟨key, built, tree, source, tables, realizes, _, _, faithful⟩ :=
    input.localizedLigandRoot_sourceTree_faithfulExactExpansion center index stage
      (input.molecularReader descriptorMap target)
  exact ⟨key, built, tree, source, tables, realizes, faithful⟩

/-- The detected frame of the runtime input: canonical ascending-index ligands. -/
def molecularDetectedFrame : DetectedFrame input.moleculeGraph where
  ligand unit index := input.canonicalLigandAtom
    ⟨unit.1.atom, (Finset.mem_filter.2 ⟨Finset.mem_univ _, unit.2⟩)⟩ index
  adjacent unit index := input.canonicalLigandAtom_adj
    ⟨unit.1.atom, (Finset.mem_filter.2 ⟨Finset.mem_univ _, unit.2⟩)⟩ index

/-- The top occurrence of a detected center. -/
def topUnit (center : input.TetrahedralCenter) : DetectedOccurrence input.moleculeGraph :=
  ⟨⟨center.1, []⟩, (Finset.mem_filter.1 center.2).2⟩

/-- **The actual tree is an admissible expansion of the molecular instance.**  Hence its
declarative digraph carries exactly the molecular evidence of the instance whose ordinary key model
is `detectedMolecularData_ordinaryRuleKeyModel`. -/
theorem molecularReader_ligandRoot_admissible
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (extra : ConstitutionalProblemData input.Atom (DetectedOccurrence input.moleculeGraph))
    (center : input.TetrahedralCenter) (index : Fin 4) (stage : LocalizedCumulativeRule45Stage) :
    ∃ tree : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1),
      tree.source = input.localizedLigandRootCursor center index ∧
        LocalizedCumulativeTreeRealizes input (input.molecularReader descriptorMap target) tree ∧
          (detectedMolecularData input.moleculeGraph input.molecularDetectedFrame extra).admissibleExpansion
            (input.topUnit center) index
            (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).toDeclarativeDigraph := by
  obtain ⟨_, _, tree, source, _, realizes, faithful⟩ :=
    input.molecularReader_ligandRoot_build descriptorMap target center index stage
  refine ⟨tree, source, realizes, ?_⟩
  change RootedDigraph.FaithfulExactExpansion input.moleculeGraph center.1
    (input.canonicalLigandAtom ⟨center.1, _⟩ index) _
  exact faithful

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rerootWalk_eq_append
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.readContext_top_toLocalizedLabel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.kindPriority_eq_runtime
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rule4bBit_eq_runtime
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rule4cOrder_eq_runtime
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rule5Order_eq_runtime
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularReader_eq_readContext
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularReader_eq_none_of_not_real
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularReader_ligandRoot_build
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularReader_ligandRoot_admissible

/-! ## Whole-tree identification on the actual original-root ligand tree

`molecularReader_eq_readContext` takes history, root, address and simple-path hypotheses at one
cursor.  This section derives all of them, at every node and arbitrary depth, from the actual
build: the erased source tree is generated by `executableOfficialCIPChildren` (children are
`extend`ed nodes), so every history is the reversed ancestor atom path above
`rootFromEdge center ligand`; non-real children are terminal duplicate leaves, so real histories
are simple; `LocalizedCumulativeTreeIncoming` gives every cursor a nonempty address, and
`subtreeAt?_source_occurrence_root_eq` keeps the original root.  The top unit (empty path) is the
boundary of this section. -/

namespace TetraStereo.OneCenter
namespace MolecularEvidenceTree

open DeclarativeCIP
open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree

/-! ### Ancestor paths of the erased digraph -/

section SourceTree

variable {V : Type} [DecidableEq V]

/-- Optional current atoms at the prefixes of an address, root first. -/
def pathLabels (tree : OfficialCIPSourceTree V) (address : List ℕ) : List (Option V) :=
  address.inits.map fun pre => (tree.sourceAtAddress? pre).bind OfficialCIPNode.current?

theorem declarativeLabel_atom (tree : OfficialCIPSourceTree V) (node : tree.HierarchyNode) :
    (tree.declarativeLabel node).atom? =
      (tree.sourceAtAddress? node.1).bind OfficialCIPNode.current? := by
  unfold OfficialCIPSourceTree.declarativeLabel
  split <;> rename_i hsource <;> simp [hsource, OfficialCIPNode.toDeclarativeLabel]

theorem ancestorPath_rel_toDeclarativeDigraph (tree : OfficialCIPSourceTree V) :
    ∀ (address : List ℕ) (present : address ∈ tree.hierarchyAddresses),
      AncestorPath tree.toDeclarativeDigraph ⟨address, present⟩ (pathLabels tree address) := by
  intro address
  induction address using List.reverseRecOn with
  | nil =>
      intro present
      rw [show pathLabels tree [] = [(tree.declarativeLabel ⟨[], present⟩).atom?] by
        simp [pathLabels, declarativeLabel_atom]]
      exact AncestorPath.root
  | append_singleton address slot ih =>
      intro present
      have parent : address ∈ tree.hierarchyAddresses := by
        simpa using tree.dropLast_mem_hierarchyAddresses present
      rw [show pathLabels tree (address ++ [slot]) = pathLabels tree address ++
          [(tree.declarativeLabel ⟨address ++ [slot], present⟩).atom?] by
        simp [pathLabels, List.inits_append, declarativeLabel_atom]]
      exact AncestorPath.step
        (show tree.HierarchyChild ⟨address, parent⟩ ⟨address ++ [slot], present⟩ from ⟨slot, rfl⟩)
        (ih parent)

theorem ancestorPath_toDeclarativeDigraph (tree : OfficialCIPSourceTree V)
    (node : tree.toDeclarativeDigraph.Node) :
    ancestorPath tree.toDeclarativeDigraph node = some (pathLabels tree node.1) :=
  ancestorPath_eq_some (ancestorPath_rel_toDeclarativeDigraph tree node.1 node.2)
    fun _ hother => ancestorPath_unique_of_addressing tree.declarativeAddressing hother
      (ancestorPath_rel_toDeclarativeDigraph tree node.1 node.2)

theorem mapM_id_map_some {α : Type*} : ∀ values : List α,
    (values.map some).mapM id = some values
  | [] => rfl
  | value :: values => by simp [List.mapM_cons, mapM_id_map_some values]

/-! ### Histories of generated trees -/

omit [DecidableEq V] in
theorem pathLabels_cons (source : OfficialCIPNode V) (children : List (OfficialCIPSourceTree V))
    (slot : ℕ) (address : List ℕ) (child : OfficialCIPSourceTree V)
    (hchild : children[slot]? = some child) :
    pathLabels (.node source children) (slot :: address) =
      source.current? :: pathLabels child address := by
  simp [pathLabels, OfficialCIPSourceTree.sourceAtAddress?,
    OfficialCIPSourceTree.subtreeAt?, hchild, OfficialCIPSourceTree.source]

omit [DecidableEq V] in
theorem subtreeAt?_cons_child {source : OfficialCIPNode V} {children : List (OfficialCIPSourceTree V)}
    {slot : ℕ} {address : List ℕ} {subtree : OfficialCIPSourceTree V}
    (lookup : (OfficialCIPSourceTree.node source children).subtreeAt? (slot :: address) = some subtree) :
    ∃ child, children[slot]? = some child ∧ child.subtreeAt? address = some subtree := by
  unfold OfficialCIPSourceTree.subtreeAt? at lookup
  split at lookup
  · cases lookup
  · exact ⟨_, ‹_›, lookup⟩

/-- In a tree generated by `extend` children, a node's history is the reversed atom path below the
root, followed by the root's history, and every prefix bears an atom. -/
theorem generated_history (enumerate : OfficialCIPNode V → List (OfficialCIPNode V))
    (extended : ∀ node child, child ∈ enumerate node → ∃ next copy, child = node.extend next copy) :
    ∀ (address : List ℕ) (tree subtree : OfficialCIPSourceTree V) (atom : V),
      tree.GeneratedBy enumerate → tree.source.current? = some atom →
        tree.subtreeAt? address = some subtree →
          ∃ rest : List V, pathLabels tree address = (atom :: rest).map some ∧
            subtree.source.history = rest.reverse ++ tree.source.history
  | [], tree, subtree, atom, _, hcurrent, lookup => by
      cases Option.some.inj lookup
      exact ⟨[], by simp [pathLabels, OfficialCIPSourceTree.sourceAtAddress?,
        OfficialCIPSourceTree.subtreeAt?, hcurrent], by simp⟩
  | slot :: address, .node source children, subtree, atom, generated, hcurrent, lookup => by
      obtain ⟨child, hchild, lookup'⟩ := subtreeAt?_cons_child lookup
      rw [OfficialCIPSourceTree.GeneratedBy] at generated
      have hmem : child ∈ children := List.mem_of_getElem? hchild
      obtain ⟨next, copy, hextend⟩ :=
        extended source child.source (generated.1.subset (List.mem_map_of_mem hmem))
      have childGenerated :=
        (OfficialCIPSourceTree.forestGeneratedBy_iff_forall enumerate children).1 generated.2
          child hmem
      have childCurrent : child.source.current? = some next := by rw [hextend]; rfl
      obtain ⟨rest, hpath, hhistory⟩ :=
        generated_history enumerate extended address child subtree next childGenerated
          childCurrent lookup'
      refine ⟨next :: rest, ?_, ?_⟩
      · rw [pathLabels_cons source children slot address child hchild, hpath]
        change source.current? = some atom at hcurrent
        simp [hcurrent]
      · rw [hhistory, hextend]
        simp [OfficialCIPSourceTree.source]

theorem childProvenance_eq_realAtom_iff (node : OfficialCIPNode V) (next : V) (copy : ℕ) :
    node.childProvenance next copy = .realAtom ↔ copy = 0 ∧ next ∉ node.history := by
  unfold OfficialCIPNode.childProvenance
  split_ifs <;> simp_all

theorem isDuplicateLeaf_extend_of_ne (node : OfficialCIPNode V) (next : V) (copy : ℕ)
    (h : (node.extend next copy).provenance ≠ .realAtom) :
    (node.extend next copy).isDuplicateLeaf = true := by
  revert h
  simp only [OfficialCIPNode.extend, OfficialCIPNode.isDuplicateLeaf, OfficialCIPNode.childProvenance]
  split_ifs <;> simp [OfficialCIPNodeProvenance.isDuplicateLeaf]

/-- Real nodes of a generated tree with a simple root history have simple histories. -/
theorem generated_nodup (enumerate : OfficialCIPNode V → List (OfficialCIPNode V))
    (extended : ∀ node child, child ∈ enumerate node → ∃ next copy, child = node.extend next copy)
    (terminal : ∀ node, node.isDuplicateLeaf = true → enumerate node = []) :
    ∀ (address : List ℕ) (tree subtree : OfficialCIPSourceTree V),
      tree.GeneratedBy enumerate → tree.source.history.Nodup →
        tree.subtreeAt? address = some subtree → subtree.source.provenance = .realAtom →
          subtree.source.history.Nodup
  | [], tree, subtree, _, hnodup, lookup, _ => by
      cases Option.some.inj lookup
      exact hnodup
  | slot :: address, .node source children, subtree, generated, hnodup, lookup, hreal => by
      obtain ⟨child, hchild, lookup'⟩ := subtreeAt?_cons_child lookup
      rw [OfficialCIPSourceTree.GeneratedBy] at generated
      have hmem : child ∈ children := List.mem_of_getElem? hchild
      obtain ⟨next, copy, hextend⟩ :=
        extended source child.source (generated.1.subset (List.mem_map_of_mem hmem))
      have childGenerated :=
        (OfficialCIPSourceTree.forestGeneratedBy_iff_forall enumerate children).1 generated.2
          child hmem
      by_cases hchildReal : child.source.provenance = .realAtom
      · have hfresh : next ∉ source.history := by
          rw [hextend] at hchildReal
          exact ((childProvenance_eq_realAtom_iff source next copy).1 hchildReal).2
        have childNodup : child.source.history.Nodup := by
          rw [hextend]
          exact List.nodup_cons.2 ⟨hfresh, hnodup⟩
        exact generated_nodup enumerate extended terminal address child subtree childGenerated
          childNodup lookup' hreal
      · exfalso
        have hleaf : child.source.isDuplicateLeaf = true := by
          rw [hextend] at hchildReal ⊢
          exact isDuplicateLeaf_extend_of_ne source next copy hchildReal
        cases child with
        | node childSource grandchildren =>
            rw [OfficialCIPSourceTree.GeneratedBy] at childGenerated
            have hnil : grandchildren = [] := by
              have := childGenerated.1
              rw [show (OfficialCIPSourceTree.node childSource grandchildren).source = childSource
                from rfl] at hleaf
              rw [terminal childSource hleaf] at this
              simpa using this
            subst hnil
            cases address with
            | nil =>
                cases Option.some.inj lookup'
                exact hchildReal hreal
            | cons _ _ =>
                obtain ⟨_, hnone, _⟩ := subtreeAt?_cons_child lookup'
                simp at hnone

end SourceTree

/-! ### Decorated lookup and erasure -/

section Decorated

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- Decorated lookup commutes with source erasure.  (`LocalizedActualCanonicalConstitutionalRefinement`
proves the same for its own `decoratedSubtreeAt?`; this is the statement for the
`subtreeAt?` lookup used by the realized-tree root and label lemmas.) -/
theorem toOfficialSourceTree_subtreeAt?_eq :
    ∀ (address : List ℕ) (tree : LocalizedCumulativeDecoratedTree input carrierFuel),
      (toOfficialSourceTree tree).subtreeAt? address =
        (subtreeAt? tree address).map toOfficialSourceTree
  | [], tree => by simp [OfficialCIPSourceTree.subtreeAt?]
  | slot :: address, ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ => by
      rw [toOfficialSourceTree_mk, toOfficialSourceTreeList_eq_map, subtreeAt?_cons]
      unfold OfficialCIPSourceTree.subtreeAt?
      rw [List.getElem?_map]
      cases children[slot]? with
      | none => rfl
      | some child => exact toOfficialSourceTree_subtreeAt?_eq address child

theorem incoming_of_subtreeAt? :
    ∀ (address : List ℕ) (tree node : LocalizedCumulativeDecoratedTree input carrierFuel),
      LocalizedCumulativeTreeIncoming input tree → subtreeAt? tree address = some node →
        LocalizedCumulativeTreeIncoming input node
  | [], tree, node, incoming, lookup => by
      cases Option.some.inj lookup
      exact incoming
  | slot :: address, ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩, node,
      incoming, lookup => by
      obtain ⟨child, hchild, lookup'⟩ := subtreeAt?_cons_eq_some_iff.1 lookup
      rw [localizedCumulativeTreeIncoming_mk] at incoming
      exact incoming_of_subtreeAt? address child node
        (localizedCumulativeTreeIncoming_of_mem incoming.2 (List.mem_of_getElem? hchild)) lookup'

theorem address_ne_nil_of_incoming {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (incoming : LocalizedCumulativeTreeIncoming input tree) :
    tree.source.occurrence.1.address ≠ [] := by
  obtain ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ := tree
  rw [localizedCumulativeTreeIncoming_mk] at incoming
  obtain ⟨_, _, _, _, hlength⟩ := incoming.1
  intro hnil
  change source.occurrence.1.address = [] at hnil
  rw [hnil] at hlength
  simp at hlength

end Decorated

/-! ### The actual original-root ligand tree -/

theorem executableOfficialCIPChildren_extend (input : CertifiedLocalizedCIPInput)
    (node child : OfficialCIPNode input.Atom) (present : child ∈ input.executableOfficialCIPChildren node) :
    ∃ next copy, child = node.extend next copy := by
  unfold CertifiedLocalizedCIPInput.executableOfficialCIPChildren at present
  split at present
  · simp at present
  · obtain ⟨copy, _, rfl⟩ := List.mem_map.1 present
    exact ⟨copy.1, copy.2, rfl⟩

theorem executableOfficialCIPChildren_terminal (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (leaf : node.isDuplicateLeaf = true) :
    input.executableOfficialCIPChildren node = [] := by
  unfold CertifiedLocalizedCIPInput.executableOfficialCIPChildren
  rw [if_pos leaf]

theorem provenance_eq_realAtom_of_toDeclarative {provenance : OfficialCIPNodeProvenance}
    (h : provenance.toDeclarative = .realAtom) : provenance = .realAtom := by
  cases provenance with
  | realAtom => rfl
  | multipleBondDuplicate _ => cases h
  | ringDuplicate _ => cases h
  | placeholder kind _ => cases kind <;> cases h

/-- **Whole-tree identification.**  For the actual original-root ligand tree built with the
concrete reader, every node of its declarative digraph, at every depth, is an actual decorated node
whose actual label (the reader value at its actual cursor) is the localized label of the molecular
evidence's reading at that node: the descriptor reading at real atoms, nothing at duplicates.
Every structural premise of the pointwise theorem is derived; the only inputs are the target's
root and empty address. -/
theorem molecularReader_ligandRoot_observations (input : CertifiedLocalizedCIPInput)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (center : input.TetrahedralCenter) (index : Fin 4)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (htargetRoot : target.1.root = center.1) (htargetAddress : target.1.address = [])
    (stage : LocalizedCumulativeRule45Stage) :
    ∃ key : input.LocalizedRerootCumulativeRule45Key,
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
          (input.molecularReader descriptorMap target)
          (2 * (input.certified.input.molecule.atomCount + 1 + 1))
          (input.localizedLigandRootCursor center index) = some key ∧
        ∃ tree : LocalizedCumulativeDecoratedTree input
            (input.certified.input.molecule.atomCount + 1),
          tree.source = input.localizedLigandRootCursor center index ∧
            LocalizedCumulativeTreeTableMatch stage tree key ∧
              LocalizedCumulativeTreeRealizes input (input.molecularReader descriptorMap target) tree ∧
                RootedDigraph.FaithfulExactExpansion input.moleculeGraph center.1
                  (input.canonicalLigandAtom center index)
                  (toOfficialSourceTree tree).toDeclarativeDigraph ∧
                ∀ node : (toOfficialSourceTree tree).toDeclarativeDigraph.Node,
                    ∃ actual, subtreeAt? tree node.1 = some actual ∧
                      actual.label =
                        (occurrenceReading input.moleculeGraph descriptorMap (input.topUnit center)
                          (toOfficialSourceTree tree).toDeclarativeDigraph node).toLocalizedLabel := by
  obtain ⟨key, built, tree, hsource, tables, realizes, generated, treeRoot, faithful⟩ :=
    input.localizedLigandRoot_sourceTree_faithfulExactExpansion center index stage
      (input.molecularReader descriptorMap target)
  refine ⟨key, built, tree, hsource, tables, realizes, faithful, ?_⟩
  have incoming : LocalizedCumulativeTreeIncoming input tree :=
    input.localizedCumulativeTreeIncoming_of_realizes _ tree realizes
      (by rw [hsource]; exact input.localizedLigandRootCursor_incoming center index)
  intro node
  obtain ⟨erased, herased⟩ :=
    OfficialCIPSourceTree.exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses
      (toOfficialSourceTree tree) node.1 node.2
  rw [toOfficialSourceTree_subtreeAt?_eq, Option.map_eq_some_iff] at herased
  obtain ⟨actual, hactual, rfl⟩ := herased
  refine ⟨actual, hactual, ?_⟩
  have hlookup : (toOfficialSourceTree tree).subtreeAt? node.1 = some (toOfficialSourceTree actual) := by
    rw [toOfficialSourceTree_subtreeAt?_eq, hactual]
    rfl
  have hlabel := OfficialCIPSourceTree.declarativeLabel_eq_of_subtreeAt? (toOfficialSourceTree tree) _ node
    hlookup
  have hprovenance : ((toOfficialSourceTree tree).toDeclarativeDigraph.label node).provenance =
      (toOfficialSourceTree actual).source.provenance.toDeclarative := by
    change ((toOfficialSourceTree tree).declarativeLabel node).provenance = _
    rw [hlabel]
    rfl
  by_cases hreal : ((toOfficialSourceTree tree).toDeclarativeDigraph.label node).provenance =
      .realAtom
  swap
  · have hnotReal : actual.source.occurrence.1.node.provenance ≠ .realAtom := by
      intro h
      apply hreal
      rw [hprovenance, toOfficialSourceTree_source, h]
      rfl
    rw [subtreeAt?_node_label_eq_read realizes hactual,
      input.molecularReader_eq_none_of_not_real descriptorMap target actual.source hnotReal]
    unfold occurrenceReading
    split
    · rename_i hmatch _
      exact absurd hmatch hreal
    · rfl
  have hrealSource : (toOfficialSourceTree actual).source.provenance = .realAtom := by
    apply provenance_eq_realAtom_of_toDeclarative
    rw [← hprovenance]
    exact hreal
  have rootCurrent : (toOfficialSourceTree tree).source.current? =
      some (input.canonicalLigandAtom center index) := by rw [treeRoot]; rfl
  obtain ⟨rest, hpath, hhistory⟩ :=
    generated_history input.executableOfficialCIPChildren
      (executableOfficialCIPChildren_extend input) node.1 (toOfficialSourceTree tree) _
      (input.canonicalLigandAtom center index) generated rootCurrent hlookup
  have hligand : input.canonicalLigandAtom center index ≠ center.1 := by
    intro h
    have hadj := input.canonicalLigandAtom_adj center index
    rw [show input.canonicalLigandAtom center index = center.1 from h] at hadj
    simp [MoleculeGraph.Adj, input.moleculeGraph.bond_self] at hadj
  have rootNodup : (toOfficialSourceTree tree).source.history.Nodup := by
    rw [treeRoot]
    simp [OfficialCIPNode.rootFromEdge, hligand]
  have hnodup := generated_nodup input.executableOfficialCIPChildren
    (executableOfficialCIPChildren_extend input) (executableOfficialCIPChildren_terminal input)
    node.1 (toOfficialSourceTree tree) _ generated rootNodup hlookup hrealSource
  have rootHistory : (toOfficialSourceTree tree).source.history =
      [input.canonicalLigandAtom center index, center.1] := by rw [treeRoot]; rfl
  have hcursorHistory : actual.source.occurrence.1.node.history =
      (center.1 :: input.canonicalLigandAtom center index :: rest).reverse := by
    rw [← toOfficialSourceTree_source, hhistory, rootHistory]
    simp
  have hsteps : ancestorAtoms (toOfficialSourceTree tree).toDeclarativeDigraph node =
      some (input.canonicalLigandAtom center index :: rest) := by
    rw [ancestorAtoms, ancestorPath_toDeclarativeDigraph, hpath]
    exact mapM_id_map_some _
  have hroot : actual.source.occurrence.1.root = center.1 := by
    rw [subtreeAt?_source_occurrence_root_eq realizes hactual, hsource]
    rfl
  have haddress : actual.source.occurrence.1.address ≠ [] :=
    address_ne_nil_of_incoming (incoming_of_subtreeAt? node.1 tree actual incoming hactual)
  have hsimple : (center.1 :: input.canonicalLigandAtom center index :: rest).Nodup := by
    rw [← List.nodup_reverse, ← hcursorHistory, ← toOfficialSourceTree_source]
    exact hnodup
  rw [subtreeAt?_node_label_eq_read realizes hactual,
    occurrenceReading_eq_readContext input.moleculeGraph descriptorMap (input.topUnit center) _ hreal
      hsteps]
  exact input.molecularReader_eq_readContext descriptorMap target actual.source (input.topUnit center)
    rfl htargetRoot htargetAddress hroot haddress
    (by rw [← toOfficialSourceTree_source]; exact hrealSource)
    (input.canonicalLigandAtom center index :: rest)
    hcursorHistory hsimple
    (List.cons_ne_nil _ _)

end MolecularEvidenceTree
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.MolecularEvidenceTree.ancestorPath_toDeclarativeDigraph
assert_kernel_only TetraStereo.OneCenter.MolecularEvidenceTree.generated_history
assert_kernel_only TetraStereo.OneCenter.MolecularEvidenceTree.generated_nodup
assert_kernel_only TetraStereo.OneCenter.MolecularEvidenceTree.toOfficialSourceTree_subtreeAt?_eq
assert_kernel_only TetraStereo.OneCenter.MolecularEvidenceTree.molecularReader_ligandRoot_observations
