import TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked
import TetraStereo.OneCenter.LocalizedMarkedGeneratedFactUniqueness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# The actual generated ring facts always pass the duplicate guard

History uniqueness is independent of the raw step, so it applies to the distant-reference
successor as well as the immediate-reference evaluator. The generated state is the actual
recursive state, at any depth and geometry. Ring revisits have different histories.

At the root, temporary-fact insertion therefore always succeeds. The equivalent form of
`Separated` below removes its insertion-success and existential temporary-state premises;
marked key separation and agreement of the priority parity remain open chemical obligations.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneratedFacts
open LocalizedChemicalRingSenseTransport
open LocalizedMarkedOperationEvaluator (Operations underWith tiedChildren)
open LocalizedGenericMarkedRecalculation (Geometry appendFacts?)
open LocalizedMarkedReachedFrameNeighbors (SingleBonded)
open LocalizedMarkedGeneratedFactUniqueness (factOf_key child_atoms_nodup appendFacts_of_nodup)

/-- Every emitted fact retains the suffix of the actual occurrence at which recursion began. -/
theorem history_suffix (step : Step) (mol : RawMolecule) (ops : Operations) (depth : Nat) :
    ∀ geom state ctx node fact, fact ∈ factsWith step mol ops depth geom state ctx node →
      node.history <:+ fact.key.history := by
  induction depth with
  | zero => simp [factsWith]
  | succ depth ih =>
      intro geom state ctx node fact member
      rw [factsWith_succ] at member
      rcases List.mem_append.mp member with own | descendant
      · obtain ⟨descriptor, _, rfl⟩ := List.mem_map.mp own
        simp [factOf_key, canonicalOccurrenceKey]
      · obtain ⟨child, edge, member⟩ := List.mem_flatMap.mp descendant
        have suffix := ih geom state ctx child fact member
        have step : node.history <:+ child.history := by
          rw [mol.canonicalChildren_history node child edge]
          exact List.suffix_cons _ _
        exact step.trans suffix

private theorem child_history_disjoint (step : Step) (mol : RawMolecule) (ops : Operations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat)
    (node left right : Node) (leftEdge : left ∈ mol.canonicalChildren node)
    (rightEdge : right ∈ mol.canonicalChildren node) (different : left.atom ≠ right.atom) :
    List.Disjoint
      ((factsWith step mol ops depth geom state ctx left).map (fun fact => fact.key.history))
      ((factsWith step mol ops depth geom state ctx right).map (fun fact => fact.key.history)) := by
  intro history leftMember rightMember
  obtain ⟨lf, lm, le⟩ := List.mem_map.mp leftMember
  obtain ⟨rf, rm, re⟩ := List.mem_map.mp rightMember
  have ls := history_suffix step mol ops depth geom state ctx left lf lm
  have rs := history_suffix step mol ops depth geom state ctx right rf rm
  rw [le] at ls
  rw [re] at rs
  have length : left.history.length = right.history.length := by
    rw [mol.canonicalChildren_history node left leftEdge,
      mol.canonicalChildren_history node right rightEdge]
    rfl
  have same := (List.suffix_of_suffix_length_le ls rs (Nat.le_of_eq length)).eq_of_length length
  rw [mol.canonicalChildren_history node left leftEdge,
    mol.canonicalChildren_history node right rightEdge] at same
  exact different (List.cons.inj same).1

private theorem forest_histories_nodup (step : Step) (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (children : ∀ child ∈ mol.canonicalChildren node,
      ((factsWith step mol ops depth geom state ctx child).map (fun fact => fact.key.history)).Nodup) :
    (((mol.canonicalChildren node).flatMap (factsWith step mol ops depth geom state ctx)).map
      (fun fact => fact.key.history)).Nodup := by
  rw [List.map_flatMap]
  apply List.nodup_flatMap.mpr
  refine ⟨children, ?_⟩
  have distinct : (mol.canonicalChildren node).Pairwise (fun l r => l.atom ≠ r.atom) := by
    simpa only [List.Nodup, List.pairwise_map] using
      child_atoms_nodup mol wellFormed single unique node
  exact distinct.imp_of_mem fun {l r} lm rm neq =>
    child_history_disjoint step mol ops depth geom state ctx node l r lm rm neq

/-- Generated facts are unique by full history, even before their provenance is inspected. -/
theorem facts_histories_nodup (step : Step) (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) :
    ∀ geom state ctx node,
      ((factsWith step mol ops depth geom state ctx node).map (fun fact => fact.key.history)).Nodup := by
  induction depth with
  | zero => simp [factsWith]
  | succ depth ih =>
      intro geom state ctx node
      have forest := forest_histories_nodup step mol ops wellFormed single unique depth geom state ctx
        node (fun child _ => ih geom state ctx child)
      have absent : node.history ∉
          (((mol.canonicalChildren node).flatMap (factsWith step mol ops depth geom state ctx)).map
            (fun fact => fact.key.history)) := by
        intro member
        obtain ⟨fact, fm, historyEq⟩ := List.mem_map.mp member
        obtain ⟨child, edge, member⟩ := List.mem_flatMap.mp fm
        have bound := (history_suffix step mol ops depth geom state ctx child fact member).length_le
        rw [historyEq, mol.canonicalChildren_history node child edge, List.length_cons] at bound
        omega
      rw [factsWith_succ, List.map_append, List.map_map]
      cases value : descriptorWith step mol ops depth geom state ctx node with
      | none => simpa using forest
      | some descriptor =>
          simpa [factOf_key, canonicalOccurrenceKey] using List.nodup_cons.mpr ⟨absent, forest⟩

theorem facts_keys_nodup (step : Step) (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) :
    ((factsWith step mol ops depth geom state ctx node).map (·.key)).Nodup := by
  apply List.Nodup.of_map CanonicalOccurrenceKey.history
  simpa only [List.map_map, Function.comp_def] using
    facts_histories_nodup step mol ops wellFormed single unique depth geom state ctx node

theorem underWith_keys_nodup (step : Step) (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (mark : Nat) :
    ((underWith mol ops geom state node (factsWith step mol ops depth) mark).map (·.key)).Nodup := by
  have forest := forest_histories_nodup step mol ops wellFormed single unique depth geom state
    (some mark) node (fun child _ =>
      facts_histories_nodup step mol ops wellFormed single unique depth geom state (some mark) child)
  have selected : (tiedChildren mol ops state node).Sublist (mol.canonicalChildren node) := by
    unfold tiedChildren
    split
    · exact List.filter_sublist
    · exact List.nil_sublist _
  have subset := (selected.flatMap (factsWith step mol ops depth geom state (some mark))).map
    (fun fact => fact.key.history)
  apply List.Nodup.of_map CanonicalOccurrenceKey.history
  simpa only [underWith, List.map_map, Function.comp_def] using forest.sublist subset


/-- Duplicate-free insertion for the shared recursion, whatever its raw step computes. -/
theorem extension_succeeds (step : Step) (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (depth : Nat) (geom : Geometry) (node : Node) (mark : Nat) :
    appendFacts? [] (underWith mol ops geom [] node (factsWith step mol ops depth) mark) =
      some (underWith mol ops geom [] node (factsWith step mol ops depth) mark) :=
  appendFacts_of_nodup [] _
    (underWith_keys_nodup step mol ops wellFormed single unique depth geom [] node mark)

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingCompletenessStrict
open LocalizedChemicalRingCompletenessMarked
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center)

include agreement admissible supported single in
theorem generated_extension_succeeds (geom : Geometry) (mark : Nat) :
    appendFacts? [] (generated input mol c geom mark) = some (generated input mol c geom mark) := by
  unfold generated
  rw [facts_eq_factsWith]
  exact extension_succeeds _ mol (sparseOperations input mol) admissible.1.1
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
    admissible.1.2 _ geom _ mark

include agreement admissible supported single in
theorem distant_generated_extension_succeeds (geom : Geometry) (mark : Nat) :
    appendFacts? [] (distantGenerated input mol c geom mark) =
      some (distantGenerated input mol c geom mark) := by
  unfold distantGenerated
  rw [distant_facts_eq_factsWith]
  exact extension_succeeds _ mol (sparseOperations input mol) admissible.1.1
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
    admissible.1.2 _ geom _ mark

/-- The insertion premise and the chosen temporary state are redundant once insertion is derived. -/
theorem separated_iff_of_extension (data : RootData input mol c)
    (under : Nat → OccurrenceAuxState) (h : ℝ)
    (extension : ∀ mark, appendFacts? [] (under mark) = some (under mark)) :
    Separated input mol single c data under h ↔
      ∀ i ∈ tiedLigands input mol single c data,
        Function.Injective (markedKeys input mol single c data
          (under (input.detectedMultiCenterMolecule.ligandAtomAt c i).val)
          (input.detectedMultiCenterMolecule.ligandAtomAt c i)) ∧
        permHandedness (rankPerm input mol c data (markedKeys input mol single c data
          (under (input.detectedMultiCenterMolecule.ligandAtomAt c i).val)
          (input.detectedMultiCenterMolecule.ligandAtomAt c i))) = h := by
  unfold Separated
  constructor
  · intro separated i member
    obtain ⟨temp, inserted, injective, parity⟩ := separated i member
    rw [extension, Option.some.injEq] at inserted
    subst temp
    exact ⟨injective, parity⟩
  · intro separated i member
    exact ⟨_, extension _, separated i member⟩

include agreement admissible supported single in
/-- For the distant-reference evaluator, only injective marked keys and their common parity remain. -/
theorem distant_separated_iff (data : RootData input mol c) (geom : Geometry) (h : ℝ) :
    Separated input mol single c data (distantGenerated input mol c geom) h ↔
      ∀ i ∈ tiedLigands input mol single c data,
        Function.Injective (markedKeys input mol single c data
          (distantGenerated input mol c geom (input.detectedMultiCenterMolecule.ligandAtomAt c i).val)
          (input.detectedMultiCenterMolecule.ligandAtomAt c i)) ∧
        permHandedness (rankPerm input mol c data (markedKeys input mol single c data
          (distantGenerated input mol c geom (input.detectedMultiCenterMolecule.ligandAtomAt c i).val)
          (input.detectedMultiCenterMolecule.ligandAtomAt c i))) = h :=
  separated_iff_of_extension input mol single c data _ h
    (distant_generated_extension_succeeds input mol agreement admissible supported single c geom)

end TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneratedFacts

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneratedFacts.history_suffix
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneratedFacts.facts_keys_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneratedFacts.underWith_keys_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneratedFacts.extension_succeeds
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneratedFacts.generated_extension_succeeds
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneratedFacts.distant_generated_extension_succeeds
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneratedFacts.distant_separated_iff
