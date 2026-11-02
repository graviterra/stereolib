import TetraStereo.OneCenter.DescriptorDiscovery
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace TetraStereo
namespace Examples

open OneCenter

/-!
  A formal pseudoasymmetry benchmark inspired by 2,3,4-trihydroxyglutaric acid.

  The graph is a finite skeletal model of `HOOC-CHOH-CHOH-CHOH-COOH`.  The terminal stereocenters
  are assigned opposite local handedness, and the middle carbon is attached to two enantiomorphic
  ligand paths.  The half-turn symmetry swaps the terminal centers and swaps the two middle ligand
  paths, proving the configuration is achiral while the middle center still receives a lowercase
  pseudoasymmetric descriptor.

  ## Calibration scope

  This fixture is **abstract permutation data**, not a claimed Cartesian realization of the
  molecule.  The source sign calibration (`-1 ↦ r`, `+1 ↦ s`) is applied to the local signs that
  the configuration carries.  In particular, the terminal centers with abstract local signs `+1`
  and `-1` receive `S` and `R` respectively, and the middle center receives `r`.  The middle label
  is `r` for a genuine reason: the source-calibration reversal and the Rule-5 pair reversal cancel.
  It is not obtained by copying the old label, and it must not be flipped to `s`.
-/

namespace PseudoasymmetricTrihydroxyglutaricAcid

inductive Atom where
  | c2
  | c3
  | c4
  | carboxylL
  | carboxylR
  | carboxylLO1
  | carboxylLO2
  | carboxylRO1
  | carboxylRO2
  | o2
  | h2
  | o3
  | h3
  | o4
  | h4
  deriving DecidableEq, Repr, Fintype

open Atom

def centerSet : Finset Atom :=
  {c2, c3, c4}

def atomZ : Atom → AtomicNumber
  | h2 | h3 | h4 => 1
  | o2 | o3 | o4 | carboxylLO1 | carboxylLO2 | carboxylRO1 | carboxylRO2 => 8
  | _ => 6

def bond : Atom → Atom → BondOrder
  | c2, carboxylL => 1
  | carboxylL, c2 => 1
  | carboxylL, carboxylLO1 => 2
  | carboxylLO1, carboxylL => 2
  | carboxylL, carboxylLO2 => 1
  | carboxylLO2, carboxylL => 1
  | c2, c3 => 1
  | c3, c2 => 1
  | c2, o2 => 1
  | o2, c2 => 1
  | c2, h2 => 1
  | h2, c2 => 1
  | c3, c4 => 1
  | c4, c3 => 1
  | c3, o3 => 1
  | o3, c3 => 1
  | c3, h3 => 1
  | h3, c3 => 1
  | c4, carboxylR => 1
  | carboxylR, c4 => 1
  | carboxylR, carboxylRO1 => 2
  | carboxylRO1, carboxylR => 2
  | carboxylR, carboxylRO2 => 1
  | carboxylRO2, carboxylR => 1
  | c4, o4 => 1
  | o4, c4 => 1
  | c4, h4 => 1
  | h4, c4 => 1
  | _, _ => 0

def mol : MoleculeGraph Atom where
  atomZ := atomZ
  bond := bond
  bond_symm := by
    intro u v
    cases u <;> cases v <;> simp [bond]
  bond_self := by
    intro u
    cases u <;> simp [bond]

def ligandAt : ∀ c, c ∈ centerSet → Fin 4 → Atom := by
  intro c hc i
  cases c <;> try simp [centerSet] at hc
  · exact ![o2, carboxylL, c3, h2] i
  · exact ![o3, c2, c4, h3] i
  · exact ![o4, carboxylR, c3, h4] i

def multi : MultiCenterMolecule Atom where
  mol := mol
  centers := centerSet
  ligandAtom := ligandAt
  ligandAtom_adj := by
    intro c hc i
    cases c <;> try simp [centerSet] at hc
    · fin_cases i <;> simp [ligandAt, MoleculeGraph.Adj, mol, bond]
    · fin_cases i <;> simp [ligandAt, MoleculeGraph.Adj, mol, bond]
    · fin_cases i <;> simp [ligandAt, MoleculeGraph.Adj, mol, bond]
  ligandAtom_injective := by
    intro c hc i j hij
    cases c <;> try simp [centerSet] at hc
    · fin_cases i <;> fin_cases j <;> simp [ligandAt] at hij ⊢
    · fin_cases i <;> fin_cases j <;> simp [ligandAt] at hij ⊢
    · fin_cases i <;> fin_cases j <;> simp [ligandAt] at hij ⊢
  ligandAtom_surjective := by
    intro c hc v hv
    cases c <;> try simp [centerSet] at hc
    · cases v <;> simp [ligandAt, MoleculeGraph.Adj, mol, bond] at hv ⊢
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨3, rfl⟩
    · cases v <;> simp [ligandAt, MoleculeGraph.Adj, mol, bond] at hv ⊢
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨3, rfl⟩
    · cases v <;> simp [ligandAt, MoleculeGraph.Adj, mol, bond] at hv ⊢
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨3, rfl⟩

def leftCenter : multi.Center :=
  ⟨c2, by simp [multi, centerSet]⟩

def middleCenter : multi.Center :=
  ⟨c3, by simp [multi, centerSet]⟩

def rightCenter : multi.Center :=
  ⟨c4, by simp [multi, centerSet]⟩

def flip : Atom → Atom
  | c2 => c4
  | c4 => c2
  | carboxylL => carboxylR
  | carboxylR => carboxylL
  | carboxylLO1 => carboxylRO1
  | carboxylRO1 => carboxylLO1
  | carboxylLO2 => carboxylRO2
  | carboxylRO2 => carboxylLO2
  | o2 => o4
  | o4 => o2
  | h2 => h4
  | h4 => h2
  | x => x

theorem flip_involutive : Function.Involutive flip := by
  intro x
  cases x <;> simp [flip]

def flipPerm : Equiv.Perm Atom :=
  { toFun := flip
    invFun := flip
    left_inv := by
      intro x
      simpa using flip_involutive x
    right_inv := by
      intro x
      simpa using flip_involutive x }

theorem flipPerm_mem_molAut : flipPerm ∈ multi.mol.Aut := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    cases v <;> simp [multi, mol, atomZ, flipPerm, flip]
  · intro v
    cases v <;> simp [multi, mol, flipPerm, flip]
  · intro v
    rfl
  · intro u v
    cases u <;> cases v <;> simp [multi, mol, bond, flipPerm, flip]

theorem flipPerm_preservesCenters : multi.PreservesCenters flipPerm := by
  intro c
  cases c <;> simp [multi, centerSet, flipPerm, flip]

def flipAut : multi.Aut :=
  ⟨flipPerm, ⟨flipPerm_mem_molAut, flipPerm_preservesCenters⟩⟩

theorem ligandPermAt_flipAut_left : multi.ligandPermAt flipAut leftCenter = 1 := by
  classical
  ext i
  have hi : multi.ligandPermAt flipAut leftCenter i = i := by
    apply multi.ligandAtomAt_injective (multi.centerPerm flipAut leftCenter)
    have hAtom := multi.ligandAtomAt_ligandPermAt (e := flipAut) (c := leftCenter) i
    calc
      multi.ligandAtomAt (multi.centerPerm flipAut leftCenter)
          (multi.ligandPermAt flipAut leftCenter i)
          = (flipAut : Equiv.Perm Atom) (multi.ligandAtomAt leftCenter i) := hAtom
      _ = multi.ligandAtomAt (multi.centerPerm flipAut leftCenter) i := by
            fin_cases i <;>
              simp [leftCenter, multi, MultiCenterMolecule.ligandAtomAt, ligandAt,
                flipAut, flipPerm, flip,
                MultiCenterMolecule.centerPerm]
  simpa using congrArg Fin.val hi

theorem ligandPermAt_flipAut_right : multi.ligandPermAt flipAut rightCenter = 1 := by
  classical
  ext i
  have hi : multi.ligandPermAt flipAut rightCenter i = i := by
    apply multi.ligandAtomAt_injective (multi.centerPerm flipAut rightCenter)
    have hAtom := multi.ligandAtomAt_ligandPermAt (e := flipAut) (c := rightCenter) i
    calc
      multi.ligandAtomAt (multi.centerPerm flipAut rightCenter)
          (multi.ligandPermAt flipAut rightCenter i)
          = (flipAut : Equiv.Perm Atom) (multi.ligandAtomAt rightCenter i) := hAtom
      _ = multi.ligandAtomAt (multi.centerPerm flipAut rightCenter) i := by
            fin_cases i <;>
              simp [rightCenter, multi, MultiCenterMolecule.ligandAtomAt, ligandAt,
                flipAut, flipPerm, flip,
                MultiCenterMolecule.centerPerm]
  simpa using congrArg Fin.val hi

theorem ligandPermAt_flipAut_middle :
    multi.ligandPermAt flipAut middleCenter = Equiv.swap (1 : Fin 4) 2 := by
  classical
  ext i
  have hi :
      multi.ligandPermAt flipAut middleCenter i = (Equiv.swap (1 : Fin 4) 2) i := by
    apply multi.ligandAtomAt_injective (multi.centerPerm flipAut middleCenter)
    have hAtom := multi.ligandAtomAt_ligandPermAt (e := flipAut) (c := middleCenter) i
    calc
      multi.ligandAtomAt (multi.centerPerm flipAut middleCenter)
          (multi.ligandPermAt flipAut middleCenter i)
          = (flipAut : Equiv.Perm Atom) (multi.ligandAtomAt middleCenter i) := hAtom
      _ = multi.ligandAtomAt (multi.centerPerm flipAut middleCenter)
            ((Equiv.swap (1 : Fin 4) 2) i) := by
            fin_cases i <;>
              simp [middleCenter, multi, MultiCenterMolecule.ligandAtomAt, ligandAt,
                flipAut, flipPerm, flip, Equiv.swap_apply_of_ne_of_ne,
                MultiCenterMolecule.centerPerm]
  simpa using congrArg Fin.val hi

theorem permHandedness_ligandPermAt_flipAut_middle :
    permHandedness (multi.ligandPermAt flipAut middleCenter) = -1 := by
  have hswap : permHandedness (Equiv.swap (1 : Fin 4) 2) = -1 := by
    norm_num [permHandedness, Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 2)]
  simpa [ligandPermAt_flipAut_middle] using hswap

private theorem centerPerm_flipAut_middle :
    multi.centerPerm flipAut middleCenter = middleCenter := by
  apply Subtype.ext
  simp [middleCenter, multi, flipAut, flipPerm, flip, MultiCenterMolecule.centerPerm]

/-- The two side ligand paths at the middle center have identical ordinary descriptor keys.  The
graph symmetry swaps them, so any final ordering must come from a descriptor-dependent rule. -/
theorem middle_side_descriptor_keys_eq :
    multi.cipKeyDescriptorAt middleCenter (1 : Fin 4) =
      multi.cipKeyDescriptorAt middleCenter (2 : Fin 4) := by
  have h := multi.cipKeyCycleCutAt_eq_cipKeyCycleCutAt_ligandPermAt
    (e := flipAut) (c := middleCenter) (i := (1 : Fin 4))
  simpa [MultiCenterMolecule.cipKeyDescriptorAt, centerPerm_flipAut_middle,
    ligandPermAt_flipAut_middle] using h.symm

/-- Ordinary graph/key comparison ties on the two middle side paths before Rule 5 is invoked. -/
theorem middle_side_key_trace_tied :
    cipTraceOutcome
      (CIPRuleEngine.compareKeyTrace
        (multi.cipKeyDescriptorAt middleCenter (1 : Fin 4))
        (multi.cipKeyDescriptorAt middleCenter (2 : Fin 4))) = Ordering.eq :=
  CIPRuleEngine.compareKeyTrace_outcome_eq_of_eq middle_side_descriptor_keys_eq

def cfg : multi.Configuration :=
  fun c =>
    match c.1 with
    | c4 => MultiCenterMolecule.mirrorFrame
    | _ => 1

@[simp] theorem cfg_sign_left : multi.configurationSign cfg leftCenter = 1 := by
  simp [MultiCenterMolecule.configurationSign, cfg, leftCenter]

@[simp] theorem cfg_sign_middle : multi.configurationSign cfg middleCenter = 1 := by
  simp [MultiCenterMolecule.configurationSign, cfg, middleCenter]

@[simp] theorem cfg_sign_right : multi.configurationSign cfg rightCenter = -1 := by
  simp [MultiCenterMolecule.configurationSign, cfg, rightCenter,
    MultiCenterMolecule.mirrorFrame]

/-- With the corrected source calibration (`-1 ↦ R`, `+1 ↦ S`) the terminal centers are `S` and
`R`.  This is the first half of the cancellation that keeps the middle label at `r`. -/
theorem terminal_descriptors_are_enantiomorphic :
    multi.configurationRS cfg leftCenter = RS.S ∧
      multi.configurationRS cfg rightCenter = RS.R := by
  constructor
  · show RS.ofHandedness (multi.configurationSign cfg leftCenter) = RS.S
    rw [cfg_sign_left]
    exact RS.ofHandedness_one
  · show RS.ofHandedness (multi.configurationSign cfg rightCenter) = RS.R
    rw [cfg_sign_right]
    exact RS.ofHandedness_neg_one

/-- The initial global descriptor-discovery state seeds the terminal `S/R` descriptors from the
configuration and has no lowercase pseudoasymmetric descriptors yet. -/
noncomputable def initialDescriptorState : DescriptorDiscoveryState multi cfg :=
  DescriptorDiscoveryState.seedConfigurationRS multi cfg

@[simp] theorem initialDescriptorState_rs_left :
    initialDescriptorState.rs leftCenter = some RS.S := by
  simp [initialDescriptorState, DescriptorDiscoveryState.seedConfigurationRS,
    terminal_descriptors_are_enantiomorphic.1]

@[simp] theorem initialDescriptorState_rs_right :
    initialDescriptorState.rs rightCenter = some RS.R := by
  simp [initialDescriptorState, DescriptorDiscoveryState.seedConfigurationRS,
    terminal_descriptors_are_enantiomorphic.2]



def middleRule5DiscoveryTask : Rule5DiscoveryTask multi cfg where
  center := middleCenter
  leftLigand := 1
  rightLigand := 2
  leftSource := leftCenter
  rightSource := rightCenter
  keyTie := middle_side_key_trace_tied

/-- The safe descriptor-CIP seed state: centers are seeded only if their descriptor-facing local CIP
priorities are resolved. -/
noncomputable def safeDescriptorSeedState : DescriptorDiscoveryState multi cfg :=
  DescriptorDiscoveryState.seedResolvedDescriptorRS? multi cfg

theorem middleRule5DiscoveryTask_ready_initial :
    middleRule5DiscoveryTask.Ready initialDescriptorState := by
  constructor
  · exact ⟨RS.S, initialDescriptorState_rs_left⟩
  · exact ⟨RS.R, initialDescriptorState_rs_right⟩



theorem middleRule5DiscoveryTask_ready_safeDescriptorSeed_of_terminal_resolved
    (hleft : multi.ResolvedCIPDescriptorAt leftCenter)
    (hright : multi.ResolvedCIPDescriptorAt rightCenter) :
    middleRule5DiscoveryTask.Ready safeDescriptorSeedState := by
  simpa [safeDescriptorSeedState, middleRule5DiscoveryTask] using
    Rule5DiscoveryTask.ready_seedResolvedDescriptorRS?_of_resolved_sources
      (task := middleRule5DiscoveryTask) hleft hright

theorem middleRule5DiscoveryTask_resolvesFromSafeDescriptorSeed_of_terminal_resolved
    (hleft : multi.ResolvedCIPDescriptorAt leftCenter)
    (hright : multi.ResolvedCIPDescriptorAt rightCenter)
    (hne : multi.cipConfigurationRSDescriptor cfg leftCenter ≠
      multi.cipConfigurationRSDescriptor cfg rightCenter) :
    middleRule5DiscoveryTask.resolveFromState? safeDescriptorSeedState =
      some
        (middleRule5DiscoveryTask.resolve
          (multi.cipConfigurationRSDescriptor cfg leftCenter)
          (multi.cipConfigurationRSDescriptor cfg rightCenter)) := by
  simpa [safeDescriptorSeedState, middleRule5DiscoveryTask] using
    Rule5DiscoveryTask.resolveFromState?_seedResolvedDescriptorRS?_eq_some
      (task := middleRule5DiscoveryTask) hleft hright hne

noncomputable def middleDiscoveryResult : Rule5DiscoveryTask.Result middleRule5DiscoveryTask :=
  middleRule5DiscoveryTask.resolve RS.S RS.R

/-- The guarded resolver still resolves the actual initial fixture to the actual legacy result:
the two seeded terminal labels are distinct, so the equal-pair refusal does not fire.  The proof is
stated through the result's own source fields so it follows any relabelling of the terminal
calibration. -/
theorem middleRule5DiscoveryTask_resolveFromInitial :
    middleRule5DiscoveryTask.resolveFromState? initialDescriptorState =
      some middleDiscoveryResult := by
  have hleft :
      initialDescriptorState.rs middleRule5DiscoveryTask.leftSource =
        some middleDiscoveryResult.leftDescriptor := by
    simp [middleDiscoveryResult, middleRule5DiscoveryTask, Rule5DiscoveryTask.resolve,
      initialDescriptorState_rs_left]
  have hright :
      initialDescriptorState.rs middleRule5DiscoveryTask.rightSource =
        some middleDiscoveryResult.rightDescriptor := by
    simp [middleDiscoveryResult, middleRule5DiscoveryTask, Rule5DiscoveryTask.resolve,
      initialDescriptorState_rs_right]
  have hne : middleDiscoveryResult.leftDescriptor ≠ middleDiscoveryResult.rightDescriptor := by
    simp [middleDiscoveryResult, middleRule5DiscoveryTask, Rule5DiscoveryTask.resolve]
  simpa [middleDiscoveryResult, Rule5DiscoveryTask.resolve] using
    Rule5DiscoveryTask.resolveFromState?_eq_some_of_rs_sources_ne
      (task := middleRule5DiscoveryTask) (state := initialDescriptorState)
      (leftDescriptor := middleDiscoveryResult.leftDescriptor)
      (rightDescriptor := middleDiscoveryResult.rightDescriptor) hleft hright hne

/-- One global discovery step after the terminal descriptors are known. -/
noncomputable def afterMiddleDiscoveryState : DescriptorDiscoveryState multi cfg :=
  initialDescriptorState.applyRule5Task middleRule5DiscoveryTask

/-- The Rule-5 trace engine decides the enantiomorphic ligand-pair ordering used at the middle
center: the right `R` path outranks the left `S` path (`S` before `R` has negative orientation).
This is the second half of the cancellation that keeps the middle label at `r`. -/
theorem middle_rule5PairTrace_outcome :
    (rule5PairTraceCertificate
      (multi.configurationRS cfg leftCenter)
      (multi.configurationRS cfg rightCenter)).outcome = Ordering.lt := by
  simp [terminal_descriptors_are_enantiomorphic.1, terminal_descriptors_are_enantiomorphic.2,
    rule5PairTraceCertificate_S_R_outcome]

/-- The middle-center descriptor-dependent engine: ordinary side-path keys tie, so the engine
falls through to Rule 5 using the terminal `S/R` descriptors. -/
noncomputable def middlePseudoDescriptorEngine : CIPRuleEngine.Rule5PseudoDescriptorEngineResult :=
  middleDiscoveryResult.engine

theorem middle_engine_comparison_outcome :
    middlePseudoDescriptorEngine.comparison.outcome = Ordering.lt := by
  simpa [middlePseudoDescriptorEngine, middleDiscoveryResult, middleRule5DiscoveryTask,
    Rule5DiscoveryTask.resolve, MultiCenterMolecule.rule5PseudoDescriptorEngineAt] using
    CIPRuleEngine.rule5PseudoDescriptorEngineFromKeys_comparison_outcome_S_R_of_key_eq
      (centerSign := multi.configurationSign cfg middleCenter) middle_side_key_trace_tied

/-- The corrected source calibration maps the combined sign `(+1) * (-1) = -1` to `r`.  The sign
reversal from `R/S → S/R` and the calibration reversal cancel exactly. -/
theorem middle_engine_descriptor_eq_r :
    middlePseudoDescriptorEngine.descriptor = PseudoRS.r := by
  simpa [middlePseudoDescriptorEngine, middleDiscoveryResult, middleRule5DiscoveryTask,
    Rule5DiscoveryTask.resolve, MultiCenterMolecule.rule5PseudoDescriptorEngineAt] using
    CIPRuleEngine.rule5PseudoDescriptorEngineFromKeys_one_S_R_descriptor_eq_r_of_key_eq
      middle_side_key_trace_tied

theorem middleDiscoveryResult_descriptor_eq_r :
    middleDiscoveryResult.descriptor = PseudoRS.r := by
  simpa [middlePseudoDescriptorEngine] using middle_engine_descriptor_eq_r

theorem afterMiddleDiscoveryState_middle_pseudo_eq_some_r :
    afterMiddleDiscoveryState.pseudo middleCenter = some PseudoRS.r := by
  have h :=
    DescriptorDiscoveryState.applyRule5Task_pseudo_eq_some_of_resolveFromState?_eq_some
      (state := initialDescriptorState) (task := middleRule5DiscoveryTask)
      (result := middleDiscoveryResult) middleRule5DiscoveryTask_resolveFromInitial
  simpa [afterMiddleDiscoveryState, middleDiscoveryResult_descriptor_eq_r] using h

private theorem preimage_flip_left :
    ((multi.centerPerm flipAut)⁻¹ leftCenter) = rightCenter := by
  apply Subtype.ext
  simp [leftCenter, rightCenter, multi, flipAut, flipPerm, flip,
    MultiCenterMolecule.centerPerm]

private theorem preimage_flip_middle :
    ((multi.centerPerm flipAut)⁻¹ middleCenter) = middleCenter := by
  apply Subtype.ext
  simp [middleCenter, multi, flipAut, flipPerm, flip, MultiCenterMolecule.centerPerm]

private theorem preimage_flip_right :
    ((multi.centerPerm flipAut)⁻¹ rightCenter) = leftCenter := by
  apply Subtype.ext
  simp [leftCenter, rightCenter, multi, flipAut, flipPerm, flip,
    MultiCenterMolecule.centerPerm]

private theorem achiral_at_left :
    multi.configurationSign (flipAut • cfg) leftCenter =
      multi.configurationSign (multi.mirrorConfiguration cfg) leftCenter := by
  calc
    multi.configurationSign (flipAut • cfg) leftCenter
        = multi.configurationSign cfg ((multi.centerPerm flipAut)⁻¹ leftCenter) *
            permHandedness (multi.ligandPermAt flipAut
              ((multi.centerPerm flipAut)⁻¹ leftCenter)) := by
            exact multi.configurationSign_smul (e := flipAut) (cfg := cfg) leftCenter
    _ = -1 := by simp [preimage_flip_left, ligandPermAt_flipAut_right]
    _ = multi.configurationSign (multi.mirrorConfiguration cfg) leftCenter := by
          simp [MultiCenterMolecule.configurationSign_mirrorConfiguration]

private theorem achiral_at_middle :
    multi.configurationSign (flipAut • cfg) middleCenter =
      multi.configurationSign (multi.mirrorConfiguration cfg) middleCenter := by
  calc
    multi.configurationSign (flipAut • cfg) middleCenter
        = multi.configurationSign cfg ((multi.centerPerm flipAut)⁻¹ middleCenter) *
            permHandedness (multi.ligandPermAt flipAut
              ((multi.centerPerm flipAut)⁻¹ middleCenter)) := by
            exact multi.configurationSign_smul (e := flipAut) (cfg := cfg) middleCenter
    _ = -1 := by simp [preimage_flip_middle, permHandedness_ligandPermAt_flipAut_middle]
    _ = multi.configurationSign (multi.mirrorConfiguration cfg) middleCenter := by
          simp [MultiCenterMolecule.configurationSign_mirrorConfiguration]

private theorem achiral_at_right :
    multi.configurationSign (flipAut • cfg) rightCenter =
      multi.configurationSign (multi.mirrorConfiguration cfg) rightCenter := by
  calc
    multi.configurationSign (flipAut • cfg) rightCenter
        = multi.configurationSign cfg ((multi.centerPerm flipAut)⁻¹ rightCenter) *
            permHandedness (multi.ligandPermAt flipAut
              ((multi.centerPerm flipAut)⁻¹ rightCenter)) := by
            exact multi.configurationSign_smul (e := flipAut) (cfg := cfg) rightCenter
    _ = 1 := by simp [preimage_flip_right, ligandPermAt_flipAut_left]
    _ = multi.configurationSign (multi.mirrorConfiguration cfg) rightCenter := by
          simp [MultiCenterMolecule.configurationSign_mirrorConfiguration]

/-- The opposite terminal configurations plus the middle ligand swap make the full configuration
symmetry-equivalent to its mirror. -/
theorem achiralConfigurationBySymmetry : multi.AchiralConfigurationBySymmetry cfg := by
  refine ⟨flipAut, ?_⟩
  funext c
  cases c with
  | mk a ha =>
      cases a <;> simp [multi, centerSet] at ha
      · simpa [leftCenter] using achiral_at_left
      · simpa [middleCenter] using achiral_at_middle
      · simpa [rightCenter] using achiral_at_right

/-- The middle carbon has lowercase `r`: the local central sign is positive and Rule 5 gives the
enantiomorphic `S,R` pair negative orientation, so the combined source sign is `-1`.  Before the
source calibration this same abstract data produced `r` through the opposite pair of conventions;
both conventions were wrong, and the two errors cancel. -/
theorem middle_pseudoDescriptor_eq_r :
    pseudoDescriptor (multi.configurationSign cfg middleCenter)
      (multi.configurationRS cfg leftCenter) (multi.configurationRS cfg rightCenter) =
        PseudoRS.r := by
  have hengine :
      middlePseudoDescriptorEngine.descriptor =
        pseudoDescriptor (multi.configurationSign cfg middleCenter)
          (multi.configurationRS cfg leftCenter) (multi.configurationRS cfg rightCenter) := by
    simpa [middlePseudoDescriptorEngine, middleDiscoveryResult, middleRule5DiscoveryTask,
      Rule5DiscoveryTask.resolve, MultiCenterMolecule.rule5PseudoDescriptorEngineAt,
      terminal_descriptors_are_enantiomorphic.1, terminal_descriptors_are_enantiomorphic.2] using
      CIPRuleEngine.rule5PseudoDescriptorEngineFromKeys_descriptor_eq_pseudoDescriptor_of_key_eq
        (multi.configurationSign cfg middleCenter)
        (multi.configurationRS cfg leftCenter)
        (multi.configurationRS cfg rightCenter)
        middle_side_key_trace_tied
  rw [← hengine]
  exact middle_engine_descriptor_eq_r

/-- The mirror calculation preserves the lowercase descriptor: central handedness changes sign,
but the enantiomorphic ligand labels swap too. -/
theorem middle_pseudoDescriptor_mirror_invariant :
    pseudoDescriptor (-(multi.configurationSign cfg middleCenter))
      (RS.swap (multi.configurationRS cfg leftCenter))
      (RS.swap (multi.configurationRS cfg rightCenter)) =
        pseudoDescriptor (multi.configurationSign cfg middleCenter)
          (multi.configurationRS cfg leftCenter) (multi.configurationRS cfg rightCenter) := by
  exact pseudoDescriptor_mirror _ _ _

/-- A compact proof object packaging the pseudoasymmetric and achiral facts. -/
def middlePseudoasymmetricCertificate :
    PseudoasymmetricRule5Certificate multi cfg where
  center := middleCenter
  centerSign := 1
  centerSign_normalized := Or.inr rfl
  leftDescriptor := RS.S
  rightDescriptor := RS.R
  centerSign_eq := by simp
  enantiomorphic := rfl
  descriptor := PseudoRS.r
  descriptor_eq := by
    simp [pseudoDescriptor, pseudoasymmetricSign]
  achiral := achiralConfigurationBySymmetry

/-- The stronger engine-backed certificate: the ordinary middle side-path keys tie, the engine
invokes Rule 5 automatically, and the resulting lowercase descriptor is `r` in an achiral
configuration. -/
def middleRule5EngineCertificate :
    Rule5PseudoasymmetricEngineCertificate multi cfg where
  center := middleCenter
  leftLigand := 1
  rightLigand := 2
  leftDescriptor := RS.S
  rightDescriptor := RS.R
  keyTie := middle_side_key_trace_tied
  descriptor := PseudoRS.r
  descriptor_eq := by
    simpa [middlePseudoDescriptorEngine, middleDiscoveryResult, middleRule5DiscoveryTask,
      Rule5DiscoveryTask.resolve, MultiCenterMolecule.rule5PseudoDescriptorEngineAt,
      terminal_descriptors_are_enantiomorphic.1, terminal_descriptors_are_enantiomorphic.2] using
      middle_engine_descriptor_eq_r.symm
  achiral := achiralConfigurationBySymmetry




noncomputable def middleGlobalDiscoveryCertificate :
    Rule5GlobalDiscoveryCertificate multi cfg where
  initial := initialDescriptorState
  task := middleRule5DiscoveryTask
  result := middleDiscoveryResult
  resolved_from_initial := middleRule5DiscoveryTask_resolveFromInitial
  finalState := afterMiddleDiscoveryState
  finalState_eq := rfl
  final_pseudo := by
    simpa [middleRule5DiscoveryTask, middleDiscoveryResult_descriptor_eq_r] using
      afterMiddleDiscoveryState_middle_pseudo_eq_some_r
  achiral := achiralConfigurationBySymmetry

end PseudoasymmetricTrihydroxyglutaricAcid

end Examples
end TetraStereo
