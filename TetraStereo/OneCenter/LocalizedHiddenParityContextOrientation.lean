import TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Actual contextual orientation evidence at the hidden-parity cage

This module records the frame-permutation information carried by the already accepted proper and
mirror auxiliary transports. It does not assign ordinary local descriptors or a CIP priority.
-/

namespace TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalInverse
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport
open TetraStereo.OneCenter.LocalizedRuleMajorReference
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open scoped Classical

noncomputable section



abbrev nearAFrame :=
  cyclicContextFrameCompilation decReference simple_bonded nearAOccurrence
    nearAOccurrence_real nearAUnit rfl

abbrev farAFrame :=
  cyclicContextFrameCompilation decReference simple_bonded farAOccurrence
    farAOccurrence_real farAUnit rfl

abbrev nearBFrame :=
  cyclicContextFrameCompilation decReference simple_bonded nearBOccurrence
    nearBOccurrence_real nearBUnit rfl

abbrev farBFrame :=
  cyclicContextFrameCompilation decReference simple_bonded farBOccurrence
    farBOccurrence_real farBUnit rfl

theorem nearAFrame_current : nearAFrame.center.1 = (6 : Fin 21) := by
  have current := nearAOccurrence_current
  have facts := (decReference.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff
    nearAOccurrence nearAFrame.center).mp nearAFrame.centerComputed
  exact Option.some.inj (facts.2.symm.trans current)

theorem farAFrame_current : farAFrame.center.1 = (11 : Fin 21) := by
  have current := farAOccurrence_current
  have facts := (decReference.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff
    farAOccurrence farAFrame.center).mp farAFrame.centerComputed
  exact Option.some.inj (facts.2.symm.trans current)

theorem nearBFrame_current : nearBFrame.center.1 = (15 : Fin 21) := by
  have current := nearBOccurrence_current
  have facts := (decReference.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff
    nearBOccurrence nearBFrame.center).mp nearBFrame.centerComputed
  exact Option.some.inj (facts.2.symm.trans current)

theorem farBFrame_current : farBFrame.center.1 = (20 : Fin 21) := by
  have current := farBOccurrence_current
  have facts := (decReference.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff
    farBOccurrence farBFrame.center).mp farBFrame.centerComputed
  exact Option.some.inj (facts.2.symm.trans current)

/-- Any actual retained-context transport forces the full local ligand-frame action at each fixed
detected center in the deleted-history component to have exactly its requested orientation. This
is the local implication needed at a near bridgehead: a proper transport has even action, and a
mirror transport has odd action. -/
theorem auxiliaryTransport_orientation_at_fixedReachedCenter
    {input : LocalizedRuleMajorReference.Input}
    {target : Occurrence input}
    {unit : DeclarativeCIP.DetectedOccurrence input.certified.moleculeGraph}
    {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
    {frames : ContextFrameCompilation input target unit targetUnit}
    {σ : input.certified.moleculeGraph.Aut}
    {cfg : input.certified.detectedMultiCenterMolecule.Configuration}
    {a b : Fin 4} {mirror : Bool}
    (transport : AuxiliaryBranchTransport frames σ cfg a b mirror)
    (d : input.certified.detectedMultiCenterMolecule.Center)
    (reached : RetainedCoherentSymmetry.InComponent input.certified.moleculeGraph
      target.1.node.history
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation a)) d.1)
    (fixed : input.certified.detectedMultiCenterMolecule.centerPerm
      (input.certified.physicalDetectedAut σ) d = d) :
    permHandedness (input.certified.detectedMultiCenterMolecule.ligandPermAt
      (input.certified.physicalDetectedAut σ) d) = if mirror then -1 else 1 := by
  have law := transport.componentLaw d reached
  rw [fixed] at law
  change permHandedness (cfg d) *
      permHandedness (input.certified.detectedMultiCenterMolecule.ligandPermAt
        (input.certified.physicalDetectedAut σ) d) =
    (if mirror then -1 else 1) * permHandedness (cfg d) at law
  have hs : permHandedness (cfg d) ≠ 0 := by
    intro hz
    have sq := permHandedness_mul_self (cfg d)
    rw [hz] at sq
    norm_num at sq
  cases mirror with
  | false =>
      simp at law
      exact mul_left_cancel₀ hs (by simpa using law)
  | true =>
      simp at law
      have hmul : permHandedness (cfg d) *
          permHandedness (input.certified.detectedMultiCenterMolecule.ligandPermAt
            (input.certified.physicalDetectedAut σ) d) =
          permHandedness (cfg d) * (-1) := by linarith
      exact mul_left_cancel₀ hs hmul

/-- The accepted bridge cycle itself is even as a permutation of the full decorated atom set. -/
theorem nearA_cycle_fullAtomParity : Equiv.Perm.sign cycleAPerm = 1 := by
  have h89 : (8 : Fin 21) ≠ 9 := by decide
  have h910 : (9 : Fin 21) ≠ 10 := by decide
  simp [cycleAPerm, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap h89, Equiv.Perm.sign_swap h910]

/-- The accepted far-A proper witness swaps two bridge atoms and is odd on the full atom set.
This records the concrete odd witness; since its residual detected-center set is empty, it does
not contradict the local orientation theorem above. -/
theorem farA_swap_fullAtomParity :
    Equiv.Perm.sign (otherBridgeSwap 8 : Equiv.Perm (Fin 21)) = -1 := by
  have h : (9 : Fin 21) ≠ 10 := by decide
  simp [LocalizedRecursiveAuxiliaryParityDecoration.otherBridgeSwap,
    Equiv.Perm.sign_swap h]

/-- The corresponding far-B proper witness is odd on the full atom set. -/
theorem farB_swap_fullAtomParity :
    Equiv.Perm.sign (otherBridgeSwap 17 : Equiv.Perm (Fin 21)) = -1 := by
  have h : (18 : Fin 21) ≠ 19 := by decide
  simp [LocalizedRecursiveAuxiliaryParityDecoration.otherBridgeSwap,
    Equiv.Perm.sign_swap h]

private def canonicalAutOfGraphAut (e : graph.Aut) : decCanon.Aut := by
  refine ⟨(e : Equiv.Perm (Fin 21)), ⟨e.property, ?_⟩⟩
  intro c
  change c ∈ graph.tetrahedralCenterSet ↔ (e : Equiv.Perm (Fin 21)) c ∈
    graph.tetrahedralCenterSet
  exact graph.mem_tetrahedralCenterSet_apply_aut_iff e c

/-- Local ligand-action parity is unchanged by the accepted per-center frame reindexing whenever
the automorphism fixes that center. -/
theorem ligandPermAt_sign_reindexFrames_of_fixed
    (m : MultiCenterMolecule (Fin 21))
    (τ : m.Center → Equiv.Perm (Fin 4)) (E : m.Aut) (c : m.Center)
    (fixed : m.centerPerm E c = c) :
    permHandedness ((m.reindexFrames τ).ligandPermAt (m.autReindex τ E) c) =
      permHandedness (m.ligandPermAt E c) := by
  rw [MultiCenterMolecule.reindexFrames_ligandPermAt,
    MultiCenterMolecule.reindexFrames_centerPerm, fixed]
  simp only [permHandedness_mul, permHandedness_inv]
  calc
    permHandedness (τ c) * permHandedness (m.ligandPermAt E c) * permHandedness (τ c) =
        (permHandedness (τ c) * permHandedness (τ c)) *
          permHandedness (m.ligandPermAt E c) := by ring
    _ = permHandedness (m.ligandPermAt E c) := by
      rw [permHandedness_mul_self]
      ring

/-- On the canonical full frames of the near-A cage, every history-fixed graph automorphism has
the same local ligand-permutation parity at the current bridgehead 6 and the remote bridgehead
11. The proof composes with the accepted arm swap and applies `arm_coupled`; parity of the
arm-swap factor cancels. -/
theorem nearA_canonical_current_remote_action
    (σ : graph.Aut)
    (fixRoot : (σ : Equiv.Perm (Fin 21)) 0 = 0)
    (fixIncoming : (σ : Equiv.Perm (Fin 21)) 3 = 3)
    (fixCurrent : (σ : Equiv.Perm (Fin 21)) 6 = 6) :
    decCanon.centerPerm (canonicalAutOfGraphAut σ) k11 = k11 ∧
      permHandedness (decCanon.ligandPermAt (canonicalAutOfGraphAut σ) k6) =
        permHandedness (decCanon.ligandPermAt (canonicalAutOfGraphAut σ) k11) := by
  let G := canonicalAutOfGraphAut σ
  let S := canonicalAutOfGraphAut armSwap
  let T := S * G
  have tRoot : (T : Equiv.Perm (Fin 21)) 0 = 0 := by
    simp [T, S, G, canonicalAutOfGraphAut, fixRoot,
      LocalizedRecursiveAuxiliaryParityDecoration.armSwap,
      LocalizedRecursiveAuxiliaryParityDecoration.armSwapPerm,
      LocalizedRecursiveAuxiliaryParityDecoration.armSwapFun]
  have tIncoming : (T : Equiv.Perm (Fin 21)) 3 = 12 := by
    simp [T, S, G, canonicalAutOfGraphAut, fixIncoming,
      LocalizedRecursiveAuxiliaryParityDecoration.armSwap,
      LocalizedRecursiveAuxiliaryParityDecoration.armSwapPerm,
      LocalizedRecursiveAuxiliaryParityDecoration.armSwapFun]
  have tRootFixed : decCanon.centerPerm T k0 = k0 := by
    apply Subtype.ext
    exact tRoot
  have tRootMoved : decCanon.ligandPermAt T k0 2 = 3 := by
    have action := decCanon.ligandAtomAt_ligandPermAt (e := T) (c := k0) 2
    rw [tRootFixed] at action
    have atomEq : decCanon.ligandAtomAt k0 (decCanon.ligandPermAt T k0 2) =
        decCanon.ligandAtomAt k0 3 := by
      calc
        decCanon.ligandAtomAt k0 (decCanon.ligandPermAt T k0 2) =
            (T : Equiv.Perm (Fin 21)) (decCanon.ligandAtomAt k0 2) := action
        _ = 12 := by rw [lig0f]; exact tIncoming
        _ = decCanon.ligandAtomAt k0 3 := by rw [lig0f]; rfl
    exact (decCanon.ligandAtomAt_injective k0).eq_iff.mp atomEq
  have coupledT := LocalizedRecursiveAuxiliaryParityDecoration.arm_coupled T
    tRootFixed tRootMoved
  have sRoot : decCanon.centerPerm S k0 = k0 := by
    apply Subtype.ext
    change LocalizedRecursiveAuxiliaryParityDecoration.armSwapFun 0 = 0
    decide
  have sRootMoved : decCanon.ligandPermAt S k0 2 = 3 := by
    have action := decCanon.ligandAtomAt_ligandPermAt (e := S) (c := k0) 2
    rw [sRoot] at action
    have sIncoming : (S : Equiv.Perm (Fin 21)) 3 = 12 := by
      change LocalizedRecursiveAuxiliaryParityDecoration.armSwapFun 3 = 12
      decide
    have atomEq : decCanon.ligandAtomAt k0 (decCanon.ligandPermAt S k0 2) =
        decCanon.ligandAtomAt k0 3 := by
      calc
        decCanon.ligandAtomAt k0 (decCanon.ligandPermAt S k0 2) =
            (S : Equiv.Perm (Fin 21)) (decCanon.ligandAtomAt k0 2) := action
        _ = 12 := by rw [lig0f]; exact sIncoming
        _ = decCanon.ligandAtomAt k0 3 := by rw [lig0f]; rfl
    exact (decCanon.ligandAtomAt_injective k0).eq_iff.mp atomEq
  have coupledS := LocalizedRecursiveAuxiliaryParityDecoration.arm_coupled S
    sRoot sRootMoved
  have gCenter6 : decCanon.centerPerm G k6 = k6 := by
    apply Subtype.ext
    exact fixCurrent
  have tCenter11 := coupledT.2.1
  have sCenter11 := coupledS.2.1
  have mulCenters : decCanon.centerPerm (S * G) k11 =
      decCanon.centerPerm S (decCanon.centerPerm G k11) := by
    simpa [MultiCenterMolecule.centerPermHom] using
      congrArg (fun p : Equiv.Perm decCanon.Center => p k11)
        (decCanon.centerPermHom.map_mul S G)
  have gCenter11 : decCanon.centerPerm G k11 = k11 := by
    apply (decCanon.centerPerm S).injective
    calc
      decCanon.centerPerm S (decCanon.centerPerm G k11) =
          decCanon.centerPerm (S * G) k11 := mulCenters.symm
      _ = k20 := tCenter11
      _ = decCanon.centerPerm S k11 := sCenter11.symm
  have mul6 := decCanon.ligandPermAt_mul S G k6
  have mul11 := decCanon.ligandPermAt_mul S G k11
  rw [gCenter6] at mul6
  rw [gCenter11] at mul11
  have signMul6 := congrArg permHandedness mul6
  have signMul11 := congrArg permHandedness mul11
  rw [permHandedness_mul] at signMul6 signMul11
  have parityT : permHandedness (decCanon.ligandPermAt (S * G) k6) =
      permHandedness (decCanon.ligandPermAt (S * G) k11) := by
    simpa [T] using coupledT.2.2
  have parityS := coupledS.2.2
  have signSq := permHandedness_mul_self (decCanon.ligandPermAt S k6)
  have signNe : permHandedness (decCanon.ligandPermAt S k6) ≠ 0 := by
    intro h
    rw [h] at signSq
    norm_num at signSq
  have parityT' :
      permHandedness (decCanon.ligandPermAt S k6) *
          permHandedness (decCanon.ligandPermAt G k6) =
        permHandedness (decCanon.ligandPermAt S k6) *
          permHandedness (decCanon.ligandPermAt G k11) := by
    simpa [signMul6, signMul11, parityS] using parityT
  refine ⟨gCenter11, ?_⟩
  exact mul_left_cancel₀ signNe parityT'

/-- Coupled current/remote action on the B cage. -/
theorem nearB_canonical_current_remote_action
    (σ : graph.Aut)
    (fixRoot : (σ : Equiv.Perm (Fin 21)) 0 = 0)
    (fixIncoming : (σ : Equiv.Perm (Fin 21)) 12 = 12)
    (fixCurrent : (σ : Equiv.Perm (Fin 21)) 15 = 15) :
    decCanon.centerPerm (canonicalAutOfGraphAut σ) k20 = k20 ∧
      permHandedness (decCanon.ligandPermAt (canonicalAutOfGraphAut σ) k15) =
        permHandedness (decCanon.ligandPermAt (canonicalAutOfGraphAut σ) k20) := by
  have _fixed15 := fixCurrent
  let G := canonicalAutOfGraphAut σ
  let S := canonicalAutOfGraphAut armSwap
  let T := G * S
  have tRoot : (T : Equiv.Perm (Fin 21)) 0 = 0 := by
    simp [T, S, G, canonicalAutOfGraphAut, fixRoot,
      LocalizedRecursiveAuxiliaryParityDecoration.armSwap,
      LocalizedRecursiveAuxiliaryParityDecoration.armSwapPerm,
      LocalizedRecursiveAuxiliaryParityDecoration.armSwapFun]
  have tIncoming : (T : Equiv.Perm (Fin 21)) 3 = 12 := by
    simp [T, S, G, canonicalAutOfGraphAut, fixIncoming,
      LocalizedRecursiveAuxiliaryParityDecoration.armSwap,
      LocalizedRecursiveAuxiliaryParityDecoration.armSwapPerm,
      LocalizedRecursiveAuxiliaryParityDecoration.armSwapFun]
  have tRootFixed : decCanon.centerPerm T k0 = k0 := by
    apply Subtype.ext
    exact tRoot
  have tRootMoved : decCanon.ligandPermAt T k0 2 = 3 := by
    have action := decCanon.ligandAtomAt_ligandPermAt (e := T) (c := k0) 2
    rw [tRootFixed] at action
    have atomEq : decCanon.ligandAtomAt k0 (decCanon.ligandPermAt T k0 2) =
        decCanon.ligandAtomAt k0 3 := by
      calc
        decCanon.ligandAtomAt k0 (decCanon.ligandPermAt T k0 2) =
            (T : Equiv.Perm (Fin 21)) (decCanon.ligandAtomAt k0 2) := action
        _ = 12 := by rw [lig0f]; exact tIncoming
        _ = decCanon.ligandAtomAt k0 3 := by rw [lig0f]; rfl
    exact (decCanon.ligandAtomAt_injective k0).eq_iff.mp atomEq
  have coupledT := LocalizedRecursiveAuxiliaryParityDecoration.arm_coupled T
    tRootFixed tRootMoved
  have sRoot : decCanon.centerPerm S k0 = k0 := by
    apply Subtype.ext
    change LocalizedRecursiveAuxiliaryParityDecoration.armSwapFun 0 = 0
    decide
  have sRootMoved : decCanon.ligandPermAt S k0 2 = 3 := by
    have action := decCanon.ligandAtomAt_ligandPermAt (e := S) (c := k0) 2
    rw [sRoot] at action
    have sIncoming : (S : Equiv.Perm (Fin 21)) 3 = 12 := by
      change LocalizedRecursiveAuxiliaryParityDecoration.armSwapFun 3 = 12
      decide
    have atomEq : decCanon.ligandAtomAt k0 (decCanon.ligandPermAt S k0 2) =
        decCanon.ligandAtomAt k0 3 := by
      calc
        decCanon.ligandAtomAt k0 (decCanon.ligandPermAt S k0 2) =
            (S : Equiv.Perm (Fin 21)) (decCanon.ligandAtomAt k0 2) := action
        _ = 12 := by rw [lig0f]; exact sIncoming
        _ = decCanon.ligandAtomAt k0 3 := by rw [lig0f]; rfl
    exact (decCanon.ligandAtomAt_injective k0).eq_iff.mp atomEq
  have coupledS := LocalizedRecursiveAuxiliaryParityDecoration.arm_coupled S
    sRoot sRootMoved
  have gCenter20 : decCanon.centerPerm G k20 = k20 := by
    have comp := congrArg (fun p : Equiv.Perm decCanon.Center => p k11)
      (decCanon.centerPermHom.map_mul G S)
    change decCanon.centerPerm (G * S) k11 =
      decCanon.centerPerm G (decCanon.centerPerm S k11) at comp
    rw [coupledS.2.1] at comp
    exact comp.symm.trans coupledT.2.1
  have m6 := congrArg permHandedness (decCanon.ligandPermAt_mul G S k6)
  have m11 := congrArg permHandedness (decCanon.ligandPermAt_mul G S k11)
  rw [coupledS.1, permHandedness_mul] at m6
  rw [coupledS.2.1, permHandedness_mul] at m11
  have eq := coupledT.2.2
  change permHandedness (decCanon.ligandPermAt (G * S) k6) =
    permHandedness (decCanon.ligandPermAt (G * S) k11) at eq
  rw [m6, m11, coupledS.2.2] at eq
  have nz : permHandedness (decCanon.ligandPermAt S k11) ≠ 0 := by
    intro hz
    have sq := permHandedness_mul_self (decCanon.ligandPermAt S k11)
    rw [hz] at sq
    norm_num at sq
  exact ⟨gCenter20, mul_right_cancel₀ nz eq⟩

/-- The parity projection of `nearA_canonical_current_remote_action`. -/
theorem nearA_canonical_current_remote_parity
    (σ : graph.Aut)
    (fixRoot : (σ : Equiv.Perm (Fin 21)) 0 = 0)
    (fixIncoming : (σ : Equiv.Perm (Fin 21)) 3 = 3)
    (fixCurrent : (σ : Equiv.Perm (Fin 21)) 6 = 6) :
    permHandedness (decCanon.ligandPermAt (canonicalAutOfGraphAut σ) k6) =
      permHandedness (decCanon.ligandPermAt (canonicalAutOfGraphAut σ) k11) :=
  (nearA_canonical_current_remote_action σ fixRoot fixIncoming fixCurrent).2

/-- The arbitrary near-A history-fixed action has equal parity at current and remote bridgeheads
after the accepted source-frame reindexing `decTau`. The equality `decTau_spec` identifies this
reindexed molecule with the accepted detected molecule. -/
theorem nearA_reindexed_current_remote_parity
    (σ : graph.Aut)
    (fixRoot : (σ : Equiv.Perm (Fin 21)) 0 = 0)
    (fixIncoming : (σ : Equiv.Perm (Fin 21)) 3 = 3)
    (fixCurrent : (σ : Equiv.Perm (Fin 21)) 6 = 6) :
    permHandedness ((decCanon.reindexFrames decTau).ligandPermAt
      (decCanon.autReindex decTau (canonicalAutOfGraphAut σ)) k6) =
    permHandedness ((decCanon.reindexFrames decTau).ligandPermAt
      (decCanon.autReindex decTau (canonicalAutOfGraphAut σ)) k11) := by
  let E := canonicalAutOfGraphAut σ
  have fixed6 : decCanon.centerPerm E k6 = k6 := by
    apply Subtype.ext
    exact fixCurrent
  have ⟨fixed11, parity⟩ := nearA_canonical_current_remote_action σ
    fixRoot fixIncoming fixCurrent
  have parity6 := ligandPermAt_sign_reindexFrames_of_fixed decCanon decTau E k6 fixed6
  have parity11 := ligandPermAt_sign_reindexFrames_of_fixed decCanon decTau E k11 fixed11
  simpa [E] using parity6.trans (parity.trans parity11.symm)

/-- The explicit far-A history-fixed bridge swap has odd action on center 11's complete
canonical ligand frame `[7,8,9,10]`. -/
theorem farA_canonical_fullFrame_odd :
    permHandedness (decCanon.ligandPermAt
      (canonicalAutOfGraphAut (otherBridgeSwap 8)) k11) = -1 := by
  have fixed : decCanon.centerPerm (canonicalAutOfGraphAut (otherBridgeSwap 8)) k11 = k11 := by
    apply Subtype.ext
    change (Equiv.swap (9 : Fin 21) 10) 11 = 11
    decide
  have frame : decCanon.ligandPermAt
      (canonicalAutOfGraphAut (otherBridgeSwap 8)) k11 = Equiv.swap 2 3 := by
    ext i
    have action := decCanon.ligandAtomAt_ligandPermAt
      (e := canonicalAutOfGraphAut (otherBridgeSwap 8)) (c := k11) i
    rw [fixed] at action
    rw [lig11f] at action
    have atomEq : decCanon.ligandAtomAt k11
        ((decCanon.ligandPermAt (canonicalAutOfGraphAut (otherBridgeSwap 8)) k11) i) =
        decCanon.ligandAtomAt k11 (Equiv.swap 2 3 i) := by
      rw [lig11f]
      fin_cases i <;> rw [action] <;> decide
    exact congrArg Fin.val ((decCanon.ligandAtomAt_injective k11).eq_iff.mp atomEq)
  rw [frame]
  norm_num [permHandedness, Equiv.Perm.sign_swap (by decide : (2 : Fin 4) ≠ 3)]

/-- The explicit far-B history-fixed bridge swap is odd on center 20's complete canonical
ligand frame `[16,17,18,19]`. -/
theorem farB_canonical_fullFrame_odd :
    permHandedness (decCanon.ligandPermAt
      (canonicalAutOfGraphAut (otherBridgeSwap 17)) k20) = -1 := by
  have fixed : decCanon.centerPerm (canonicalAutOfGraphAut (otherBridgeSwap 17)) k20 = k20 := by
    apply Subtype.ext
    change (Equiv.swap (18 : Fin 21) 19) 20 = 20
    decide
  have frame : decCanon.ligandPermAt
      (canonicalAutOfGraphAut (otherBridgeSwap 17)) k20 = Equiv.swap 2 3 := by
    ext i
    have action := decCanon.ligandAtomAt_ligandPermAt
      (e := canonicalAutOfGraphAut (otherBridgeSwap 17)) (c := k20) i
    rw [fixed] at action
    rw [lig20f] at action
    have atomEq : decCanon.ligandAtomAt k20
        ((decCanon.ligandPermAt (canonicalAutOfGraphAut (otherBridgeSwap 17)) k20) i) =
        decCanon.ligandAtomAt k20 (Equiv.swap 2 3 i) := by
      rw [lig20f]
      fin_cases i <;> rw [action] <;> decide
    exact congrArg Fin.val ((decCanon.ligandAtomAt_injective k20).eq_iff.mp atomEq)
  rw [frame]
  norm_num [permHandedness, Equiv.Perm.sign_swap (by decide : (2 : Fin 4) ≠ 3)]

/-- Far-A's odd local frame action persists under the actual detected-frame reindexing. -/
theorem farA_reindexed_fullFrame_odd :
    permHandedness ((decCanon.reindexFrames decTau).ligandPermAt
      (decCanon.autReindex decTau
        (canonicalAutOfGraphAut (otherBridgeSwap 8))) k11) = -1 := by
  have fixed : decCanon.centerPerm (canonicalAutOfGraphAut (otherBridgeSwap 8)) k11 = k11 := by
    apply Subtype.ext
    change (Equiv.swap (9 : Fin 21) 10) 11 = 11
    decide
  rw [ligandPermAt_sign_reindexFrames_of_fixed decCanon decTau
    (canonicalAutOfGraphAut (otherBridgeSwap 8)) k11 fixed]
  exact farA_canonical_fullFrame_odd

/-- Far-B's odd local frame action persists under the actual detected-frame reindexing. -/
theorem farB_reindexed_fullFrame_odd :
    permHandedness ((decCanon.reindexFrames decTau).ligandPermAt
      (decCanon.autReindex decTau
        (canonicalAutOfGraphAut (otherBridgeSwap 17))) k20) = -1 := by
  have fixed : decCanon.centerPerm (canonicalAutOfGraphAut (otherBridgeSwap 17)) k20 = k20 := by
    apply Subtype.ext
    change (Equiv.swap (18 : Fin 21) 19) 20 = 20
    decide
  rw [ligandPermAt_sign_reindexFrames_of_fixed decCanon decTau
    (canonicalAutOfGraphAut (otherBridgeSwap 17)) k20 fixed]
  exact farB_canonical_fullFrame_odd


private theorem ligandPermAt_eq_of_molecule_eq
    {m n : MultiCenterMolecule (Fin 21)} (h : m = n)
    (E : m.Aut) (F : n.Aut) (c : m.Center) (d : n.Center)
    (autEq : (E : Equiv.Perm (Fin 21)) = (F : Equiv.Perm (Fin 21)))
    (centerEq : c.1 = d.1) : m.ligandPermAt E c = n.ligandPermAt F d := by
  subst n
  have ef : E = F := Subtype.ext autEq
  have cd : c = d := Subtype.ext centerEq
  subst F
  subst d
  rfl

private theorem detectedAction_eq_reindexed (σ : graph.Aut)
    (c : decCanon.Center) (d : decoratedCertified.detectedMultiCenterMolecule.Center)
    (same : c.1 = d.1) :
    decoratedCertified.detectedMultiCenterMolecule.ligandPermAt
      (decoratedCertified.physicalDetectedAut σ) d =
    (decCanon.reindexFrames decTau).ligandPermAt
      (decCanon.autReindex decTau (canonicalAutOfGraphAut σ)) c := by
  exact (ligandPermAt_eq_of_molecule_eq decTau_spec _ _ c d rfl same).symm

private theorem source_ne_fixed_of_distinct
    {target : Occurrence decReference}
    {unit : DeclarativeCIP.DetectedOccurrence graph}
    {unitEq : decReference.certified.molecularFrameUnit target.1 = unit.1}
    (frames : ContextFrameCompilation decReference target unit unitEq)
    {σ : graph.Aut} {cfg : decoratedCertified.detectedMultiCenterMolecule.Configuration}
    {a b : Fin 4} {mirror : Bool}
    (tr : AuxiliaryBranchTransport frames σ cfg a b mirror) (distinct : a ≠ b)
    (x : Fin 21) (fixed : (σ : Equiv.Perm (Fin 21)) x = x) :
    decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt frames.center
      (frames.detectedLigandPermutation a) ≠ x := by
  intro eq
  have sent := tr.ligandSent
  change (σ : Equiv.Perm (Fin 21))
      (decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation a)) =
      decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation b) at sent
  rw [eq, fixed] at sent
  apply distinct
  apply frames.detectedLigandPermutation.injective
  apply decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt_injective frames.center
  exact eq.trans sent

/-- Distinct actual near-A transported slots force the current full frame to have the
requested parity. The incoming slot is excluded by history fixation and injectivity. -/
theorem nearA_actualTransport_orientation
    (σ : graph.Aut) (cfg : decoratedCertified.detectedMultiCenterMolecule.Configuration)
    {a b : Fin 4} {mirror : Bool}
    (tr : AuxiliaryBranchTransport nearAFrame σ cfg a b mirror) (distinct : a ≠ b) :
    permHandedness (decoratedCertified.detectedMultiCenterMolecule.ligandPermAt
      (decoratedCertified.physicalDetectedAut σ) nearAFrame.center) =
        if mirror then -1 else 1 := by
  have fix0 := tr.historyFixed (0 : Fin 21) (by rw [nearAOccurrence_history]; decide)
  have fix3 := tr.historyFixed (3 : Fin 21) (by rw [nearAOccurrence_history]; decide)
  have fix6 := tr.historyFixed (6 : Fin 21) (by rw [nearAOccurrence_history]; decide)
  have coupling := nearA_canonical_current_remote_action σ fix0 fix3 fix6
  have fix11 : (σ : Equiv.Perm (Fin 21)) 11 = 11 :=
    congrArg Subtype.val coupling.1
  let d : decoratedCertified.detectedMultiCenterMolecule.Center := ⟨(11 : Fin 21), by decide⟩
  let s : Fin 21 := decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt
    nearAFrame.center (nearAFrame.detectedLigandPermutation a)
  have ne3 : s ≠ 3 := source_ne_fixed_of_distinct nearAFrame tr distinct 3 fix3
  have adj : graph.Adj 6 s := by
    have h := decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt_adj
      nearAFrame.center (nearAFrame.detectedLigandPermutation a)
    change graph.Adj nearAFrame.center.1 s at h
    rwa [nearAFrame_current] at h
  have finite : ∀ x : Fin 21, graph.Adj 6 x → x ≠ 3 →
      x ∉ ([6,3,0] : List (Fin 21)) ∧ graph.Adj x 11 := by decide
  have hs := finite s adj ne3
  have reached : RetainedCoherentSymmetry.InComponent graph
      nearAOccurrence.1.node.history s d.1 := by
    rw [nearAOccurrence_history]
    exact ⟨hs.1, ⟨SimpleGraph.Walk.cons ⟨hs.1, by decide, hs.2⟩ .nil⟩⟩
  have fixed : decoratedCertified.detectedMultiCenterMolecule.centerPerm
      (decoratedCertified.physicalDetectedAut σ) d = d := Subtype.ext fix11
  have remote := auxiliaryTransport_orientation_at_fixedReachedCenter tr d reached fixed
  rw [detectedAction_eq_reindexed σ k6 nearAFrame.center nearAFrame_current.symm,
    nearA_reindexed_current_remote_parity σ fix0 fix3 fix6]
  rw [detectedAction_eq_reindexed σ k11 d rfl] at remote
  exact remote

/-- Near-B actual distinct transported slots have the requested current-frame parity. -/
theorem nearB_actualTransport_orientation
    (σ : graph.Aut) (cfg : decoratedCertified.detectedMultiCenterMolecule.Configuration)
    {a b : Fin 4} {mirror : Bool}
    (tr : AuxiliaryBranchTransport nearBFrame σ cfg a b mirror) (distinct : a ≠ b) :
    permHandedness (decoratedCertified.detectedMultiCenterMolecule.ligandPermAt
      (decoratedCertified.physicalDetectedAut σ) nearBFrame.center) =
        if mirror then -1 else 1 := by
  have fix0 := tr.historyFixed (0 : Fin 21) (by rw [nearBOccurrence_history]; decide)
  have fix12 := tr.historyFixed (12 : Fin 21) (by rw [nearBOccurrence_history]; decide)
  have fix15 := tr.historyFixed (15 : Fin 21) (by rw [nearBOccurrence_history]; decide)
  have coupling := nearB_canonical_current_remote_action σ fix0 fix12 fix15
  have fix20 : (σ : Equiv.Perm (Fin 21)) 20 = 20 :=
    congrArg Subtype.val coupling.1
  let d : decoratedCertified.detectedMultiCenterMolecule.Center := ⟨(20 : Fin 21), by decide⟩
  let s : Fin 21 := decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt
    nearBFrame.center (nearBFrame.detectedLigandPermutation a)
  have ne12 : s ≠ 12 := source_ne_fixed_of_distinct nearBFrame tr distinct 12 fix12
  have adj : graph.Adj 15 s := by
    have h := decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt_adj
      nearBFrame.center (nearBFrame.detectedLigandPermutation a)
    change graph.Adj nearBFrame.center.1 s at h
    rwa [nearBFrame_current] at h
  have finite : ∀ x : Fin 21, graph.Adj 15 x → x ≠ 12 →
      x ∉ ([15,12,0] : List (Fin 21)) ∧ graph.Adj x 20 := by decide
  have hs := finite s adj ne12
  have reached : RetainedCoherentSymmetry.InComponent graph
      nearBOccurrence.1.node.history s d.1 := by
    rw [nearBOccurrence_history]
    exact ⟨hs.1, ⟨SimpleGraph.Walk.cons ⟨hs.1, by decide, hs.2⟩ .nil⟩⟩
  have fixed : decoratedCertified.detectedMultiCenterMolecule.centerPerm
      (decoratedCertified.physicalDetectedAut σ) d = d := Subtype.ext fix20
  have remote := auxiliaryTransport_orientation_at_fixedReachedCenter tr d reached fixed
  have fixed15 : decCanon.centerPerm (canonicalAutOfGraphAut σ) k15 = k15 :=
    Subtype.ext fix15
  rw [detectedAction_eq_reindexed σ k15 nearBFrame.center nearBFrame_current.symm,
    ligandPermAt_sign_reindexFrames_of_fixed decCanon decTau _ k15 fixed15, coupling.2]
  rw [detectedAction_eq_reindexed σ k20 d rfl,
    ligandPermAt_sign_reindexFrames_of_fixed decCanon decTau _ k20 coupling.1] at remote
  exact remote

private theorem far_explicit_proper
    {target : Occurrence decReference} {unit : DeclarativeCIP.DetectedOccurrence graph}
    {unitEq : decReference.certified.molecularFrameUnit target.1 = unit.1}
    (frames : ContextFrameCompilation decReference target unit unitEq)
    (nonroot : target.1.address ≠ [])
    (σ : graph.Aut) (s t : Fin 21)
    (adjS : graph.Adj frames.center.1 s) (adjT : graph.Adj frames.center.1 t)
    (freshS : s ∉ target.1.node.history) (freshT : t ∉ target.1.node.history)
    (distinct : s ≠ t)
    (fixed : ∀ x ∈ target.1.node.history, (σ : Equiv.Perm (Fin 21)) x = x)
    (sent : (σ : Equiv.Perm (Fin 21)) s = t)
    (isolated : ∀ x, x ∉ target.1.node.history → graph.Adj s x → False)
    (notCenter : s ∉ graph.tetrahedralCenterSet) :
    ∃ a b : Fin 4, a ≠ b ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt a) ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt b) ∧
      AuxiliaryBranchTransport frames σ detectedCfg a b false := by
  obtain ⟨a, ha, oa⟩ := outwardSlot_of_fresh frames nonroot s adjS freshS
  obtain ⟨b, hb, ob⟩ := outwardSlot_of_fresh frames nonroot t adjT freshT
  refine ⟨a, b, ?_, oa, ob, ⟨fixed, ?_, ?_⟩⟩
  · intro eq
    exact distinct (ha.symm.trans ((congrArg (fun k =>
      decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation k)) eq).trans hb))
  · rw [ha, hb]; exact sent
  · intro d component
    rw [ha] at component
    have member := LocalizedRecursiveAuxiliaryPhysicalCompletion.inComponent_closed
      graph target.1.node.history (fun x => x = s)
      (fun x y hx _ hy adj => (isolated y hy (hx ▸ adj)).elim) component rfl
    have center : d.1 ∈ graph.tetrahedralCenterSet := d.2
    exact (notCenter (member ▸ center)).elim

/-- The same explicit bridge swap is a proper actual far-A transport and has odd
current-frame action. The source component is a non-center singleton. -/
theorem farA_actualProper_oddWitness :
    (∃ a b : Fin 4, a ≠ b ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified farAOccurrence
        (farAFrame.frame.cursorAt a) ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified farAOccurrence
        (farAFrame.frame.cursorAt b) ∧
      AuxiliaryBranchTransport farAFrame (otherBridgeSwap 8) detectedCfg a b false) ∧
    permHandedness (decoratedCertified.detectedMultiCenterMolecule.ligandPermAt
      (decoratedCertified.physicalDetectedAut (otherBridgeSwap 8)) farAFrame.center) = -1 := by
  constructor
  · apply far_explicit_proper farAFrame farAOccurrence_nonroot (otherBridgeSwap 8) 9 10
    · rw [farAFrame_current]; decide
    · rw [farAFrame_current]; decide
    · rw [farAOccurrence_history]; decide
    · rw [farAOccurrence_history]; decide
    · decide
    · rw [farAOccurrence_history]; decide
    · decide
    · rw [farAOccurrence_history]; decide
    · decide
  · rw [detectedAction_eq_reindexed (otherBridgeSwap 8) k11 farAFrame.center
      farAFrame_current.symm]
    exact farA_reindexed_fullFrame_odd

/-- Far-B has the analogous explicit odd proper transport on its actual frame. -/
theorem farB_actualProper_oddWitness :
    (∃ a b : Fin 4, a ≠ b ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified farBOccurrence
        (farBFrame.frame.cursorAt a) ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified farBOccurrence
        (farBFrame.frame.cursorAt b) ∧
      AuxiliaryBranchTransport farBFrame (otherBridgeSwap 17) detectedCfg a b false) ∧
    permHandedness (decoratedCertified.detectedMultiCenterMolecule.ligandPermAt
      (decoratedCertified.physicalDetectedAut (otherBridgeSwap 17)) farBFrame.center) = -1 := by
  constructor
  · apply far_explicit_proper farBFrame farBOccurrence_nonroot (otherBridgeSwap 17) 18 19
    · rw [farBFrame_current]; decide
    · rw [farBFrame_current]; decide
    · rw [farBOccurrence_history]; decide
    · rw [farBOccurrence_history]; decide
    · decide
    · rw [farBOccurrence_history]; decide
    · decide
    · rw [farBOccurrence_history]; decide
    · decide
  · rw [detectedAction_eq_reindexed (otherBridgeSwap 17) k20 farBFrame.center
      farBFrame_current.symm]
    exact farB_reindexed_fullFrame_odd

/-- An actual near-A proper transport between distinct slots has even current-frame action. -/
theorem nearA_actualProper_even
    (σ : graph.Aut) (cfg : decoratedCertified.detectedMultiCenterMolecule.Configuration)
    {a b : Fin 4}
    (tr : AuxiliaryBranchTransport nearAFrame σ cfg a b false) (distinct : a ≠ b) :
    permHandedness (decoratedCertified.detectedMultiCenterMolecule.ligandPermAt
      (decoratedCertified.physicalDetectedAut σ) nearAFrame.center) = 1 := by
  simpa using nearA_actualTransport_orientation σ cfg tr distinct


/-- An actual near-A mirror transport between distinct slots has odd current-frame action. -/
theorem nearA_actualMirror_odd
    (σ : graph.Aut) (cfg : decoratedCertified.detectedMultiCenterMolecule.Configuration)
    {a b : Fin 4}
    (tr : AuxiliaryBranchTransport nearAFrame σ cfg a b true) (distinct : a ≠ b) :
    permHandedness (decoratedCertified.detectedMultiCenterMolecule.ligandPermAt
      (decoratedCertified.physicalDetectedAut σ) nearAFrame.center) = -1 := by
  simpa using nearA_actualTransport_orientation σ cfg tr distinct


/-- An actual near-B proper transport between distinct slots has even current-frame action. -/
theorem nearB_actualProper_even
    (σ : graph.Aut) (cfg : decoratedCertified.detectedMultiCenterMolecule.Configuration)
    {a b : Fin 4}
    (tr : AuxiliaryBranchTransport nearBFrame σ cfg a b false) (distinct : a ≠ b) :
    permHandedness (decoratedCertified.detectedMultiCenterMolecule.ligandPermAt
      (decoratedCertified.physicalDetectedAut σ) nearBFrame.center) = 1 := by
  simpa using nearB_actualTransport_orientation σ cfg tr distinct


/-- An actual near-B mirror transport between distinct slots has odd current-frame action. -/
theorem nearB_actualMirror_odd
    (σ : graph.Aut) (cfg : decoratedCertified.detectedMultiCenterMolecule.Configuration)
    {a b : Fin 4}
    (tr : AuxiliaryBranchTransport nearBFrame σ cfg a b true) (distinct : a ≠ b) :
    permHandedness (decoratedCertified.detectedMultiCenterMolecule.ligandPermAt
      (decoratedCertified.physicalDetectedAut σ) nearBFrame.center) = -1 := by
  simpa using nearB_actualTransport_orientation σ cfg tr distinct

end

end TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation

assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.nearAFrame_current
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.farAFrame_current
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.nearBFrame_current
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.farBFrame_current
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.auxiliaryTransport_orientation_at_fixedReachedCenter
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.nearA_cycle_fullAtomParity
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.farA_swap_fullAtomParity
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.farB_swap_fullAtomParity
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.nearA_canonical_current_remote_action
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.nearA_reindexed_current_remote_parity
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.farA_canonical_fullFrame_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.farB_canonical_fullFrame_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.farA_reindexed_fullFrame_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.farB_reindexed_fullFrame_odd

assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.nearA_actualTransport_orientation

assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.farA_actualProper_oddWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.farB_actualProper_oddWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.nearB_canonical_current_remote_action
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.nearB_actualTransport_orientation

assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.nearA_actualProper_even

assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.nearA_actualMirror_odd

assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.nearB_actualProper_even

assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.nearB_actualMirror_odd

assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.nearA_canonical_current_remote_parity

assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityContextOrientation.ligandPermAt_sign_reindexFrames_of_fixed
