import TetraStereo.OneCenter.DeclarativeCIPOrdinaryCanonicalAddressing
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP
namespace OrdinaryCanonicalAddressingKernelCertificate

open RootedDigraph

/-! ## Constitutionally tied siblings with different Rule-3 evidence

A root has two leaf children labelled by the same atom at the same depth.  Only `marked` carries a
Rule-3 observation.  Both sibling orders are canonical for the three-rule family, yet they give
opposite Rule-3 outcomes; the ordinary family admits only the order listing `marked` first. -/

inductive TwinNode where
  | root
  | marked
  | plain
  deriving DecidableEq

instance : Fintype TwinNode :=
  ⟨{.root, .marked, .plain}, by intro node; cases node <;> simp⟩

def twinMolecule : MoleculeGraph (Fin 2) where
  atomZ := fun _ => 6
  bond := fun _ _ => 0
  bond_symm := by simp
  bond_self := by simp

def twinGraph : RootedDigraph (Fin 2) where
  Node := TwinNode
  nodeFintype := inferInstance
  root := .root
  child := fun parent node => parent = .root ∧ node ≠ .root
  label := fun node => match node with
    | .root => ⟨some 0, NodeProvenance.realAtom⟩
    | _ => ⟨some 1, NodeProvenance.realAtom⟩
  depth := fun node => match node with
    | .root => 0
    | _ => 1
  root_depth := rfl
  child_depth := by
    rintro parent node ⟨rfl, hnode⟩
    cases node <;> simp_all
  reachable := by
    intro node
    cases node with
    | root => exact Relation.ReflTransGen.refl
    | marked => exact Relation.ReflTransGen.single ⟨rfl, by decide⟩
    | plain => exact Relation.ReflTransGen.single ⟨rfl, by decide⟩

def twinEvidence : StereochemicalEvidence twinGraph := fun node =>
  match node with
  | .marked => ⟨some ⟨[]⟩, none, none, none, none⟩
  | _ => ⟨none, none, none, none, none⟩

def forwardAddress : TwinNode → List ℕ
  | .root => []
  | .marked => [0]
  | .plain => [1]

def reverseAddress : TwinNode → List ℕ
  | .root => []
  | .marked => [1]
  | .plain => [0]

def forward : twinGraph.Addressing where
  address := forwardAddress
  address_injective := by intro a b h; cases a <;> cases b <;> simp_all [forwardAddress]
  root_address := rfl
  child_iff := by
    intro parent node
    change (parent = .root ∧ node ≠ .root) ↔ _
    cases parent <;> cases node <;> simp [forwardAddress]

def reverse : twinGraph.Addressing where
  address := reverseAddress
  address_injective := by intro a b h; cases a <;> cases b <;> simp_all [reverseAddress]
  root_address := rfl
  child_iff := by
    intro parent node
    change (parent = .root ∧ node ≠ .root) ↔ _
    cases parent <;> cases node <;> simp [reverseAddress]

theorem leaf_childList (node : TwinNode) (hnode : node ≠ .root) : twinGraph.childList node = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro child hchild
  have := (twinGraph.mem_childList).1 hchild
  exact hnode this.1

theorem dense_of {address : TwinNode → List ℕ} (addressing : twinGraph.Addressing)
    (haddress : addressing.address = address)
    (hroot : ∀ slot, (∃ child, address child = [slot]) ↔ slot < 2)
    (hleaf : ∀ node, node ≠ TwinNode.root → ∀ child slot, address child ≠ address node ++ [slot]) :
    Dense addressing := by
  intro parent
  cases parent with
  | root =>
      refine ⟨2, fun slot => ?_⟩
      rw [haddress]
      simpa [show address TwinNode.root = [] by rw [← haddress]; exact addressing.root_address]
        using hroot slot
  | marked =>
      refine ⟨0, fun slot => ⟨fun ⟨child, hchild⟩ => ?_, fun h => absurd h (Nat.not_lt_zero _)⟩⟩
      rw [haddress] at hchild
      exact (hleaf .marked (by decide) child slot hchild).elim
  | plain =>
      refine ⟨0, fun slot => ⟨fun ⟨child, hchild⟩ => ?_, fun h => absurd h (Nat.not_lt_zero _)⟩⟩
      rw [haddress] at hchild
      exact (hleaf .plain (by decide) child slot hchild).elim

theorem forward_dense : Dense forward := by
  refine dense_of (address := forwardAddress) forward rfl ?_ ?_
  · intro slot
    constructor
    · rintro ⟨child, hchild⟩
      cases child <;> simp [forwardAddress] at hchild <;> omega
    · intro h
      rcases (by omega : slot = 0 ∨ slot = 1) with rfl | rfl
      · exact ⟨.marked, rfl⟩
      · exact ⟨.plain, rfl⟩
  · intro node hnode child slot
    cases node <;> cases child <;> simp_all [forwardAddress]

theorem reverse_dense : Dense reverse := by
  refine dense_of (address := reverseAddress) reverse rfl ?_ ?_
  · intro slot
    constructor
    · rintro ⟨child, hchild⟩
      cases child <;> simp [reverseAddress] at hchild <;> omega
    · intro h
      rcases (by omega : slot = 0 ∨ slot = 1) with rfl | rfl
      · exact ⟨.plain, rfl⟩
      · exact ⟨.marked, rfl⟩
  · intro node hnode child slot
    cases node <;> cases child <;> simp_all [reverseAddress]

/-- The two leaves have the same three-rule key. -/
theorem leaves_ruleKey_eq (W D : ℕ) :
    ruleKey twinMolecule twinGraph W D .marked = ruleKey twinMolecule twinGraph W D .plain := by
  rw [ruleKey_eq, ruleKey_eq, leaf_childList .marked (by decide), leaf_childList .plain (by decide)]
  rfl

theorem address_child_ne_root {addressing : twinGraph.Addressing} {parent child : TwinNode}
    {slot : ℕ} (h : addressing.address child = addressing.address parent ++ [slot]) :
    child ≠ .root := by
  rintro rfl
  have hroot : addressing.address TwinNode.root = [] := addressing.root_address
  have := congrArg List.length h
  rw [hroot] at this
  simp at this

theorem keySorted_ruleKey (addressing : twinGraph.Addressing) :
    KeySorted (ruleKey twinMolecule twinGraph twinGraph.width twinGraph.height) addressing := by
  intro parent first second firstSlot secondSlot hfirst hsecond _
  have h₁ := address_child_ne_root hfirst
  have h₂ := address_child_ne_root hsecond
  cases first <;> cases second <;> simp_all [leaves_ruleKey_eq]

/-- **Both sibling orders are canonical for the three-rule family.** -/
theorem forward_canonical : CanonicalAddressing twinMolecule forward :=
  ⟨forward_dense, keySorted_ruleKey forward⟩

theorem reverse_canonical : CanonicalAddressing twinMolecule reverse :=
  ⟨reverse_dense, keySorted_ruleKey reverse⟩

theorem before_singleton_zero (position : List ℕ) (h : HierarchyAddressBefore position [0]) :
    position = [] := by
  unfold HierarchyAddressBefore HierarchyAddressKey at h
  cases position with
  | nil => rfl
  | cons head tail =>
      have hle : (head :: tail).length ≤ 1 := List.head_le_of_lt h
      have hlen : tail.length = 0 := by
        simp only [List.length_cons] at hle
        omega
      have htail : tail = [] := List.eq_nil_of_length_eq_zero hlen
      subst htail
      have hfull : List.Lex (fun a b : ℕ => a < b) (1 :: [head]) (1 :: [0]) :=
        (List.lt_iff_lex_lt (1 :: [head]) (1 :: [0])).1 (by simpa using h)
      have : head < 0 := (List.lex_singleton_iff head 0).1 (List.lex_cons_iff.1 hfull)
      omega

theorem addressEvidence_eq {addressing : twinGraph.Addressing} {node : TwinNode}
    {position : List ℕ} (h : addressing.address node = position) :
    addressEvidence addressing twinEvidence position = some (twinEvidence node) :=
  ((observationAt_iff_eq_addressEvidence addressing twinEvidence position
    (some (twinEvidence node))).1 ⟨node, h, rfl⟩).symm

theorem rule3_outcome (first second : twinGraph.Addressing) (firstNode secondNode : TwinNode)
    (hfirst : first.address firstNode = [0]) (hsecond : second.address secondNode = [0])
    (outcome : Ordering)
    (hlocal : OrderedKeyOutcome
      (stereoValue .rule3DoubleBondGeometry (some (twinEvidence firstNode)))
      (stereoValue .rule3DoubleBondGeometry (some (twinEvidence secondNode))) outcome)
    (houtcome : outcome ≠ Ordering.eq) :
    StereochemicalHierarchyOutcome .rule3DoubleBondGeometry twinGraph first twinEvidence
      twinGraph second twinEvidence outcome := by
  have hat : StereochemicalOutcomeAt .rule3DoubleBondGeometry twinGraph first twinEvidence
      twinGraph second twinEvidence [0] outcome := by
    rw [stereochemicalOutcomeAt_iff, addressEvidence_eq hfirst, addressEvidence_eq hsecond]
    exact hlocal
  have hroot : StereochemicalOutcomeAt .rule3DoubleBondGeometry twinGraph first twinEvidence
      twinGraph second twinEvidence [] Ordering.eq := by
    rw [stereochemicalOutcomeAt_iff, addressEvidence_eq first.root_address,
      addressEvidence_eq second.root_address]
    exact .eq rfl
  have hearlier : ∀ earlier, HierarchyAddressBefore earlier [0] →
      StereochemicalOutcomeAt .rule3DoubleBondGeometry twinGraph first twinEvidence
        twinGraph second twinEvidence earlier Ordering.eq := by
    intro earlier h
    rw [before_singleton_zero earlier h]
    exact hroot
  cases outcome with
  | eq => exact absurd rfl houtcome
  | lt => exact ⟨[0], hat, hearlier⟩
  | gt => exact ⟨[0], hat, hearlier⟩

theorem marked_value : stereoValue .rule3DoubleBondGeometry (some (twinEvidence .marked)) =
    ((encodeHierarchy Rule3Geometry.priority [] : StereoCode) : WithBot StereoCode) := rfl

theorem plain_value : stereoValue .rule3DoubleBondGeometry (some (twinEvidence .plain)) = ⊥ := rfl

/-- **The three-rule family is not stereochemically independent.**  Forward against reverse is
`gt` for Rule 3, reverse against forward is `lt`. -/
theorem threeRuleFamily_rule3_not_independent :
    StereochemicalHierarchyOutcome .rule3DoubleBondGeometry twinGraph forward twinEvidence
        twinGraph reverse twinEvidence Ordering.gt ∧
      StereochemicalHierarchyOutcome .rule3DoubleBondGeometry twinGraph reverse twinEvidence
        twinGraph forward twinEvidence Ordering.lt := by
  constructor
  · refine rule3_outcome forward reverse .marked .plain rfl rfl _ ?_ (by decide)
    rw [marked_value, plain_value]
    exact .gt (WithBot.bot_lt_coe _)
  · refine rule3_outcome reverse forward .plain .marked rfl rfl _ ?_ (by decide)
    rw [marked_value, plain_value]
    exact .lt (WithBot.bot_lt_coe _)

/-- The marked leaf has the strictly larger ordinary key. -/
theorem plain_lt_marked (W D : ℕ) :
    ordinaryKey twinMolecule twinGraph twinEvidence W D .plain <
      ordinaryKey twinMolecule twinGraph twinEvidence W D .marked := by
  rw [ordinaryKey_eq, ordinaryKey_eq]
  simp only [rankedOrdinaryKeys, leaf_childList .marked (by decide),
    leaf_childList .plain (by decide), List.map_nil]
  refine toLex_lt_of_snd ?_ ?_
  · rfl
  · apply List.Lex.rel
    apply List.Lex.rel
    apply List.Lex.rel
    show ((stereoLabel twinGraph twinEvidence .rule3DoubleBondGeometry .plain : StereoLabel) :
        WithBot StereoLabel) <
      ((stereoLabel twinGraph twinEvidence .rule3DoubleBondGeometry .marked : StereoLabel) :
        WithBot StereoLabel)
    exact WithBot.coe_lt_coe.2 (WithBot.bot_lt_coe _)

/-- **The ordinary family keeps the forward order and excludes the reverse order.** -/
theorem forward_ordinaryCanonical : OrdinaryCanonicalAddressing twinMolecule twinEvidence forward := by
  refine ⟨forward_dense, ?_⟩
  intro parent first second firstSlot secondSlot hfirst hsecond hlt
  have h₁ := address_child_ne_root hfirst
  have h₂ := address_child_ne_root hsecond
  cases parent <;> cases first <;> cases second <;>
    simp_all [forward, forwardAddress] <;>
    first | exact le_rfl | exact (plain_lt_marked _ _).le | omega

theorem reverse_not_ordinaryCanonical :
    ¬ OrdinaryCanonicalAddressing twinMolecule twinEvidence reverse := by
  rintro ⟨_, hsorted⟩
  have h := hsorted .root .plain .marked 0 1 rfl rfl (by decide)
  exact absurd h (not_le.2 (plain_lt_marked _ _))

end OrdinaryCanonicalAddressingKernelCertificate
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.stereochemicalNodeOutcome_iff
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.representedBy_compareAddressedHierarchy
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.representedBy_rule4b
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.ordinaryKey_fst
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.ordinaryCanonical_canonical
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.stereoAddressValue_eq_keyObservation
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.stereoAddressValue_ordinaryCanonical_eq
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.keyAddressing_dense_sorted
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.exists_ordinaryCanonicalAddressing
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.stereochemicalHierarchyOutcome_ordinaryCanonical_iff
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.ordinaryKey_iso
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.ordinaryCanonical_transport_iff
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.StereochemicalProblemData.withOrdinaryCanonicalAddressing_constitutionalIndependent
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.StereochemicalProblemData.withOrdinaryCanonicalAddressing_stereochemicalIndependent
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.StereochemicalProblemData.withOrdinaryCanonicalAddressing_exists
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.OrdinaryCanonicalAddressingKernelCertificate.forward_canonical
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.OrdinaryCanonicalAddressingKernelCertificate.reverse_canonical
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.OrdinaryCanonicalAddressingKernelCertificate.threeRuleFamily_rule3_not_independent
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.OrdinaryCanonicalAddressingKernelCertificate.plain_lt_marked
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.OrdinaryCanonicalAddressingKernelCertificate.forward_ordinaryCanonical
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.OrdinaryCanonicalAddressingKernelCertificate.reverse_not_ordinaryCanonical
