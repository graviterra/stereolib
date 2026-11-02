import TetraStereo.UniversalProof.NextFrontier.FramedAtomicDispatch
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096



























































namespace TetraStereo.OneCenter

namespace RawFramedConstitutionalFuelClosure

open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.FrameRuntime
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.FramedAtomicDispatch

/-! ## The profile gate extracts an actual generated root frame -/

/-- Every node collected from a frontier that is entirely inside the canonical center tree rooted at
`root` remains inside that tree.  This is the `CanonicalCenterTreeNode` analogue of
`FramedAtomicDispatch.collect_closed`. -/
theorem collect_reachable_of_frontier (mol : RawMolecule) (root : Nat) :
    ∀ fuel cap frontier result,
      CanonicalTreeProfile.collect fuel cap mol frontier = some result →
      (∀ node, node ∈ frontier → CanonicalCenterTreeNode mol root node) →
      ∀ node, node ∈ result → CanonicalCenterTreeNode mol root node := by
  intro fuel
  induction fuel with
  | zero =>
      intro cap frontier result computed _
      cases frontier with
      | nil => simp [CanonicalTreeProfile.collect] at computed; subst result; simp
      | cons head tail => simp [CanonicalTreeProfile.collect] at computed
  | succ fuel ih =>
      intro cap frontier result computed frontierGenerated
      cases frontier with
      | nil => simp [CanonicalTreeProfile.collect] at computed; subst result; simp
      | cons head tail =>
          rw [CanonicalTreeProfile.collect] at computed <;> try simp only [List.cons_ne_nil, imp_self]
          by_cases capExceeded : cap < (head :: tail).length
          · rw [if_pos capExceeded] at computed
            cases computed
          · rw [if_neg capExceeded] at computed
            cases restEq : CanonicalTreeProfile.collect fuel
                (cap - (head :: tail).length) mol ((head :: tail).flatMap mol.canonicalChildren) with
            | none =>
                rw [restEq] at computed
                cases computed
            | some rest =>
                have restGenerated : ∀ node,
                    node ∈ (head :: tail).flatMap mol.canonicalChildren →
                    CanonicalCenterTreeNode mol root node := by
                  intro node member
                  rcases List.mem_flatMap.mp member with ⟨parent, parentMember, childMember⟩
                  exact .child (frontierGenerated parent parentMember) childMember
                have closed := ih _ _ _ restEq restGenerated
                rw [restEq] at computed
                have resultEq : result = (head :: tail) ++ rest := (Option.some.inj computed).symm
                subst result
                intro node member
                rcases List.mem_append.mp member with atFront | inRest
                · exact frontierGenerated node atFront
                · exact closed node inRest

/-- Unpack the *actual* admitted profile gate.

For `available : FrameRuntime.profile? mol center = some profile`, the center owns a root `root`
with `center.history.getLast? = some root`, the admitted `root < mol.atomCount`, the admitted
`mol.WellFormed`, and `center` is a node of the canonical center tree rooted at `root`.  All four
facts are read off the executable gate; none is assumed. -/
theorem profile_center_generated {mol : RawMolecule} {center : CanonicalBranchNode}
    {profile : FrameRuntime.Profile}
    (available : FrameRuntime.profile? mol center = some profile) :
    ∃ root, center.history.getLast? = some root ∧ root < mol.atomCount ∧
      mol.WellFormed ∧ CanonicalCenterTreeNode mol root center := by
  cases rootEq : center.history.getLast? with
  | none =>
      unfold FrameRuntime.profile? CanonicalTreeProfile.profile? at available
      simp only [rootEq, Bind.bind, Option.bind] at available
      cases available
  | some root =>
      unfold FrameRuntime.profile? CanonicalTreeProfile.profile? at available
      simp only [rootEq, Bind.bind, Option.bind] at available
      split at available
      · contradiction
      · rename_i guardFalse
        have guardEq : (!(decide (root < mol.atomCount)) ||
            !(mol.bonds.all mol.bondEndpointsOK?)) = false :=
          Bool.eq_false_of_not_eq_true guardFalse
        have rootBound : root < mol.atomCount := by
          have notNotRoot : (!(decide (root < mol.atomCount))) = false :=
            (Bool.or_eq_false_iff.mp guardEq).1
          have rootDecide : decide (root < mol.atomCount) = true := by
            cases h : decide (root < mol.atomCount) with
            | false => simp [h] at notNotRoot
            | true => rfl
          exact of_decide_eq_true rootDecide
        have bondsAll : mol.bonds.all mol.bondEndpointsOK? = true := by
          have notNotBonds : (!(mol.bonds.all mol.bondEndpointsOK?)) = false :=
            (Bool.or_eq_false_iff.mp guardEq).2
          cases h : mol.bonds.all mol.bondEndpointsOK? with
            | false => simp [h] at notNotBonds
            | true => rfl
        have wellFormed : mol.WellFormed := by
          intro bond member
          exact (mol.bondEndpointsOK?_eq_true_iff bond).mp
            ((List.all_eq_true.mp bondsAll) bond member)
        cases collected : CanonicalTreeProfile.collect (mol.atomCount + 1) mol.atomCount mol
            [{ atom := root, parent := root, history := [root], provenance := CanonicalNodeProvenance.realAtom }] with
        | none =>
            rw [collected] at available
            cases available
        | some inventory =>
            rw [collected] at available
            dsimp only at available
            split at available
            · contradiction
            · rename_i containsFalse
              have containsNot : (!(inventory.contains center)) = false :=
                Bool.eq_false_of_not_eq_true containsFalse
              have centerContains : inventory.contains center = true := by
                cases h : inventory.contains center with
                | false =>
                    rw [h] at containsNot
                    simp at containsNot
                | true => rfl
              split at available
              · contradiction
              · have centerMember : center ∈ inventory := List.contains_iff_mem.mp centerContains
                have frontierGenerated : ∀ node : CanonicalBranchNode,
                    node ∈ [canonicalCenterRoot root] →
                    CanonicalCenterTreeNode mol root node := by
                  intro node member
                  have nodeEq : node = canonicalCenterRoot root := by
                    simpa using member
                  subst node
                  exact .root
                have reachable := collect_reachable_of_frontier mol root (mol.atomCount + 1)
                  mol.atomCount [canonicalCenterRoot root] inventory collected frontierGenerated
                exact ⟨root, rfl, rootBound, wellFormed, reachable center centerMember⟩

/-! ## Recursive support for framed cursors and frontiers -/

/-- Support invariant consumed by the runtime: a padding cursor is supported whenever its retained
parent is observed; an actual cursor is supported when it is a genuine reroot cursor of the center
tree rooted at `root` and its molecule-derived height is below the fuel. -/
inductive FramedCursorSupport (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (root : Nat) : Nat → FrameRuntime.Cursor → Prop where
  | padding (fuel : Nat) (parent : FrameRuntime.Cursor)
      (observed : ∃ distance, FrameRuntime.cursor? mol profile parent = some distance) :
      FramedCursorSupport mol profile root fuel (.padding parent)
  | actual (fuel : Nat) (cursor : CanonicalRerootCursor)
      (eligible : CanonicalCenterRerootCursor mol root cursor)
      (heightLe : moleculeCursorHeight mol cursor ≤ fuel) :
      FramedCursorSupport mol profile root fuel (.actual cursor)

/-- Support for a paired frontier. -/
def FramedFrontierSupport (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (root : Nat) (fuel : Nat) (pairs : List (FrameRuntime.Cursor × FrameRuntime.Cursor)) : Prop :=
  ∀ pair, pair ∈ pairs →
    FramedCursorSupport mol profile root fuel pair.1 ∧
    FramedCursorSupport mol profile root fuel pair.2

/-- Padding cursors are always terminal. -/
theorem terminal_padding (mol : RawMolecule) (cursor : FrameRuntime.Cursor) :
    FrameRuntime.terminal mol (.padding cursor) = true := by
  simp [FrameRuntime.terminal, FrameRuntime.Cursor.original, cursorTerminal,
    canonicalPhantom, CanonicalBranchNode.forcedLeaf]

namespace FramedCursorSupport

/-- Support is monotone in the fuel. -/
theorem mono {mol : RawMolecule} {profile : FrameRuntime.Profile} {root : Nat}
    {smaller larger : Nat} {cursor : FrameRuntime.Cursor}
    (support : FramedCursorSupport mol profile root smaller cursor) (le : smaller ≤ larger) :
    FramedCursorSupport mol profile root larger cursor := by
  cases support with
  | padding parent parentObserved => exact .padding larger parent parentObserved
  | actual cursor eligible heightLe => exact .actual larger cursor eligible (heightLe.trans le)

/-- Support at `fuel` implies support at `fuel + 1`. -/
theorem succ {mol : RawMolecule} {profile : FrameRuntime.Profile} {root : Nat} {fuel : Nat}
    {cursor : FrameRuntime.Cursor} (support : FramedCursorSupport mol profile root fuel cursor) :
    FramedCursorSupport mol profile root (fuel + 1) cursor :=
  support.mono (Nat.le_succ fuel)

/-- Every supported cursor is observed by the actual runtime `cursor?`. -/
theorem observed {mol : RawMolecule} {root : Nat} {center : CanonicalBranchNode}
    {profile : FrameRuntime.Profile}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (available : FrameRuntime.profile? mol center = some profile) :
    ∀ (fuel : Nat) (cursor : FrameRuntime.Cursor),
      FramedCursorSupport mol profile root fuel cursor →
      ∃ distance, FrameRuntime.cursor? mol profile cursor = some distance := by
  intro fuel cursor support
  cases support with
  | padding parent parentObserved =>
      rcases parentObserved with ⟨d, hd⟩
      exact ⟨d + 1, by simp [FrameRuntime.cursor?, hd]⟩
  | actual cursor eligible _ =>
      exact generated_cursor_observed centerGenerated profile available eligible

/-- A cursor supported at fuel `0` is terminal. -/
theorem zero_terminal {mol : RawMolecule} {profile : FrameRuntime.Profile} {root : Nat}
    (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed) :
    ∀ cursor, FramedCursorSupport mol profile root 0 cursor →
      FrameRuntime.terminal mol cursor = true := by
  intro cursor support
  cases support with
  | padding parent parentObserved => exact terminal_padding mol parent
  | actual cursor eligible heightZero =>
      have heightEq : moleculeCursorHeight mol cursor = 0 := by omega
      have terminal : cursorTerminal mol cursor = true :=
        moleculeCursorHeight_zero_terminal centerBound wellFormed cursor eligible heightEq
      simpa [FrameRuntime.terminal, FrameRuntime.Cursor.original] using terminal

end FramedCursorSupport

/-- An eligible reroot cursor has a real node in the admitted profile domain. -/
theorem eligible_node_real {mol : RawMolecule} {root : Nat} {center : CanonicalBranchNode}
    {profile : FrameRuntime.Profile}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (available : FrameRuntime.profile? mol center = some profile)
    {cursor : CanonicalRerootCursor} (eligible : CanonicalCenterRerootCursor mol root cursor) :
    cursor.node.provenance = CanonicalNodeProvenance.realAtom := by
  have generated : CanonicalCenterTreeNode mol root cursor.node := by
    cases eligible with
    | @descending parent node parentGenerated member => exact .child parentGenerated member
    | @ascending node child nodeGenerated member => exact nodeGenerated
  exact (profile_generated centerGenerated profile available cursor.node generated).2

/-- A real node has a total Rule-1a authoritative label. -/
theorem realAtom_rule1a_label (mol : RawMolecule) (node : CanonicalBranchNode)
    (real : node.provenance = CanonicalNodeProvenance.realAtom) :
    mol.canonicalRule1aLabelAuthoritative? node =
      some { numerator := mol.atomZAt node.atom, denominator := 1 } := by
  unfold canonicalRule1aLabelAuthoritative?
  rw [real]

/-- Every supported framed cursor carries a total Rule-1a label on the actual admitted domain. -/
theorem framed_cursor_rule1a_label (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (root : Nat) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (available : FrameRuntime.profile? mol center = some profile) :
    ∀ (fuel : Nat) (cursor : FrameRuntime.Cursor),
      FramedCursorSupport mol profile root fuel cursor →
      ∃ label, mol.canonicalRule1aLabelAuthoritative?
        (FrameRuntime.Cursor.original mol cursor).node = some label := by
  intro fuel cursor support
  cases support with
  | padding parent parentObserved =>
      refine ⟨{ numerator := 0, denominator := 1 }, ?_⟩
      simp [FrameRuntime.Cursor.original, canonicalPhantom, canonicalRule1aLabelAuthoritative?]
  | actual cursor eligible _ =>
      have real : cursor.node.provenance = CanonicalNodeProvenance.realAtom :=
        eligible_node_real centerGenerated available eligible
      refine ⟨{ numerator := mol.atomZAt cursor.node.atom, denominator := 1 }, ?_⟩
      simpa [FrameRuntime.Cursor.original] using realAtom_rule1a_label mol cursor.node real

/-! ## Totality of the actual runtime on supported inputs -/

/-- `FrameRuntime.label?` is total for every supported cursor pair. -/
theorem label?_exists_of_support (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (root : Nat) (fuel : Nat) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (available : FrameRuntime.profile? mol center = some profile) :
    ∀ (rule : CanonicalRuleStage) (left right : FrameRuntime.Cursor),
      FramedCursorSupport mol profile root fuel left →
      FramedCursorSupport mol profile root fuel right →
      ∃ ordering, FrameRuntime.label? mol profile true rule left right = some ordering := by
  intro rule left right leftSupport rightSupport
  have hld : ∃ ld, FrameRuntime.cursor? mol profile left = some ld :=
    FramedCursorSupport.observed centerGenerated available fuel left leftSupport
  have hrd : ∃ rd, FrameRuntime.cursor? mol profile right = some rd :=
    FramedCursorSupport.observed centerGenerated available fuel right rightSupport
  rcases hld with ⟨ld, ldEq⟩
  rcases hrd with ⟨rd, rdEq⟩
  cases rule with
  | rule1a =>
      rcases framed_cursor_rule1a_label mol profile root centerGenerated available fuel left
          leftSupport with ⟨ll, hll⟩
      rcases framed_cursor_rule1a_label mol profile root centerGenerated available fuel right
          rightSupport with ⟨rl, hrl⟩
      exact ⟨compareCIPAtomicLabel ll rl, by
        simp [FrameRuntime.label?, ldEq, rdEq, hll, hrl, compareCanonicalNodeRuleAuthoritative?]⟩
  | rule1b =>
      exact ⟨(if ld < rd then Ordering.gt else if rd < ld then Ordering.lt else Ordering.eq), by
        simp [FrameRuntime.label?, ldEq, rdEq]⟩
  | rule2 =>
      exact ⟨mol.compareCanonicalNodeRule .rule2 (FrameRuntime.Cursor.original mol left).node
        (FrameRuntime.Cursor.original mol right).node, by
        simp [FrameRuntime.label?, ldEq, rdEq, compareCanonicalNodeRuleAuthoritative?]⟩

/-- `FrameRuntime.pairLabels?` is total for every supported frontier. -/
theorem pairLabels?_exists_of_support (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (root : Nat) (fuel : Nat) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (available : FrameRuntime.profile? mol center = some profile)
    (rule : CanonicalRuleStage) :
    ∀ pairs, FramedFrontierSupport mol profile root fuel pairs →
      ∃ ordering, FrameRuntime.pairLabels? mol profile true rule pairs = some ordering
  | [], _ => ⟨Ordering.eq, by simp [FrameRuntime.pairLabels?]⟩
  | (left, right) :: pairs, support => by
      have head := support (left, right) (by simp)
      have tail : FramedFrontierSupport mol profile root fuel pairs := by
        intro pair member
        exact support pair (by simp [member])
      rcases label?_exists_of_support mol profile root fuel centerGenerated available rule left right
          head.1 head.2 with ⟨cmp, hcmp⟩
      rcases pairLabels?_exists_of_support mol profile root fuel centerGenerated available rule
          pairs tail with ⟨rest, hrest⟩
      cases cmp with
      | lt => exact ⟨.lt, by simp [FrameRuntime.pairLabels?, hcmp]⟩
      | gt => exact ⟨.gt, by simp [FrameRuntime.pairLabels?, hcmp]⟩
      | eq => exact ⟨rest, by simp [FrameRuntime.pairLabels?, hcmp, hrest]⟩

/-- `List.mapM` over `Option` succeeds whenever every element is observed. -/
theorem mapM_exists_of_all_observed {α : Type*} (f : α → Option Nat) :
    ∀ values : List α, (∀ value, value ∈ values → ∃ result, f value = some result) →
      ∃ validated, values.mapM f = some validated
  | [], _ => ⟨[], rfl⟩
  | value :: values, observed => by
      have head := observed value (by simp)
      have tail : ∀ v, v ∈ values → ∃ result, f v = some result := by
        intro v member
        exact observed v (by simp [member])
      rcases head with ⟨result, hresult⟩
      rcases mapM_exists_of_all_observed f values tail with ⟨rest, hrest⟩
      exact ⟨result :: rest, by rw [List.mapM_cons, hresult, hrest]; rfl⟩


/-- `FrameRuntime.insert?` exists and preserves support when the comparison is total on supported
cursors.  Mirrors `insertCursorBy?_exists_of_supported`. -/
theorem insert?_exists_of_supported (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (root : Nat) (fuel : Nat)
    (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (total : ∀ left right,
      FramedCursorSupport mol profile root fuel left →
      FramedCursorSupport mol profile root fuel right →
      ∃ ordering, before left right = some ordering)
    (candidate : FrameRuntime.Cursor)
    (candidateSupport : FramedCursorSupport mol profile root fuel candidate) :
    ∀ input, (∀ cursor, cursor ∈ input → FramedCursorSupport mol profile root fuel cursor) →
      ∃ output,
        FrameRuntime.insert? before candidate input = some output ∧
        (∀ cursor, cursor ∈ output → FramedCursorSupport mol profile root fuel cursor) ∧
        output.length = input.length + 1
  | [], _ => ⟨[candidate], rfl, by simpa, rfl⟩
  | head :: tail, inputSupport => by
      have headSupport := inputSupport head (by simp)
      rcases total candidate head candidateSupport headSupport with ⟨ordering, orderingEq⟩
      cases ordering with
      | lt =>
          rcases insert?_exists_of_supported mol profile root fuel before total candidate
              candidateSupport tail (fun cursor member => inputSupport cursor (by simp [member]))
            with ⟨deeper, deeperEq, deeperSupport, deeperLength⟩
          refine ⟨head :: deeper, ?_, ?_, ?_⟩
          · simp [FrameRuntime.insert?, orderingEq, deeperEq]
          · intro cursor member
            rcases List.mem_cons.mp member with rfl | member
            · exact headSupport
            · exact deeperSupport cursor member
          · simp [deeperLength]
      | eq =>
          refine ⟨candidate :: head :: tail, ?_, ?_, by simp⟩
          · simp [FrameRuntime.insert?, orderingEq]
          · intro cursor member
            simp at member
            rcases member with rfl | rfl | member
            · exact candidateSupport
            · exact headSupport
            · exact inputSupport cursor (by simp [member])
      | gt =>
          refine ⟨candidate :: head :: tail, ?_, ?_, by simp⟩
          · simp [FrameRuntime.insert?, orderingEq]
          · intro cursor member
            simp at member
            rcases member with rfl | rfl | member
            · exact candidateSupport
            · exact headSupport
            · exact inputSupport cursor (by simp [member])

/-- `FrameRuntime.sort?` exists and preserves support when the comparison is total on supported
cursors.  Mirrors `sortCursorsBy?_exists_of_supported`. -/
theorem sort?_exists_of_supported (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (root : Nat) (fuel : Nat)
    (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (total : ∀ left right,
      FramedCursorSupport mol profile root fuel left →
      FramedCursorSupport mol profile root fuel right →
      ∃ ordering, before left right = some ordering) :
    ∀ input, (∀ cursor, cursor ∈ input → FramedCursorSupport mol profile root fuel cursor) →
      ∃ output,
        FrameRuntime.sort? before input = some output ∧
        (∀ cursor, cursor ∈ output → FramedCursorSupport mol profile root fuel cursor) ∧
        output.length = input.length
  | [], _ => ⟨[], rfl, by simp, rfl⟩
  | head :: tail, inputSupport => by
      have headSupport := inputSupport head (by simp)
      rcases sort?_exists_of_supported mol profile root fuel before total tail
          (fun cursor member => inputSupport cursor (by simp [member])) with
        ⟨sorted, sortedEq, sortedSupport, sortedLength⟩
      rcases insert?_exists_of_supported mol profile root fuel before total head headSupport sorted
          sortedSupport with ⟨output, outputEq, outputSupport, outputLength⟩
      refine ⟨output, ?_, outputSupport, ?_⟩
      · simp [FrameRuntime.sort?, sortedEq, outputEq]
      · calc
          output.length = sorted.length + 1 := outputLength
          _ = tail.length + 1 := by rw [sortedLength]
          _ = (head :: tail).length := by simp

/-- `FrameRuntime.ranked?` is total and lowers the support fuel, under the P-92 width bound. -/
theorem ranked?_exists_of_support (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (root : Nat) (fuel : Nat) {center : CanonicalBranchNode}
    (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (available : FrameRuntime.profile? mol center = some profile)
    (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (beforeTotal : ∀ left right,
      FramedCursorSupport mol profile root fuel left →
      FramedCursorSupport mol profile root fuel right →
      ∃ ordering, before left right = some ordering) :
    ∀ cursor, FramedCursorSupport mol profile root (fuel + 1) cursor →
      ∃ ranked, FrameRuntime.ranked? mol profile true before cursor = some ranked ∧
        ∀ child, child ∈ ranked → FramedCursorSupport mol profile root fuel child := by
  intro cursor support
  cases support with
  | padding parent parentObserved =>
      have paddingObserved : ∃ d, FrameRuntime.cursor? mol profile (.padding parent) = some d := by
        rcases parentObserved with ⟨d, hd⟩
        exact ⟨d + 1, by simp [FrameRuntime.cursor?, hd]⟩
      have rankedEq : FrameRuntime.ranked? mol profile true before (.padding parent) =
          some (List.replicate RawMolecule.authoritativeChildSlots (.padding (.padding parent))) := by
        rcases parentObserved with ⟨d, hd⟩
        simp [FrameRuntime.ranked?, FrameRuntime.cursor?, FrameRuntime.Cursor.original,
          canonicalPhantom, hd, CanonicalRerootCursor.children, CanonicalBranchNode.forcedLeaf,
          FrameRuntime.sort?]
      refine ⟨List.replicate RawMolecule.authoritativeChildSlots (.padding (.padding parent)),
        rankedEq, ?_⟩
      intro child member
      have childEq : child = .padding (.padding parent) := List.eq_of_mem_replicate member
      subst child
      exact .padding fuel (.padding parent) paddingObserved
  | actual cursor eligible heightLe =>
      have observed : ∃ distance, FrameRuntime.cursor? mol profile (.actual cursor) = some distance :=
        generated_cursor_observed centerGenerated profile available eligible
      have width : ((cursor.children mol).map FrameRuntime.Cursor.actual).length ≤
          RawMolecule.authoritativeChildSlots := by
        simpa using canonicalCenterRerootCursor_local_width bonding cursor eligible
      have width' : (cursor.children mol).length ≤
          RawMolecule.authoritativeChildSlots := by
        simpa using width
      have childrenSupported : ∀ child,
          child ∈ (cursor.children mol).map FrameRuntime.Cursor.actual →
          FramedCursorSupport mol profile root fuel child := by
        intro child member
        rw [List.mem_map] at member
        rcases member with ⟨under, underMember, rfl⟩
        have childEligible : CanonicalCenterRerootCursor mol root under :=
          CanonicalCenterRerootCursor.child eligible underMember
        have heightLt : moleculeCursorHeight mol under < moleculeCursorHeight mol cursor :=
          moleculeCursorHeight_child_lt centerBound wellFormed eligible underMember
        have heightLe' : moleculeCursorHeight mol under ≤ fuel := by omega
        exact .actual fuel under childEligible heightLe'
      have childrenObserved : ∀ child,
          child ∈ (cursor.children mol).map FrameRuntime.Cursor.actual →
          ∃ d, FrameRuntime.cursor? mol profile child = some d := by
        intro child member
        exact FramedCursorSupport.observed centerGenerated available fuel child
          (childrenSupported child member)
      rcases mapM_exists_of_all_observed (FrameRuntime.cursor? mol profile)
          ((cursor.children mol).map FrameRuntime.Cursor.actual) childrenObserved with
        ⟨validated, validatedEq⟩
      rcases sort?_exists_of_supported mol profile root fuel before beforeTotal
          ((cursor.children mol).map FrameRuntime.Cursor.actual) childrenSupported with
        ⟨sorted, sortedEq, sortedSupport, sortedLength⟩
      rcases observed with ⟨distance, hdistance⟩
      have notTooWide : ¬ RawMolecule.authoritativeChildSlots <
          ((cursor.children mol).map FrameRuntime.Cursor.actual).length :=
        Nat.not_lt_of_ge width
      refine ⟨sorted ++ List.replicate
          (RawMolecule.authoritativeChildSlots - sorted.length) (.padding (.actual cursor)), ?_, ?_⟩
      · simp [FrameRuntime.ranked?, FrameRuntime.Cursor.original, hdistance,
          validatedEq, sortedEq]
        exact width'
      · intro child member
        rcases List.mem_append.mp member with inSorted | inPadding
        · exact sortedSupport child inSorted
        · have childEq : child = .padding (.actual cursor) := List.eq_of_mem_replicate inPadding
          subst child
          exact .padding fuel (.actual cursor) ⟨distance, hdistance⟩

/-- A frontier supported at fuel `0` has empty `nextPairs?`. -/
theorem nextPairs?_zero_eq_nil (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (root : Nat) (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering) :
    ∀ pairs, FramedFrontierSupport mol profile root 0 pairs →
      FrameRuntime.nextPairs? mol profile true before pairs = some [] := by
  intro pairs
  induction pairs with
  | nil =>
      intro _
      rfl
  | cons pair rest ih =>
      intro support
      have head := support pair (by simp)
      have tail : FramedFrontierSupport mol profile root 0 rest := by
        intro candidate member
        exact support candidate (by simp [member])
      have restEq := ih tail
      have leftTerminal : FrameRuntime.terminal mol pair.1 = true :=
        FramedCursorSupport.zero_terminal centerBound wellFormed pair.1 head.1
      have rightTerminal : FrameRuntime.terminal mol pair.2 = true :=
        FramedCursorSupport.zero_terminal centerBound wellFormed pair.2 head.2
      have both : (FrameRuntime.terminal mol pair.1 &&
          FrameRuntime.terminal mol pair.2) = true := by
        simp [leftTerminal, rightTerminal]
      simp [FrameRuntime.nextPairs?, both, restEq]

/-- `FrameRuntime.nextPairs?` exists and lowers the support fuel. -/
theorem nextPairs?_exists_of_support (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (root : Nat) (fuel : Nat) {center : CanonicalBranchNode}
    (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (available : FrameRuntime.profile? mol center = some profile)
    (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (beforeTotal : ∀ left right,
      FramedCursorSupport mol profile root fuel left →
      FramedCursorSupport mol profile root fuel right →
      ∃ ordering, before left right = some ordering) :
    ∀ pairs, FramedFrontierSupport mol profile root (fuel + 1) pairs →
      ∃ next, FrameRuntime.nextPairs? mol profile true before pairs = some next ∧
        FramedFrontierSupport mol profile root fuel next := by
  intro pairs
  induction pairs with
  | nil =>
      intro _
      refine ⟨[], by simp [FrameRuntime.nextPairs?], ?_⟩
      intro pair member
      simp at member
  | cons pair rest ih =>
      intro support
      have head := support pair (by simp)
      have tail : FramedFrontierSupport mol profile root (fuel + 1) rest := by
        intro candidate member
        exact support candidate (by simp [member])
      rcases ih tail with ⟨restResult, restEq, restSupport⟩
      by_cases bothTerminal : FrameRuntime.terminal mol pair.1 = true ∧
          FrameRuntime.terminal mol pair.2 = true
      · refine ⟨restResult, by simp [FrameRuntime.nextPairs?, restEq, bothTerminal], restSupport⟩
      · rcases ranked?_exists_of_support mol profile root fuel centerBound wellFormed bonding
            centerGenerated available before beforeTotal pair.1 head.1 with
          ⟨left, leftEq, leftSupport⟩
        rcases ranked?_exists_of_support mol profile root fuel centerBound wellFormed bonding
            centerGenerated available before beforeTotal pair.2 head.2 with
          ⟨right, rightEq, rightSupport⟩
        refine ⟨left.zip right ++ restResult, ?_, ?_⟩
        · simp [FrameRuntime.nextPairs?, restEq, bothTerminal, leftEq, rightEq]
        · intro candidate member
          rcases List.mem_append.mp member with zipped | inRest
          · have components := List.of_mem_zip zipped
            exact ⟨leftSupport candidate.1 components.1, rightSupport candidate.2 components.2⟩
          · exact restSupport candidate inRest

/-- `FrameRuntime.compareRule?` is total on supported frontiers within the recursive fuel budget. -/
theorem compareRule?_exists_of_support (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (root : Nat) {center : CanonicalBranchNode}
    (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (available : FrameRuntime.profile? mol center = some profile)
    (rankFuel : Nat)
    (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (beforeTotal : ∀ left right,
      FramedCursorSupport mol profile root rankFuel left →
      FramedCursorSupport mol profile root rankFuel right →
      ∃ ordering, before left right = some ordering)
    (rule : CanonicalRuleStage) :
    ∀ fuel pairs, fuel ≤ rankFuel + 1 → FramedFrontierSupport mol profile root fuel pairs →
      ∃ ordering, FrameRuntime.compareRule? mol profile true before rule fuel pairs = some ordering := by
  intro fuel
  induction fuel with
  | zero =>
      intro pairs _ support
      rcases pairLabels?_exists_of_support mol profile root 0 centerGenerated available rule pairs
          support with ⟨labels, labelsEq⟩
      have capFalse : (!(true : Bool) && RawMolecule.defaultBranchWidthCap < pairs.length) =
          false := by simp
      cases labels with
      | lt =>
          refine ⟨.lt, ?_⟩
          rw [FrameRuntime.compareRule?, if_neg (by simp), labelsEq]
          simp
      | gt =>
          refine ⟨.gt, ?_⟩
          rw [FrameRuntime.compareRule?, if_neg (by simp), labelsEq]
          simp
      | eq =>
          have nextEq : FrameRuntime.nextPairs? mol profile true before pairs = some [] :=
            nextPairs?_zero_eq_nil mol profile root centerBound wellFormed before pairs support
          refine ⟨.eq, ?_⟩
          rw [FrameRuntime.compareRule?, if_neg (by simp), labelsEq, nextEq]
          simp
  | succ fuel ih =>
      intro pairs fuelLe support
      have lowerLe : fuel ≤ rankFuel := by omega
      have localTotal : ∀ left right,
          FramedCursorSupport mol profile root fuel left →
          FramedCursorSupport mol profile root fuel right →
          ∃ ordering, before left right = some ordering := by
        intro left right leftSupport rightSupport
        exact beforeTotal left right (leftSupport.mono lowerLe) (rightSupport.mono lowerLe)
      rcases pairLabels?_exists_of_support mol profile root (fuel + 1) centerGenerated available
          rule pairs support with ⟨labels, labelsEq⟩
      have capFalse : (!(true : Bool) && RawMolecule.defaultBranchWidthCap < pairs.length) =
          false := by simp
      cases labels with
      | lt =>
          refine ⟨.lt, ?_⟩
          rw [FrameRuntime.compareRule?, if_neg (by simp), labelsEq]
          simp
      | gt =>
          refine ⟨.gt, ?_⟩
          rw [FrameRuntime.compareRule?, if_neg (by simp), labelsEq]
          simp
      | eq =>
          rcases nextPairs?_exists_of_support mol profile root fuel centerBound wellFormed bonding
              centerGenerated available before localTotal pairs support with
            ⟨next, nextEq, nextSupport⟩
          cases next with
          | nil =>
              refine ⟨.eq, ?_⟩
              rw [FrameRuntime.compareRule?, if_neg (by simp), labelsEq, nextEq]
              simp
          | cons pair rest =>
              rcases ih (pair :: rest) (by omega) nextSupport with ⟨decision, decisionEq⟩
              refine ⟨decision, ?_⟩
              rw [FrameRuntime.compareRule?, if_neg (by simp), labelsEq, nextEq]
              show FrameRuntime.compareRule? mol profile true before rule fuel (pair :: rest) =
                some decision
              exact decisionEq

/-- `FrameRuntime.compareBranch?` at stage `.rule2` is total on supported cursor pairs. -/
theorem compareBranch?_exists_of_support (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (root : Nat) {center : CanonicalBranchNode}
    (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (available : FrameRuntime.profile? mol center = some profile) :
    ∀ (fuel : Nat) (left right : FrameRuntime.Cursor),
      FramedCursorSupport mol profile root fuel left →
      FramedCursorSupport mol profile root fuel right →
      ∃ decision, FrameRuntime.compareBranch? mol profile true fuel .rule2 left right = some decision := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right leftSupport rightSupport
      have leftTerminal : FrameRuntime.terminal mol left = true :=
        FramedCursorSupport.zero_terminal centerBound wellFormed left leftSupport
      have rightTerminal : FrameRuntime.terminal mol right = true :=
        FramedCursorSupport.zero_terminal centerBound wellFormed right rightSupport
      rcases label?_exists_of_support mol profile root 0 centerGenerated available .rule1a left right
          leftSupport rightSupport with ⟨first, firstEq⟩
      cases first with
      | lt =>
          refine ⟨.lt, ?_⟩
          rw [FrameRuntime.compareBranch?, FrameRuntime.throughLabels?, firstEq]
          simp [leftTerminal, rightTerminal]
      | gt =>
          refine ⟨.gt, ?_⟩
          rw [FrameRuntime.compareBranch?, FrameRuntime.throughLabels?, firstEq]
          simp [leftTerminal, rightTerminal]
      | eq =>
          rcases label?_exists_of_support mol profile root 0 centerGenerated available .rule1b
              left right leftSupport rightSupport with ⟨dist, distEq⟩
          cases dist with
          | lt =>
              refine ⟨.lt, ?_⟩
              rw [FrameRuntime.compareBranch?, FrameRuntime.throughLabels?, firstEq, distEq]
              simp [leftTerminal, rightTerminal]
          | gt =>
              refine ⟨.gt, ?_⟩
              rw [FrameRuntime.compareBranch?, FrameRuntime.throughLabels?, firstEq, distEq]
              simp [leftTerminal, rightTerminal]
          | eq =>
              rcases label?_exists_of_support mol profile root 0 centerGenerated available .rule2
                  left right leftSupport rightSupport with ⟨mass, massEq⟩
              refine ⟨mass, ?_⟩
              rw [FrameRuntime.compareBranch?, FrameRuntime.throughLabels?, firstEq, distEq, massEq]
              simp [leftTerminal, rightTerminal]
  | succ fuel ih =>
      intro left right leftSupport rightSupport
      let before := FrameRuntime.compareBranch? mol profile true fuel .rule2
      have beforeTotal : ∀ l r,
          FramedCursorSupport mol profile root fuel l →
          FramedCursorSupport mol profile root fuel r →
          ∃ ordering, before l r = some ordering := by
        intro l r lSupport rSupport
        exact ih l r lSupport rSupport
      have frontier : FramedFrontierSupport mol profile root (fuel + 1) [(left, right)] := by
        intro pair member
        have pairEq : pair = (left, right) := by simpa using member
        subst pair
        exact ⟨leftSupport, rightSupport⟩
      rcases compareRule?_exists_of_support mol profile root centerBound wellFormed bonding
          centerGenerated available fuel before beforeTotal .rule1a (fuel + 1) [(left, right)]
          (by omega) frontier with ⟨first, firstEq⟩
      cases first with
      | lt =>
          refine ⟨.lt, ?_⟩
          rw [FrameRuntime.compareBranch?]
          simp [before, firstEq]
      | gt =>
          refine ⟨.gt, ?_⟩
          rw [FrameRuntime.compareBranch?]
          simp [before, firstEq]
      | eq =>
          rcases compareRule?_exists_of_support mol profile root centerBound wellFormed bonding
              centerGenerated available fuel before beforeTotal .rule1b (fuel + 1) [(left, right)]
              (by omega) frontier with ⟨dist, distEq⟩
          cases dist with
          | lt =>
              refine ⟨.lt, ?_⟩
              rw [FrameRuntime.compareBranch?]
              simp [before, firstEq, distEq]
          | gt =>
              refine ⟨.gt, ?_⟩
              rw [FrameRuntime.compareBranch?]
              simp [before, firstEq, distEq]
          | eq =>
              rcases compareRule?_exists_of_support mol profile root centerBound wellFormed bonding
                  centerGenerated available fuel before beforeTotal .rule2 (fuel + 1) [(left, right)]
                  (by omega) frontier with ⟨mass, massEq⟩
              refine ⟨mass, ?_⟩
              rw [FrameRuntime.compareBranch?]
              simp [before, firstEq, distEq, massEq]

/-! ## The explicit fuel bound -/

/-- **Structural fuel bound.**

For a well-formed molecule, a center root `root` admitted (`root < mol.atomCount`), the P-92
bonding-number-six bound at that root, a center node generated in the canonical center tree rooted at
`root`, and an admitted profile for that center, every pair of eligible ligand cursors terminates:
the *actual* `FrameRuntime.compareBranch? … .rule2` returns `some ordering` within fuel
`2 * mol.atomCount + 2`. -/
theorem compareBranch_rule2_fuel_bound (mol : RawMolecule) (profile : FrameRuntime.Profile)
    {center : CanonicalBranchNode} (root : Nat)
    (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (available : FrameRuntime.profile? mol center = some profile)
    {left right : CanonicalRerootCursor}
    (leftEligible : CanonicalCenterRerootCursor mol root left)
    (rightEligible : CanonicalCenterRerootCursor mol root right) :
    ∃ ordering,
      FrameRuntime.compareBranch? mol profile true (2 * mol.atomCount + 2) .rule2
        (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) = some ordering := by
  have leftHeight : moleculeCursorHeight mol left ≤ 2 * mol.atomCount + 1 :=
    moleculeCursorHeight_le_two_mul_atomCount_add_one centerBound wellFormed leftEligible
  have rightHeight : moleculeCursorHeight mol right ≤ 2 * mol.atomCount + 1 :=
    moleculeCursorHeight_le_two_mul_atomCount_add_one centerBound wellFormed rightEligible
  have leftSupport : FramedCursorSupport mol profile root (2 * mol.atomCount + 2) (.actual left) :=
    .actual (2 * mol.atomCount + 2) left leftEligible (by omega)
  have rightSupport : FramedCursorSupport mol profile root (2 * mol.atomCount + 2) (.actual right) :=
    .actual (2 * mol.atomCount + 2) right rightEligible (by omega)
  exact compareBranch?_exists_of_support mol profile root centerBound wellFormed bonding
    centerGenerated available (2 * mol.atomCount + 2) (.actual left) (.actual right)
    leftSupport rightSupport

/-- **Endpoint: every actual admitted generated root frame terminates.**

Starting only from a well-formed molecule, the global P-92 bonding-number-six admission, an actual
admitted profile `available : FrameRuntime.profile? mol center = some profile`, and two actual ligand
cursors of that center occurrence, the *actual* `FrameRuntime.compareBranch? … .rule2` terminates and
returns `some ordering` within fuel `2 * mol.atomCount + 2`.  No root, no fuel and no key are assumed
to exist: they are extracted from the gate by `profile_center_generated`. -/
theorem compareBranch_rule2_of_admitted_profile (mol : RawMolecule) (profile : FrameRuntime.Profile)
    {center : CanonicalBranchNode}
    (wellFormed : mol.WellFormed)
    (bonding : ∀ root, CanonicalCenterBondingNumberSix mol root)
    (available : FrameRuntime.profile? mol center = some profile)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol center)
    (rightMember : right ∈ occurrenceLigandCursors mol center) :
    ∃ ordering,
      FrameRuntime.compareBranch? mol profile true (2 * mol.atomCount + 2) .rule2
        (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) = some ordering := by
  rcases profile_center_generated available with ⟨root, _rootTail, rootBound, _wellFormed,
    centerGenerated⟩
  have leftEligible : CanonicalCenterRerootCursor mol root left :=
    occurrenceLigandCursor_eligible centerGenerated leftMember
  have rightEligible : CanonicalCenterRerootCursor mol root right :=
    occurrenceLigandCursor_eligible centerGenerated rightMember
  exact compareBranch_rule2_fuel_bound mol profile root rootBound wellFormed (bonding root)
    centerGenerated available leftEligible rightEligible

end RawFramedConstitutionalFuelClosure

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalFuelClosure.profile_center_generated
assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalFuelClosure.compareBranch?_exists_of_support
assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalFuelClosure.compareBranch_rule2_fuel_bound
assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalFuelClosure.compareBranch_rule2_of_admitted_profile
