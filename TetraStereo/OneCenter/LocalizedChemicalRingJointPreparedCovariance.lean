import TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts
import TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000











































namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance

open LocalizedGenericMarkedRecalculation
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingPreparedContextFacts (preparedChildrenUnder_keys_nodup preparedFacts_keys_nodup)
open LocalizedChemicalRingMultiMarkRecursion (MultiOperations markedReadingJoint?)
open LocalizedChemicalRingSenseTransport (OrdinaryRel ordinaryRel_some_some ordinaryRel_some_none
  ordinaryRel_none_some appendFacts_eq_ite keys_nodup_iff consensus_perm)
open LocalizedChemicalRingRelabel
open LocalizedMarkedReachableConfigurations (Reached reached_root reached_child)
open LocalizedMarkedReachedFrameNeighbors (SingleBonded reached_atom_valid)

abbrev Node := RawMolecule.CanonicalBranchNode

/-- The inherited-mark context: the marks carried into an occurrence, oldest first. -/
abbrev MarkContext := List Nat

variable {mol : RawMolecule} {σ : Nat → Nat}

/-- A relabelled auxiliary state: the mapped state has, up to order, the relabelled facts of the
source state. This is the occurrence-fact symmetry used throughout; it is never literal list
equality. -/
def StateRel (σ : Nat → Nat) (state' state : OccurrenceAuxState) : Prop :=
  state'.Perm (state.map (mapFact σ))

/-! ## The step interface -/

/-- Covariance of a prepared step at reached occurrences: child continuations related at every
relabelled context `L.map σ` make the step at the relabelled occurrence and context equal to the
step at the original occurrence under the pulled-back geometry. The incoming state pair is
arbitrary but related by `StateRel`, with duplicate-free source keys. -/
def PreparedStepMap (step : PreparedStep) (mol : RawMolecule) (σ : Nat → Nat) : Prop :=
  ∀ (node : Node), Reached mol node → ∀ (geom : Geometry) (M : MarkContext)
    (state state' : OccurrenceAuxState),
    StateRel σ state' state → (state.map (·.key)).Nodup →
    ∀ (under under' : MarkContext → OccurrenceAuxState),
      (∀ L : MarkContext, StateRel σ (under' (L.map σ)) (under L)) →
      step mol geom state' (M.map σ) (mapNode σ node) under' =
        step mol (pullback σ geom) state M node under

/-- The precise operations obligation: the joint current-context order is related by
`OrdinaryRel` at relabelled states/contexts, and the joint marked comparator transports its
ranked atom list along `σ`.  The concrete residual instance is
`PreparedCovariant mol (jointOperations input mol) σ`. -/
structure PreparedCovariant (mol : RawMolecule) (ops : MultiOperations) (σ : Nat → Nat) : Prop where
  contextOrder : ∀ (node : Node), Reached mol node → ∀ (atoms atoms' : List Nat),
    frameAtoms? mol node = some atoms →
    frameAtoms? mol (mapNode σ node) = some atoms' →
    ∀ (M : MarkContext) (state state' : OccurrenceAuxState),
      StateRel σ state' state → (state.map (·.key)).Nodup →
      OrdinaryRel σ atoms atoms'
        (ops.contextOrder state' (mapNode σ node) (M.map σ))
        (ops.contextOrder state node M)
  markedJoint : ∀ (node : Node), Reached mol node → ∀ (atoms atoms' : List Nat),
    frameAtoms? mol node = some atoms →
    frameAtoms? mol (mapNode σ node) = some atoms' →
    ∀ (L : MarkContext) (state state' : OccurrenceAuxState),
      StateRel σ state' state → (state.map (·.key)).Nodup → ∀ (s : Nat),
      (ops.markedJoint state' (mapNode σ node) (L.map σ) (σ s)).bind (rankedAtoms? atoms') =
        ((ops.markedJoint state node L s).bind (rankedAtoms? atoms)).map (List.map σ)

/-! ## Duplicate-free insertion transport -/

/-- A successful append returns a state whose occurrence keys are duplicate-free, provided the
incoming state is duplicate-free. -/
theorem appendFacts?_keys_nodup (added state : OccurrenceAuxState)
    (nodup : (state.map (·.key)).Nodup) {prepared : OccurrenceAuxState}
    (append : appendFacts? state added = some prepared) :
    (prepared.map (·.key)).Nodup := by
  rw [appendFacts_eq_ite added state nodup] at append
  by_cases combined : ((state ++ added).map (·.key)).Nodup
  · rw [if_pos combined] at append
    obtain rfl := Option.some.inj append
    exact combined
  · rw [if_neg combined] at append
    cases append

/-- Duplicate-free insertion transports along a relabelled state pair.  A failed append on one
side fails on the other; a successful append returns states related by `StateRel`. -/
theorem appendFacts?_transfer (sym : StructuralSymmetry mol σ)
    {state state' : OccurrenceAuxState} (srel : StateRel σ state' state)
    (snodup : (state.map (·.key)).Nodup)
    {added added' : OccurrenceAuxState} (arel : StateRel σ added' added) :
    (∀ (prepared : OccurrenceAuxState), appendFacts? state added = some prepared →
      ∃ prepared' : OccurrenceAuxState,
        appendFacts? state' added' = some prepared' ∧ StateRel σ prepared' prepared) ∧
    (appendFacts? state added = none → appendFacts? state' added' = none) := by
  have snodup' : (state'.map (·.key)).Nodup := (keys_nodup_iff sym srel).mpr snodup
  have allRel : StateRel σ (state' ++ added') (state ++ added) := by
    have := srel.append arel
    simpa only [StateRel, List.map_append] using this
  have allIff := keys_nodup_iff sym allRel
  constructor
  · intro prepared append
    rw [appendFacts_eq_ite added state snodup] at append
    by_cases combined : ((state ++ added).map (·.key)).Nodup
    · rw [if_pos combined] at append
      obtain rfl := Option.some.inj append
      rw [appendFacts_eq_ite added' state' snodup']
      rw [if_pos (allIff.mpr combined)]
      exact ⟨state' ++ added', rfl, allRel⟩
    · rw [if_neg combined] at append
      cases append
  · intro append
    rw [appendFacts_eq_ite added state snodup] at append
    by_cases combined : ((state ++ added).map (·.key)).Nodup
    · rw [if_pos combined] at append
      cases append
    · rw [appendFacts_eq_ite added' state' snodup']
      rw [if_neg (fun mapped => combined (allIff.mp mapped))]

/-! ## All-child generated-state transport -/

/-- The generated state of **all** canonical children transports along the relabelling, provided
the child continuations are related at every relabelled context.  The child permutation is the
accepted `children_map`; this is not an extra hypothesis. -/
theorem childrenUnder_map (mol : RawMolecule) (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (single : SingleBonded mol)
    (sub sub' : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState)
    (geom : Geometry) (state state' : OccurrenceAuxState) (node : Node) (M : MarkContext)
    (agree : ∀ child ∈ mol.canonicalChildren node,
      StateRel σ (sub' geom state' (M.map σ) (mapNode σ child))
        (sub (pullback σ geom) state M child)) :
    StateRel σ (childrenUnder mol sub' geom state' (mapNode σ node) (M.map σ))
      (childrenUnder mol sub (pullback σ geom) state node M) := by
  unfold StateRel childrenUnder
  rw [List.map_flatMap]
  refine ((children_map sym wellFormed unique single node).flatMap_right _).trans ?_
  rw [List.flatMap_map]
  apply List.Perm.flatMap_left
  intro child member
  exact agree child member

/-- The same all-child transport with the recursion's own fact continuation and an arbitrary
fact-transport hypothesis at the next depth.  The source context is the relocated context
`M.map σ`; the target context is the separate original context `M`. -/
theorem childrenUnder_factsOfStep_map (step : PreparedStep) (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (single : SingleBonded mol) (depth : Nat)
    (factsRel : ∀ (geom : Geometry) (M : MarkContext) (state state' : OccurrenceAuxState)
      (node : Node), Reached mol node → StateRel σ state' state →
      (state.map (·.key)).Nodup →
      StateRel σ (factsOfStep step mol depth geom state' (M.map σ) (mapNode σ node))
        (factsOfStep step mol depth (pullback σ geom) state M node))
    (node : Node) (reached : Reached mol node) (geom : Geometry)
    (state state' : OccurrenceAuxState) (M : MarkContext)
    (srel : StateRel σ state' state) (nodup : (state.map (·.key)).Nodup) :
    StateRel σ (childrenUnder mol (factsOfStep step mol depth) geom state' (mapNode σ node)
        (M.map σ))
      (childrenUnder mol (factsOfStep step mol depth) (pullback σ geom) state node M) :=
  childrenUnder_map mol sym wellFormed unique single
    (factsOfStep step mol depth) (factsOfStep step mol depth) geom state state' node M
    (fun child member => factsRel geom M state state' child
      (reached_child mol node child reached member) srel nodup)

/-! ## Marked-reading transport -/

/-- The joint marked reading at the relabelled occurrence and relabelled context equals the
reading at the original occurrence under the pulled-back geometry.  This is the exact consumer of
`PreparedCovariant.markedJoint`; no geometry or state is shared between the two sides. -/
theorem markedReadingJoint?_map (ops : MultiOperations) (cov : PreparedCovariant mol ops σ)
    (node : Node) (reached : Reached mol node) (atoms atoms' : List Nat)
    (frame : frameAtoms? mol node = some atoms)
    (frame' : frameAtoms? mol (mapNode σ node) = some atoms')
    (L : MarkContext) (state state' : OccurrenceAuxState) (srel : StateRel σ state' state)
    (nodup : (state.map (·.key)).Nodup) (s : Nat) (geom : Geometry) :
    markedReadingJoint? mol ops geom state' (mapNode σ node) (L.map σ) (σ s) =
      markedReadingJoint? mol ops (pullback σ geom) state node L s := by
  have h := cov.markedJoint node reached atoms atoms' frame frame' L state state' srel nodup s
  unfold markedReadingJoint?
  rw [frame, frame']
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases hm' : ops.markedJoint state' (mapNode σ node) (L.map σ) (σ s) with
  | none =>
      rw [hm', Option.bind_none] at h
      cases hm : ops.markedJoint state node L s with
      | none => rfl
      | some ranking =>
          rw [hm, Option.bind_some] at h
          simp only [Option.bind_none, Option.bind_some]
          cases hr : rankedAtoms? atoms ranking with
          | none => rfl
          | some ranked => rw [hr] at h; cases h
  | some ranking' =>
      rw [hm', Option.bind_some] at h
      cases hm : ops.markedJoint state node L s with
      | none =>
          rw [hm, Option.bind_none, Option.map_none] at h
          simp only [Option.bind_some, Option.bind_none, h]
      | some ranking =>
          rw [hm, Option.bind_some] at h
          simp only [Option.bind_some]
          cases hr : rankedAtoms? atoms ranking with
          | none => rw [hr, Option.map_none] at h; rw [h]; rfl
          | some ranked =>
              rw [hr, Option.map_some] at h
              rw [h]
              simp [readback_map]

/-- A fallback at mark `s` uses the separate extended state generated at `M ++ [s]`; its
transport therefore pairs the relabelled extended state at `(M ++ [s]).map σ` with the original
extended state at `M ++ [s]`, never with the `M`-state. -/
theorem evaluateFallback?_map (ops : MultiOperations) (sym : StructuralSymmetry mol σ)
    (cov : PreparedCovariant mol ops σ)
    (node : Node) (reached : Reached mol node) (atoms atoms' : List Nat)
    (frame : frameAtoms? mol node = some atoms)
    (frame' : frameAtoms? mol (mapNode σ node) = some atoms')
    (M : MarkContext) (state state' : OccurrenceAuxState) (srel : StateRel σ state' state)
    (nodup : (state.map (·.key)).Nodup)
    (under under' : MarkContext → OccurrenceAuxState)
    (hunder : ∀ L : MarkContext, StateRel σ (under' (L.map σ)) (under L))
    (s : Nat) (geom : Geometry) :
    evaluateFallback? mol ops geom state' (mapNode σ node) (M.map σ) under' (σ s) =
      evaluateFallback? mol ops (pullback σ geom) state node M under s := by
  have transfer := appendFacts?_transfer sym srel nodup (hunder (M ++ [s]))
  have hargs : (M ++ [s]).map σ = M.map σ ++ [σ s] := by simp
  unfold evaluateFallback?
  rw [← hargs]
  cases happ : appendFacts? state (under (M ++ [s])) with
  | none =>
      have happ' := transfer.2 happ
      rw [happ']
      rfl
  | some temp =>
      obtain ⟨temp', happ', trel⟩ := transfer.1 temp happ
      have tnodup := appendFacts?_keys_nodup (under (M ++ [s])) state nodup happ
      rw [happ']
      simp only [Option.bind_eq_bind, Option.bind_some]
      exact markedReadingJoint?_map ops cov node reached atoms atoms' frame frame'
        (M ++ [s]) temp temp' trel tnodup s geom

/-! ## Descriptor transport -/

/-- Descriptor transport from the relabelled occurrence to the original occurrence.  The two
mirror branches are evaluated separately: the source uses `geom` / `mirror geom`, the target uses
`pullback σ geom` / `mirror (pullback σ geom)`, and the latter is definitionally
`pullback σ (mirror geom)`.  The result is equality of descriptors, because the descriptor itself
is an index-derived optional value; occurrence facts are only transported up to permutation. -/
theorem descriptorWithPrepared_map (step : PreparedStep) (stepMap : PreparedStepMap step mol σ)
    (geom : Geometry) (M : MarkContext) (state state' : OccurrenceAuxState) (node : Node)
    (reached : Reached mol node) (srel : StateRel σ state' state)
    (nodup : (state.map (·.key)).Nodup)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState)
    (children : ∀ (g : Geometry) (L : MarkContext),
      StateRel σ (childrenUnder mol sub g state' (mapNode σ node) (L.map σ))
        (childrenUnder mol sub (pullback σ g) state node L)) :
    descriptorWithPrepared step mol geom state' (M.map σ) (mapNode σ node) sub =
      descriptorWithPrepared step mol (pullback σ geom) state M node sub := by
  unfold descriptorWithPrepared
  rw [stepMap node reached geom M state state' srel nodup
        (childrenUnder mol sub (pullback σ geom) state node)
        (childrenUnder mol sub geom state' (mapNode σ node)) (children geom),
      stepMap node reached (mirror geom) M state state' srel nodup
        (childrenUnder mol sub (mirror (pullback σ geom)) state node)
        (childrenUnder mol sub (mirror geom) state' (mapNode σ node)) (children (mirror geom))]
  rfl

/-- Permutation of the generated occurrence facts under relabelling, for every depth, geometry,
inherited context and reached occurrence, with an arbitrary related incoming state pair.  The
source context is `M.map σ` and the target context is `M`; the fallback contexts are transported
by `evaluateFallback?_map`, which keeps `M ++ [s]` and its relabelled image paired. -/
theorem factsOfStep_map (step : PreparedStep) (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (single : SingleBonded mol) (stepMap : PreparedStepMap step mol σ) :
    ∀ (depth : Nat) (geom : Geometry) (M : MarkContext) (state state' : OccurrenceAuxState)
      (node : Node), Reached mol node → StateRel σ state' state →
      (state.map (·.key)).Nodup →
      StateRel σ (factsOfStep step mol depth geom state' (M.map σ) (mapNode σ node))
        (factsOfStep step mol depth (pullback σ geom) state M node) := by
  intro depth
  induction depth with
  | zero =>
      intro geom M state state' node reached srel nodup
      exact List.Perm.refl _
  | succ depth ih =>
      intro geom M state state' node reached srel nodup
      have children : ∀ (g : Geometry) (L : MarkContext),
          StateRel σ (childrenUnder mol (factsOfStep step mol depth) g state'
              (mapNode σ node) (L.map σ))
            (childrenUnder mol (factsOfStep step mol depth) (pullback σ g) state node L) :=
        fun g L => childrenUnder_factsOfStep_map step sym wellFormed unique single depth
          (fun geom M state state' node => ih geom M state state' node) node reached g state
          state' L srel nodup
      have head : descriptorOfStep step mol depth geom state' (M.map σ) (mapNode σ node) =
          descriptorOfStep step mol depth (pullback σ geom) state M node := by
        unfold descriptorOfStep
        exact descriptorWithPrepared_map step stepMap geom M state state' node reached srel nodup
          (factsOfStep step mol depth) children
      unfold StateRel
      rw [factsOfStep_succ, factsOfStep_succ, List.map_append, head]
      refine List.Perm.append ?_ (children geom M)
      apply List.Perm.of_eq
      rw [List.map_map]
      exact List.map_congr_left (fun d _ => factOf_map σ node d)

/-- Descriptor transport for the prepared step at every depth, with the recursion's own
all-child continuation. -/
theorem descriptorOfStep_map (step : PreparedStep) (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (single : SingleBonded mol) (stepMap : PreparedStepMap step mol σ)
    (depth : Nat) (geom : Geometry) (M : MarkContext) (state state' : OccurrenceAuxState)
    (node : Node) (reached : Reached mol node) (srel : StateRel σ state' state)
    (nodup : (state.map (·.key)).Nodup) :
    descriptorOfStep step mol depth geom state' (M.map σ) (mapNode σ node) =
      descriptorOfStep step mol depth (pullback σ geom) state M node := by
  unfold descriptorOfStep
  exact descriptorWithPrepared_map step stepMap geom M state state' node reached srel nodup
    (factsOfStep step mol depth)
    (fun g L => childrenUnder_factsOfStep_map step sym wellFormed unique single depth
      (factsOfStep_map step sym wellFormed unique single stepMap depth) node reached g state
      state' L srel nodup)

/-! ## The concrete prepared step -/

/-- The accepted prepared step is `PreparedStepMap` as soon as the joint operations are
`PreparedCovariant`.  The comparison branch uses `OrdinaryRel`; the tied branch uses the joint
marked-reading transport at the separate extended context and reuses the accepted append transfer
for duplicate-free insertion.  All child states are handled by `childrenUnder_factsOfStep_map`. -/
theorem rawStepPrepared?_stepMap (ops : MultiOperations) (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (single : SingleBonded mol) (cov : PreparedCovariant mol ops σ) :
    PreparedStepMap (rawStepPrepared? ops) mol σ := by
  intro node reached geom M state state' srel snodup under under' hunder
  cases frame : frameAtoms? mol node with
  | none =>
      have frame' := frameAtoms_map_none sym wellFormed unique single node frame
        (reached_atom_valid mol wellFormed node reached)
      simp [rawStepPrepared?, frame, frame']
  | some atoms =>
      obtain ⟨atoms', frame', atomsPerm⟩ :=
        frameAtoms_map_some sym wellFormed unique single node atoms frame
          (reached_atom_valid mol wellFormed node reached)
      have transfer := appendFacts?_transfer sym srel snodup (hunder M)
      cases happ : appendFacts? state (under M) with
      | none =>
          have happ' := transfer.2 happ
          rw [rawStepPrepared?_none_of_appendFails ops mol geom state' (M.map σ)
                (mapNode σ node) under' atoms' frame' happ',
              rawStepPrepared?_none_of_appendFails ops mol (pullback σ geom) state M node under
                atoms frame happ]
      | some prepared =>
          obtain ⟨prepared', happ', prel⟩ := transfer.1 prepared happ
          have pnodup := appendFacts?_keys_nodup (under M) state snodup happ
          have relOrd := cov.contextOrder node reached atoms atoms' frame frame' M prepared
            prepared' prel pnodup
          rw [rawStepPrepared?_compares_at_prepared ops mol geom state' (M.map σ)
                (mapNode σ node) under' atoms' prepared' frame' happ',
              rawStepPrepared?_compares_at_prepared ops mol (pullback σ geom) state M node under
                atoms prepared frame happ]
          unfold comparisonAt?
          cases hord : ops.contextOrder prepared node M with
          | none =>
              cases hord' : ops.contextOrder prepared' (mapNode σ node) (M.map σ) with
              | none => rfl
              | some result' =>
                  rw [hord', hord, ordinaryRel_some_none] at relOrd
                  exact relOrd.elim
          | some result =>
              obtain ⟨sorted, adjacent⟩ := result
              cases hord' : ops.contextOrder prepared' (mapNode σ node) (M.map σ) with
              | none =>
                  rw [hord', hord, ordinaryRel_none_some] at relOrd
                  exact relOrd.elim
              | some result' =>
                  obtain ⟨sorted', adjacent'⟩ := result'
                  rw [hord', hord, ordinaryRel_some_some] at relOrd
                  obtain ⟨consistentEq, strictEq, atomsAtEq, eligiblePerm⟩ := relOrd
                  dsimp only
                  have nodupIff : atoms'.Nodup ↔ atoms.Nodup :=
                    atomsPerm.nodup_iff.trans
                      ⟨List.Nodup.of_map σ, fun h => h.map sym.injective⟩
                  by_cases bad : ¬ atoms.Nodup ∨ consistent adjacent = false
                  · have bad' : ¬ atoms'.Nodup ∨ consistent adjacent' = false := by
                      rw [nodupIff, consistentEq]
                      exact bad
                    rw [if_pos bad', if_pos bad]
                  · have bad' : ¬ (¬ atoms'.Nodup ∨ consistent adjacent' = false) := by
                      rw [nodupIff, consistentEq]
                      exact bad
                    rw [if_neg bad', if_neg bad]
                    by_cases strictH : strict adjacent = true
                    · have strictH' : strict adjacent' = true := by
                        rw [strictEq]
                        exact strictH
                      rw [if_pos strictH', if_pos strictH, atomsAtEq strictH]
                      cases h : atomsAt? atoms sorted with
                      | none => rfl
                      | some ranked => simp [readback_map]
                    · have strictH' : ¬ strict adjacent' = true := by
                        rw [strictEq]
                        exact strictH
                      rw [if_neg strictH', if_neg strictH]
                      rw [consensus_perm (eligiblePerm.map _), List.map_map]
                      congr 1
                      apply List.map_congr_left
                      intro s _
                      exact evaluateFallback?_map ops sym cov node
                        reached atoms atoms' frame frame' M state state' srel snodup under
                        under' hunder s geom

/-! ## The concrete prepared-context recursion -/

/-- Permutation of the generated prepared facts under relabelling, at every depth, geometry,
inherited context and reached occurrence, for an arbitrary related incoming state pair. -/
theorem preparedFacts_map (ops : MultiOperations) (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (single : SingleBonded mol) (cov : PreparedCovariant mol ops σ) :
    ∀ (depth : Nat) (geom : Geometry) (M : MarkContext) (state state' : OccurrenceAuxState)
      (node : Node), Reached mol node → StateRel σ state' state →
      (state.map (·.key)).Nodup →
      StateRel σ (preparedFacts mol ops depth geom state' (M.map σ) (mapNode σ node))
        (preparedFacts mol ops depth (pullback σ geom) state M node) :=
  factsOfStep_map (rawStepPrepared? ops) sym wellFormed unique single
    (rawStepPrepared?_stepMap ops sym wellFormed unique single cov)

/-- The same prepared-facts permutation at the actual incoming empty state `[]`. -/
theorem preparedFacts_map_empty (ops : MultiOperations) (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (single : SingleBonded mol) (cov : PreparedCovariant mol ops σ)
    (depth : Nat) (geom : Geometry) (M : MarkContext) (node : Node)
    (reached : Reached mol node) :
    StateRel σ (preparedFacts mol ops depth geom [] (M.map σ) (mapNode σ node))
      (preparedFacts mol ops depth (pullback σ geom) [] M node) :=
  preparedFacts_map ops sym wellFormed unique single cov depth geom M [] [] node reached
    (List.Perm.refl _) List.nodup_nil

/-- Transport of the generated state of **all** canonical children at the actual incoming empty
state.  The mapped state is paired with the original state at the separate original context `M`,
and its own extended contexts are `M ++ [s]` on the original side. -/
theorem preparedChildrenUnder_map (ops : MultiOperations) (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (single : SingleBonded mol) (cov : PreparedCovariant mol ops σ)
    (depth : Nat) (geom : Geometry) (M : MarkContext) (node : Node)
    (reached : Reached mol node) :
    StateRel σ (childrenUnder mol (preparedFacts mol ops depth) geom [] (mapNode σ node)
        (M.map σ))
      (childrenUnder mol (preparedFacts mol ops depth) (pullback σ geom) [] node M) :=
  childrenUnder_map mol sym wellFormed unique single
    (preparedFacts mol ops depth) (preparedFacts mol ops depth) geom [] [] node M
    (fun child member => preparedFacts_map_empty ops sym wellFormed unique single cov depth geom M
      child (reached_child mol node child reached member))

/-- Key uniqueness of the relabelled all-child generated state, derived from the accepted
original uniqueness theorem plus the permutation transport; it is not a recursion premise. -/
theorem preparedChildrenUnder_keys_nodup_map (ops : MultiOperations)
    (sym : StructuralSymmetry mol σ) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (single : SingleBonded mol)
    (cov : PreparedCovariant mol ops σ) (depth : Nat) (geom : Geometry)
    (M : MarkContext) (node : Node) (reached : Reached mol node) :
    ((childrenUnder mol (preparedFacts mol ops depth) geom [] (mapNode σ node)
        (M.map σ)).map (·.key)).Nodup :=
  (keys_nodup_iff sym (preparedChildrenUnder_map ops sym wellFormed unique single cov depth geom M
    node reached)).mpr
    (preparedChildrenUnder_keys_nodup mol ops wellFormed single unique depth
      (pullback σ geom) [] node M)

/-- Key uniqueness of the relabelled generated facts at the actual incoming empty state, also
derived rather than assumed. -/
theorem preparedFacts_keys_nodup_map (ops : MultiOperations) (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (single : SingleBonded mol) (cov : PreparedCovariant mol ops σ)
    (depth : Nat) (geom : Geometry) (M : MarkContext) (node : Node)
    (reached : Reached mol node) :
    ((preparedFacts mol ops depth geom [] (M.map σ) (mapNode σ node)).map (·.key)).Nodup :=
  (keys_nodup_iff sym (preparedFacts_map_empty ops sym wellFormed unique single cov depth geom M
    node reached)).mpr
    (preparedFacts_keys_nodup mol ops wellFormed single unique depth (pullback σ geom) [] M node)

/-- Descriptor transport for the concrete prepared evaluator at every depth and related incoming
state pair. -/
theorem preparedDescriptor_map (ops : MultiOperations) (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (single : SingleBonded mol) (cov : PreparedCovariant mol ops σ)
    (depth : Nat) (geom : Geometry) (M : MarkContext) (state state' : OccurrenceAuxState)
    (node : Node) (reached : Reached mol node) (srel : StateRel σ state' state)
    (nodup : (state.map (·.key)).Nodup) :
    preparedDescriptor? mol ops depth geom state' (M.map σ) (mapNode σ node) =
      preparedDescriptor? mol ops depth (pullback σ geom) state M node := by
  unfold preparedDescriptor?
  exact descriptorOfStep_map (rawStepPrepared? ops) sym wellFormed unique single
    (rawStepPrepared?_stepMap ops sym wellFormed unique single cov) depth geom M state state'
    node reached srel nodup

/-- Descriptor transport at the actual incoming empty state `[]` and empty inherited context
`[]`; this is the root descriptor form used by the physical joint-orientation consumer. -/
theorem preparedDescriptor_map_empty (ops : MultiOperations) (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (single : SingleBonded mol) (cov : PreparedCovariant mol ops σ)
    (depth : Nat) (geom : Geometry) (M : MarkContext) (node : Node)
    (reached : Reached mol node) :
    preparedDescriptor? mol ops depth geom [] (M.map σ) (mapNode σ node) =
      preparedDescriptor? mol ops depth (pullback σ geom) [] M node :=
  preparedDescriptor_map ops sym wellFormed unique single cov depth geom M [] [] node reached
    (List.Perm.refl _) List.nodup_nil

/-- Covariance of the prepared centre assignment at the actual root: the descriptor assigned to
the relabelled centre under the relabelled geometry equals the descriptor assigned to the
original centre under the pulled-back geometry.  Both roots have the same structural depth, and
both run with the actual incoming empty state `[]`. -/
theorem preparedAssignCenter?_map (ops : MultiOperations) (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (single : SingleBonded mol) (cov : PreparedCovariant mol ops σ)
    (geom : Geometry) (center : Nat) (valid : center < mol.atomCount) :
    preparedAssignCenter? mol ops geom (σ center) =
      preparedAssignCenter? mol ops (pullback σ geom) center := by
  have depthEq : structuralDepth mol (canonicalCenterRoot (σ center)) =
      structuralDepth mol (canonicalCenterRoot center) := by
    unfold structuralDepth
    rw [← mapNode_canonicalCenterRoot σ center, mapNode_history]
    simp
  have h := preparedDescriptor_map_empty ops sym wellFormed unique single cov
    (structuralDepth mol (canonicalCenterRoot center)) geom [] (canonicalCenterRoot center)
    (reached_root mol center valid)
  unfold preparedAssignCenter?
  rw [depthEq, ← mapNode_canonicalCenterRoot σ center]
  simpa [preparedDescriptor?] using h

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.StateRel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.PreparedStepMap
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.PreparedCovariant
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.appendFacts?_keys_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.appendFacts?_transfer
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.childrenUnder_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.childrenUnder_factsOfStep_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.markedReadingJoint?_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.evaluateFallback?_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.descriptorWithPrepared_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.factsOfStep_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.descriptorOfStep_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.rawStepPrepared?_stepMap
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.preparedFacts_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.preparedFacts_map_empty
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.preparedChildrenUnder_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.preparedChildrenUnder_keys_nodup_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.preparedFacts_keys_nodup_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.preparedDescriptor_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.preparedDescriptor_map_empty
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance.preparedAssignCenter?_map
