import TetraStereo.OneCenter.Rule4bOccurrenceClassification
import TetraStereo.OneCenter.OfficialUniformTerminalLigandTie
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open Classical

/-!
# Typed structural non-bearing facts for Rule-4b occurrence selection

`Rule4bOccurrenceClassification` deliberately keeps every real-atom occurrence without a recorded
auxiliary fact `unavailable`: the absence of an `@`/`@@` annotation, or of a complete four-ligand
occurrence frame, is evaluator unproductivity, not a nonchirality verdict.  This module supplies explicit structural evidence for operational refusal or a terminal-arm
comparison tie. A proposed callback maps that evidence to `some none`; descriptor-nonbearing
soundness of that policy remains a separate obligation.

Two independent structural reasons are implemented.

* `StructuralNonbearingFact.terminalVertex` -- the occurrence's centre has fewer than four
  lone-pair-augmented ligand positions, so `occurrenceLigandFrame?` is `none` and `occurrenceFact?`
  is `none` at every fuel and auxiliary state.  A genuine terminal (degree at most one) vertex is
  the motivating case: it has at most two lone-pair-augmented positions.  No annotation is read.
* `StructuralNonbearingFact.uniformTerminalArms` -- two distinct ligand positions of the occurrence
  are real bonded atoms whose actual official `rootFromEdge` branches are terminal under the actual
  `officialCIPChildren` enumerator and whose atomic number and exact Rule-2 isotope mass agree.
  `uniformTerminalArmData_completedTie` feeds this data to
  `MoleculeGraph.compareRuleMajorRootsWithFuel_terminal_tie`, obtaining an actual completed
  comparison certificate with `outcome = Ordering.eq` at every fuel and empty rule contexts.

The producer `occurrenceStructuralNonbearingFact?` inspects only molecule geometry: provenance,
`ligandsWithLonePair`, the actual `toMoleculeGraph` adjacency and official children enumerator, and
the exact atomic-number and Rule-2 mass projections.  It never mentions `OccurrenceAuxState`,
`occurrenceFact?`, `occurrenceChiralityClass`, or a desired classifier output.

The callback `pre4bNonbearingCallback?` is a proposed Rule-4b policy, currently unconnected to
production.  It keeps every existing
selector verdict unchanged and upgrades `none` to `some none` only when a typed fact exists.  In
particular:

* a real occurrence with a state fact keeps its uppercase/lowercase verdict;
* a non-real occurrence keeps the existing structural `knownNonchiral`/`some none` route;
* every other real occurrence -- including every real occurrence without one of the two geometric
  facts, and every real occurrence with no tetrahedral annotation -- stays `none` (unknown);
* no `some (some descriptor)` can be introduced.

Existing `knownNonchiral` verdicts retain their classifier meaning. The new structural facts
establish only their stated operational consequences; they do not yet prove absence of an
uppercase descriptor. No case is derived from annotation absence alone.
-/

/-! ## 1. Local atomic-number bridge

`RawMolecule.atomZAt` is defined through the parse-list lookup `listGet?`, while
`toMoleculeGraph.atomZ` uses `List.get` on `Fin atomCount`.  The bridge below reuses the existing
`listGet?_eq_some_get` lemma from `ChemistrySemantics`, which is already in the import closure, so
the module introduces no duplicate declaration and no additional production import.

The existing lemma is stated in the same direction, so the two definitional unfoldings meet
syntactically. -/
theorem atomZAt_eq_toMoleculeGraph_atomZ_of_lt (mol : RawMolecule) (idx : ℕ)
    (hBound : idx < mol.atomCount) :
    mol.atomZAt idx = mol.toMoleculeGraph.atomZ ⟨idx, hBound⟩ := by
  unfold RawMolecule.atomZAt RawMolecule.atomAt?
  rw [listGet?_eq_some_get mol.atoms ⟨idx, hBound⟩]
  rfl

/-- The atomic number of a real atom in the official molecule graph is the production atom lookup. -/
theorem toMoleculeGraph_atomZ_eq_atomZAt (mol : RawMolecule) (idx : ℕ)
    (hBound : idx < mol.atomCount) :
    mol.toMoleculeGraph.atomZ ⟨idx, hBound⟩ = mol.atomZAt idx :=
  (atomZAt_eq_toMoleculeGraph_atomZ_of_lt mol idx hBound).symm

/-! ## 2. The two structural kinds and their proof-carrying data -/

/-- The structural reasons for non-bearing status implemented by this module. -/
inductive StructuralNonbearingKind where
  | terminalVertex
  | uniformTerminalArms
  deriving DecidableEq, Repr

/-- Proof-carrying data for two identical terminal ligand arms of one occurrence.

The centre and both arms are real atoms of the same molecule.  Both arms are actual ligand positions
of `cursor.node.atom`, both are adjacent to the centre in the official molecule graph, and both
official `rootFromEdge` branches are terminal under the actual `officialCIPChildren` enumerator.
The arms agree on atomic number and on the exact Rule-2 isotope mass.  `distinct` prevents the fact
from being vacuous on a single ligand position.

This structure is deliberately *not* a classifier verdict: it records actual graph and official
digraph computations only. -/
structure UniformTerminalArmData (mol : RawMolecule)
    (cursor : CanonicalRerootCursor) where
  /-- The occurrence centre is a real atom index. -/
  centerBound : cursor.node.atom < mol.atomCount
  /-- First arm atom index. -/
  left : ℕ
  /-- Second arm atom index. -/
  right : ℕ
  leftBound : left < mol.atomCount
  rightBound : right < mol.atomCount
  /-- The first arm occupies a ligand position of the centre. -/
  leftMem : left ∈ mol.ligandsWithLonePair cursor.node.atom
  /-- The second arm occupies a ligand position of the centre. -/
  rightMem : right ∈ mol.ligandsWithLonePair cursor.node.atom
  /-- The two arms are distinct ligand positions. -/
  distinct : left ≠ right
  /-- The first arm is actually bonded to the centre. -/
  leftAdj : mol.toMoleculeGraph.Adj ⟨cursor.node.atom, centerBound⟩ ⟨left, leftBound⟩
  /-- The second arm is actually bonded to the centre. -/
  rightAdj : mol.toMoleculeGraph.Adj ⟨cursor.node.atom, centerBound⟩ ⟨right, rightBound⟩
  /-- The first official root branch is terminal. -/
  leftTerminal : mol.toMoleculeGraph.officialCIPChildren
    (OfficialCIPNode.rootFromEdge ⟨cursor.node.atom, centerBound⟩ ⟨left, leftBound⟩) = []
  /-- The second official root branch is terminal. -/
  rightTerminal : mol.toMoleculeGraph.officialCIPChildren
    (OfficialCIPNode.rootFromEdge ⟨cursor.node.atom, centerBound⟩ ⟨right, rightBound⟩) = []
  /-- Equal atomic numbers (Rule 1a). -/
  atomicNumberEq : mol.atomZAt left = mol.atomZAt right
  /-- Equal exact Rule-2 isotope masses. -/
  isotopeMassEq : mol.atomMassAt left = mol.atomMassAt right

/-- A structural non-bearing fact for one occurrence.

Both constructors require the occurrence to be a real atom: non-real canonical duplicate/phantom
nodes already have the independent structural route in `Rule4bOccurrenceClassification`.  Neither
constructor mentions an auxiliary state, the occurrence evaluator, or a classifier verdict. -/
inductive StructuralNonbearingFact (mol : RawMolecule)
    (cursor : CanonicalRerootCursor) : Type where
  /-- The centre has no complete four-ligand occurrence frame.  This covers terminal vertices. -/
  | terminalVertex
      (realProvenance :
        cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
      (ligandCountLtFour :
        (mol.ligandsWithLonePair cursor.node.atom).length < 4) :
      StructuralNonbearingFact mol cursor
  /-- Two distinct terminal ligand positions are constitutionally indistinguishable. -/
  | uniformTerminalArms
      (realProvenance :
        cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
      (data : UniformTerminalArmData mol cursor) :
      StructuralNonbearingFact mol cursor

namespace StructuralNonbearingFact

/-- The kind tag of a structural fact. -/
def kind {mol : RawMolecule} {cursor : CanonicalRerootCursor} :
    StructuralNonbearingFact mol cursor → StructuralNonbearingKind
  | terminalVertex _ _ => StructuralNonbearingKind.terminalVertex
  | uniformTerminalArms _ _ => StructuralNonbearingKind.uniformTerminalArms

end StructuralNonbearingFact

/-! ## 3. The geometric producer -/

/-- Produce a structural non-bearing fact from actual geometry, independently of any classifier
output.

The producer inspects only:

* the occurrence provenance (real atom versus canonical duplicate/phantom);
* the lone-pair-augmented ligand count of the centre;
* whether the actual identical-terminal-arms data exists.

It never inspects `occurrenceTetrahedralCandidate?`, `state.factAt?`, `occurrenceFact?`, or
`occurrenceChiralityClass`.  Uniform-arm existence is a `Prop`; the producer is noncomputable because
it selects an arbitrary witness with `Classical.choice`.  The selected witness is stored inside the
fact, so downstream validity proofs still use the actual geometry. -/
noncomputable def occurrenceStructuralNonbearingFact?
    (mol : RawMolecule) (cursor : CanonicalRerootCursor) :
    Option (StructuralNonbearingFact mol cursor) :=
  if hReal : cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom then
    if hCount : (mol.ligandsWithLonePair cursor.node.atom).length < 4 then
      some (.terminalVertex hReal hCount)
    else if hArms : Nonempty (UniformTerminalArmData mol cursor) then
      some (.uniformTerminalArms hReal (Classical.choice hArms))
    else none
  else none

/-- The terminal-vertex branch of the producer is exact. -/
theorem occurrenceStructuralNonbearingFact?_eq_some_terminalVertex
    (mol : RawMolecule) (cursor : CanonicalRerootCursor)
    (hReal : cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hCount : (mol.ligandsWithLonePair cursor.node.atom).length < 4) :
    occurrenceStructuralNonbearingFact? mol cursor =
      some (.terminalVertex hReal hCount) := by
  unfold occurrenceStructuralNonbearingFact?
  rw [dif_pos hReal]
  rw [dif_pos hCount]

/-- Non-real occurrences never receive a structural fact from this producer. -/
theorem occurrenceStructuralNonbearingFact?_eq_none_of_nonReal
    (mol : RawMolecule) (cursor : CanonicalRerootCursor)
    (hNonReal : cursor.node.provenance ≠
      RawMolecule.CanonicalNodeProvenance.realAtom) :
    occurrenceStructuralNonbearingFact? mol cursor = none := by
  simp [occurrenceStructuralNonbearingFact?, hNonReal]

/-- The uniform-terminal-arms branch produces a fact whenever the ligand count does not already
trigger the terminal-vertex branch. -/
theorem occurrenceStructuralNonbearingFact?_isSome_of_uniformTerminalArms
    (mol : RawMolecule) (cursor : CanonicalRerootCursor)
    (hReal : cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hArms : Nonempty (UniformTerminalArmData mol cursor))
    (hCount : ¬ (mol.ligandsWithLonePair cursor.node.atom).length < 4) :
    (occurrenceStructuralNonbearingFact? mol cursor).isSome = true := by
  simp [occurrenceStructuralNonbearingFact?, hReal, hCount, hArms]

/-- **Exact unavailability characterization.**  The producer returns `none` exactly when there is
no real provenance plus geometric reason.  The right-hand side mentions neither an auxiliary state
nor a tetrahedral annotation. -/
theorem occurrenceStructuralNonbearingFact?_eq_none_iff
    (mol : RawMolecule) (cursor : CanonicalRerootCursor) :
    occurrenceStructuralNonbearingFact? mol cursor = none ↔
      ¬ (cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
        ((mol.ligandsWithLonePair cursor.node.atom).length < 4 ∨
          Nonempty (UniformTerminalArmData mol cursor))) := by
  by_cases hReal : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom
  · by_cases hCount : (mol.ligandsWithLonePair cursor.node.atom).length < 4
    · simp [occurrenceStructuralNonbearingFact?, hReal, hCount]
    · by_cases hArms : Nonempty (UniformTerminalArmData mol cursor) <;>
        simp [occurrenceStructuralNonbearingFact?, hReal, hCount, hArms]
  · simp [occurrenceStructuralNonbearingFact?, hReal]

/-- **Exact availability characterization.**  A structural fact exists exactly under one of the two
geometric alternatives. -/
theorem occurrenceStructuralNonbearingFact?_isSome_iff
    (mol : RawMolecule) (cursor : CanonicalRerootCursor) :
    (occurrenceStructuralNonbearingFact? mol cursor).isSome = true ↔
      cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
        ((mol.ligandsWithLonePair cursor.node.atom).length < 4 ∨
          Nonempty (UniformTerminalArmData mol cursor)) := by
  by_cases hReal : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom
  · by_cases hCount : (mol.ligandsWithLonePair cursor.node.atom).length < 4
    · have hSome : occurrenceStructuralNonbearingFact? mol cursor =
          some (.terminalVertex hReal hCount) :=
        occurrenceStructuralNonbearingFact?_eq_some_terminalVertex mol cursor hReal hCount
      simp [hSome, hReal, hCount]
    · by_cases hArms : Nonempty (UniformTerminalArmData mol cursor)
      · have hSome : (occurrenceStructuralNonbearingFact? mol cursor).isSome = true :=
          occurrenceStructuralNonbearingFact?_isSome_of_uniformTerminalArms
            mol cursor hReal hArms hCount
        simp [hSome, hReal, hCount, hArms]
      · have hNone : occurrenceStructuralNonbearingFact? mol cursor = none := by
          simp [occurrenceStructuralNonbearingFact?, hReal, hCount, hArms]
        simp [hNone, hReal, hCount, hArms]
  · have hNone : occurrenceStructuralNonbearingFact? mol cursor = none :=
      occurrenceStructuralNonbearingFact?_eq_none_of_nonReal mol cursor hReal
    simp [hNone, hReal]

/-! ## 4. Terminal vertices force evaluator unproductivity

Fewer than four lone-pair-augmented ligand positions means `occurrenceLigandFrame?` cannot produce a
four-ligand frame.  The existing evaluator prerequisites then force `occurrenceFact? = none` at every
fuel and state.  This is *evaluator unproductivity plus a structural frame deficiency*, not an
annotation-based nonchirality claim. -/

/-- Fewer than four ligand positions force an absent occurrence frame. -/
theorem occurrenceLigandFrame?_eq_none_of_ligandCount_lt_four
    (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (hCount : (mol.ligandsWithLonePair node.atom).length < 4) :
    occurrenceLigandFrame? mol node = none := by
  have hne : (mol.ligandsWithLonePair node.atom).length ≠ 4 := by
    intro hEq
    rw [hEq] at hCount
    exact absurd hCount (by decide)
  have hbne : ((mol.ligandsWithLonePair node.atom).length != 4) = true :=
    bne_iff_ne.mpr hne
  simp [occurrenceLigandFrame?, hbne]

/-- The legacy evaluator cannot produce a fact for a centre with fewer than four ligand positions. -/
theorem legacyOccurrenceFact?_eq_none_of_ligandCount_lt_four
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (hCount : (mol.ligandsWithLonePair node.atom).length < 4) :
    legacyOccurrenceFact? mol fuel state node = none :=
  legacyOccurrenceFact?_eq_none_of_ligandFrame?_eq_none mol fuel state node
    (occurrenceLigandFrame?_eq_none_of_ligandCount_lt_four mol node hCount)

/-- The framed evaluator cannot produce a fact for a centre with fewer than four ligand positions. -/
theorem framedOccurrenceFact?_eq_none_of_ligandCount_lt_four
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (hCount : (mol.ligandsWithLonePair node.atom).length < 4) :
    framedOccurrenceFact? mol fuel state node = none :=
  framedOccurrenceFact?_eq_none_of_ligandFrame?_eq_none mol fuel state node
    (occurrenceLigandFrame?_eq_none_of_ligandCount_lt_four mol node hCount)

/-- The production occurrence evaluator cannot produce a fact for a centre with fewer than four
ligand positions. -/
theorem occurrenceFact?_eq_none_of_ligandCount_lt_four
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (hCount : (mol.ligandsWithLonePair node.atom).length < 4) :
    occurrenceFact? mol fuel state node = none :=
  occurrenceFact?_eq_none_of_ligandFrame?_eq_none mol fuel state node
    (occurrenceLigandFrame?_eq_none_of_ligandCount_lt_four mol node hCount)

/-! ## 5. Identical terminal arms produce a completed official tie

The proof below uses the actual `toMoleculeGraph`, the actual `officialCIPChildren` enumerator, and
the actual official comparison engine.  The empty Rule 3/4/5 contexts are justified by terminality:
there is nothing below either arm whose context could be nonempty. -/

/-- Two identical terminal arms yield an actual completed official comparison certificate with
outcome `Ordering.eq`, at every fuel and with empty rule contexts. -/
theorem uniformTerminalArmData_completedTie
    (mol : RawMolecule) (cursor : CanonicalRerootCursor)
    (data : UniformTerminalArmData mol cursor) (fuel : ℕ) :
    ∃ certificate : CIPTraceCertificate,
      mol.toMoleculeGraph.compareRuleMajorRootsWithFuel
        mol.toMoleculeGraph.officialCIPChildren fuel
        (OfficialCIPNode.rootFromEdge ⟨cursor.node.atom, data.centerBound⟩
          ⟨data.left, data.leftBound⟩)
        (OfficialCIPNode.rootFromEdge ⟨cursor.node.atom, data.centerBound⟩
          ⟨data.right, data.rightBound⟩)
        CIPRuleEngine.OfficialLigandRuleContext.empty
        CIPRuleEngine.OfficialLigandRuleContext.empty
        = some certificate ∧ certificate.outcome = Ordering.eq := by
  have hAtomic :
      (ofLex (mol.toMoleculeGraph.officialNodeAtomLabel
        (OfficialCIPNode.rootFromEdge ⟨cursor.node.atom, data.centerBound⟩
          ⟨data.left, data.leftBound⟩))).1 =
      (ofLex (mol.toMoleculeGraph.officialNodeAtomLabel
        (OfficialCIPNode.rootFromEdge ⟨cursor.node.atom, data.centerBound⟩
          ⟨data.right, data.rightBound⟩))).1 := by
    have hZ : mol.toMoleculeGraph.atomZ ⟨data.left, data.leftBound⟩ =
        mol.toMoleculeGraph.atomZ ⟨data.right, data.rightBound⟩ := by
      rw [toMoleculeGraph_atomZ_eq_atomZAt mol data.left data.leftBound,
        toMoleculeGraph_atomZ_eq_atomZAt mol data.right data.rightBound]
      exact data.atomicNumberEq
    simpa [MoleculeGraph.rawCIPAtomLabel, ofLex_toLex] using hZ
  have hMass :
      (ofLex (mol.toMoleculeGraph.officialNodeAtomLabel
        (OfficialCIPNode.rootFromEdge ⟨cursor.node.atom, data.centerBound⟩
          ⟨data.left, data.leftBound⟩))).2 =
      (ofLex (mol.toMoleculeGraph.officialNodeAtomLabel
        (OfficialCIPNode.rootFromEdge ⟨cursor.node.atom, data.centerBound⟩
          ⟨data.right, data.rightBound⟩))).2 := by
    have hm : mol.toMoleculeGraph.atomMass ⟨data.left, data.leftBound⟩ =
        mol.toMoleculeGraph.atomMass ⟨data.right, data.rightBound⟩ := by
      simpa using data.isotopeMassEq
    simpa [MoleculeGraph.rawCIPAtomLabel, ofLex_toLex] using hm
  have hDistance :
      (OfficialCIPNode.rootFromEdge (V := Fin mol.atomCount)
        ⟨cursor.node.atom, data.centerBound⟩
        ⟨data.left, data.leftBound⟩).rule1bRootDistance =
      (OfficialCIPNode.rootFromEdge (V := Fin mol.atomCount)
        ⟨cursor.node.atom, data.centerBound⟩
        ⟨data.right, data.rightBound⟩).rule1bRootDistance := by
    simp
  obtain ⟨certificate, hcomputed, houtcome⟩ :=
    mol.toMoleculeGraph.compareRuleMajorRootsWithFuel_terminal_tie
      mol.toMoleculeGraph.officialCIPChildren fuel
      (OfficialCIPNode.rootFromEdge ⟨cursor.node.atom, data.centerBound⟩
        ⟨data.left, data.leftBound⟩)
      (OfficialCIPNode.rootFromEdge ⟨cursor.node.atom, data.centerBound⟩
        ⟨data.right, data.rightBound⟩)
      data.leftTerminal data.rightTerminal hAtomic hMass hDistance
      CIPRuleEngine.OfficialLigandRuleContext.empty
      CIPRuleEngine.OfficialLigandRuleContext.empty rfl rfl
  exact ⟨certificate, hcomputed, houtcome⟩

/-! ## 6. Validity of the facts

The validity predicate is deliberately per-constructor: a terminal vertex is validated by evaluator
unproductivity at every fuel and state, while uniform terminal arms are validated by the completed
official comparison certificate above.  Neither predicate restates a desired classifier output. -/

namespace StructuralNonbearingFact

/-- Consequence predicate for a structural non-bearing fact.

* `terminalVertex`: the production occurrence evaluator returns `none` at every fuel and state.
* `uniformTerminalArms`: the actual official comparison of the two terminal root branches returns a
  completed certificate with outcome `Ordering.eq`. -/
abbrev Validated {mol : RawMolecule} {cursor : CanonicalRerootCursor}
    (fact : StructuralNonbearingFact mol cursor) : Prop :=
  match fact with
  | terminalVertex _realProvenance _ligandCountLtFour =>
      ∀ (fuel : ℕ) (state : OccurrenceAuxState),
        occurrenceFact? mol fuel state cursor.node = none
  | uniformTerminalArms _realProvenance data =>
      ∀ (fuel : ℕ), ∃ certificate : CIPTraceCertificate,
        mol.toMoleculeGraph.compareRuleMajorRootsWithFuel
          mol.toMoleculeGraph.officialCIPChildren fuel
          (OfficialCIPNode.rootFromEdge ⟨cursor.node.atom, data.centerBound⟩
            ⟨data.left, data.leftBound⟩)
          (OfficialCIPNode.rootFromEdge ⟨cursor.node.atom, data.centerBound⟩
            ⟨data.right, data.rightBound⟩)
          CIPRuleEngine.OfficialLigandRuleContext.empty
          CIPRuleEngine.OfficialLigandRuleContext.empty
          = some certificate ∧ certificate.outcome = Ordering.eq

/-- A terminal-vertex fact is validated by evaluator unproductivity. -/
theorem validated_of_terminalVertex {mol : RawMolecule} {cursor : CanonicalRerootCursor}
    (realProvenance : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom)
    (ligandCountLtFour : (mol.ligandsWithLonePair cursor.node.atom).length < 4) :
    (terminalVertex realProvenance ligandCountLtFour :
      StructuralNonbearingFact mol cursor).Validated := by
  change ∀ (fuel : ℕ) (state : OccurrenceAuxState),
    occurrenceFact? mol fuel state cursor.node = none
  intro fuel state
  exact occurrenceFact?_eq_none_of_ligandCount_lt_four mol fuel state cursor.node
    ligandCountLtFour

/-- A uniform-terminal-arms fact is validated by the completed official comparison certificate. -/
theorem validated_of_uniformTerminalArms {mol : RawMolecule} {cursor : CanonicalRerootCursor}
    (realProvenance : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom)
    (data : UniformTerminalArmData mol cursor) :
    (uniformTerminalArms realProvenance data :
      StructuralNonbearingFact mol cursor).Validated :=
  uniformTerminalArmData_completedTie mol cursor data

/-- Every structural non-bearing fact produced by this module carries its own actual-geometry
validation. -/
theorem validated {mol : RawMolecule} {cursor : CanonicalRerootCursor}
    (fact : StructuralNonbearingFact mol cursor) : fact.Validated := by
  cases fact with
  | terminalVertex realProvenance ligandCountLtFour =>
      exact validated_of_terminalVertex realProvenance ligandCountLtFour
  | uniformTerminalArms realProvenance data =>
      exact validated_of_uniformTerminalArms realProvenance data

end StructuralNonbearingFact

/-! ## 7. Evidence-level integration

`occurrenceAuxiliaryEvidenceWithStructural?` is the tri-state evidence resolver with one additional
candidate policy: when the existing resolver is `none`, a typed structural fact supplies `some none`;
the descriptor-nonbearing interpretation is not proved here.
The existing `some (some fact)` and `some none` cases pass through unchanged. -/

/-- Tri-state occurrence evidence extended by validated structural non-bearing facts.

The extra route is taken only when the existing resolver returns `none` (a real occurrence missing
from the auxiliary state) and the geometric producer returns an actual typed fact. -/
noncomputable def occurrenceAuxiliaryEvidenceWithStructural?
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) : Option (Option OccurrenceAuxFact) :=
  match occurrenceAuxiliaryEvidence? state cursor with
  | none =>
      match occurrenceStructuralNonbearingFact? mol cursor with
      | some _ => some none
      | none => none
  | evidence => evidence

/-- The selector classification is exactly the `Option (Option RS)` projection of the tri-state
auxiliary evidence.  This records the existing missing link explicitly. -/
theorem occurrenceSelectorChiralityClassification?_eq_toOptionOption_evidence
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) :
    occurrenceSelectorChiralityClassification? state cursor =
      OccurrenceChiralityClass.toOptionOption
        (occurrenceClassOfEvidence (occurrenceAuxiliaryEvidence? state cursor)) := by
  unfold occurrenceSelectorChiralityClassification? occurrenceChiralityClassification?
    occurrenceChiralityClass
  rfl

/-! ## 8. The planned pre-Rule-4b callback -/

/-- The planned pre-Rule-4b callback.

It consumes the existing selector classification and changes only its `none` case: when the selector
is `none` and an explicit validated structural fact exists, the callback returns `some none`.  All
other verdicts -- including `some none` from non-real provenance or a lowercase fact, and
`some (some descriptor)` from an actual uppercase fact -- pass through unchanged.

The callback therefore never invents an uppercase descriptor, and it never converts annotation
absence or evaluator failure into a nonchirality verdict. -/
noncomputable def pre4bNonbearingCallback?
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) : Option (Option RS) :=
  match occurrenceSelectorChiralityClassification? state cursor with
  | none =>
      match occurrenceStructuralNonbearingFact? mol cursor with
      | some _ => some none
      | none => none
  | verdict => verdict

/-- **Callback equals the extended tri-state evidence classification.**  The only new `some none`
route is an explicit structural fact at a real occurrence whose existing evidence was unavailable. -/
theorem pre4bNonbearingCallback?_eq_evidence
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) :
    pre4bNonbearingCallback? mol state cursor =
      OccurrenceChiralityClass.toOptionOption
        (occurrenceClassOfEvidence
          (occurrenceAuxiliaryEvidenceWithStructural? mol state cursor)) := by
  unfold pre4bNonbearingCallback?
  rw [occurrenceSelectorChiralityClassification?_eq_toOptionOption_evidence]
  unfold occurrenceAuxiliaryEvidenceWithStructural?
  cases hEvidence : occurrenceAuxiliaryEvidence? state cursor with
  | none =>
      cases hFact : occurrenceStructuralNonbearingFact? mol cursor with
      | none =>
          simp [occurrenceClassOfEvidence]
      | some fact =>
          simp [occurrenceClassOfEvidence]
  | some inner =>
      cases inner with
      | none => simp [occurrenceClassOfEvidence]
      | some fact =>
          cases hUpper : fact.uppercase <;>
            simp [occurrenceClassOfEvidence, hUpper]

/-! ### Exact callback behavior -/

/-- **No fabricated uppercase descriptors.**  The callback's `some (some descriptor)` verdicts are
exactly the selector's. -/
theorem pre4bNonbearingCallback?_eq_some_some_iff
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) (descriptor : RS) :
    pre4bNonbearingCallback? mol state cursor = some (some descriptor) ↔
      occurrenceSelectorChiralityClassification? state cursor = some (some descriptor) := by
  unfold pre4bNonbearingCallback?
  cases hSelector : occurrenceSelectorChiralityClassification? state cursor with
  | none =>
      cases hFact : occurrenceStructuralNonbearingFact? mol cursor with
      | none => simp
      | some fact => simp
  | some verdict =>
      cases verdict with
      | none => simp
      | some inner => simp

/-- **Exact `some none` characterization.**  A non-uppercase certainty comes either from the
existing selector route (non-real provenance or an actual lowercase fact), or from selector `none`
plus an explicit structural fact. -/
theorem pre4bNonbearingCallback?_eq_some_none_iff
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) :
    pre4bNonbearingCallback? mol state cursor = some none ↔
      occurrenceSelectorChiralityClassification? state cursor = some none ∨
        (occurrenceSelectorChiralityClassification? state cursor = none ∧
          occurrenceStructuralNonbearingFact? mol cursor ≠ none) := by
  unfold pre4bNonbearingCallback?
  cases hSelector : occurrenceSelectorChiralityClassification? state cursor with
  | none =>
      cases hFact : occurrenceStructuralNonbearingFact? mol cursor with
      | none => simp
      | some fact => simp
  | some verdict =>
      cases verdict with
      | none => simp
      | some inner => simp

/-- **Exact refusal characterization.**  The callback refuses exactly when the selector refuses and
no structural fact exists. -/
theorem pre4bNonbearingCallback?_eq_none_iff
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) :
    pre4bNonbearingCallback? mol state cursor = none ↔
      occurrenceSelectorChiralityClassification? state cursor = none ∧
        occurrenceStructuralNonbearingFact? mol cursor = none := by
  unfold pre4bNonbearingCallback?
  cases hSelector : occurrenceSelectorChiralityClassification? state cursor with
  | none =>
      cases hFact : occurrenceStructuralNonbearingFact? mol cursor with
      | none => simp
      | some fact => simp
  | some verdict => simp

/-- With no structural fact the callback is the selector classification, verdict for verdict. -/
theorem pre4bNonbearingCallback?_eq_selector_of_fact_eq_none
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (hFact : occurrenceStructuralNonbearingFact? mol cursor = none) :
    pre4bNonbearingCallback? mol state cursor =
      occurrenceSelectorChiralityClassification? state cursor := by
  unfold pre4bNonbearingCallback?
  cases hSelector : occurrenceSelectorChiralityClassification? state cursor with
  | none => simp [hFact]
  | some verdict => simp

/-- With selector `none` and an explicit fact, the callback returns `some none`. -/
theorem pre4bNonbearingCallback?_eq_some_none_of_selector_eq_none_of_fact_ne_none
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (hSelector : occurrenceSelectorChiralityClassification? state cursor = none)
    (hFact : occurrenceStructuralNonbearingFact? mol cursor ≠ none) :
    pre4bNonbearingCallback? mol state cursor = some none := by
  unfold pre4bNonbearingCallback?
  rw [hSelector]
  cases h : occurrenceStructuralNonbearingFact? mol cursor with
  | none => exact absurd h hFact
  | some fact => simp

/-- Non-real occurrences preserve the existing structural `knownNonchiral` route unchanged. -/
theorem pre4bNonbearingCallback?_eq_selector_of_nonReal
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (hNonReal : cursor.node.provenance ≠
      RawMolecule.CanonicalNodeProvenance.realAtom) :
    pre4bNonbearingCallback? mol state cursor =
      occurrenceSelectorChiralityClassification? state cursor :=
  pre4bNonbearingCallback?_eq_selector_of_fact_eq_none mol state cursor
    (occurrenceStructuralNonbearingFact?_eq_none_of_nonReal mol cursor hNonReal)

/-- **Unknown is preserved for every real occurrence without a geometric fact.**  A real occurrence
missing from the auxiliary state remains `none`; the callback does not turn absence into
nonchirality. -/
theorem pre4bNonbearingCallback?_eq_none_of_real_missing_of_no_fact
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (hProvenance : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom)
    (hMissing : state.factAt? cursor.node = none)
    (hFact : occurrenceStructuralNonbearingFact? mol cursor = none) :
    pre4bNonbearingCallback? mol state cursor = none := by
  have hSelector : occurrenceSelectorChiralityClassification? state cursor = none :=
    (occurrenceSelectorChiralityClassification?_eq_none_iff state cursor).mpr
      ⟨hProvenance, hMissing⟩
  exact (pre4bNonbearingCallback?_eq_none_iff mol state cursor).mpr
    ⟨hSelector, hFact⟩

/-- **Explicit facts upgrade unavailable real occurrences.**  A real occurrence missing from the
auxiliary state becomes `some none` only when an explicit structural fact exists. -/
theorem pre4bNonbearingCallback?_eq_some_none_of_real_missing_of_fact
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (hProvenance : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom)
    (hMissing : state.factAt? cursor.node = none)
    (hFact : occurrenceStructuralNonbearingFact? mol cursor ≠ none) :
    pre4bNonbearingCallback? mol state cursor = some none := by
  have hSelector : occurrenceSelectorChiralityClassification? state cursor = none :=
    (occurrenceSelectorChiralityClassification?_eq_none_iff state cursor).mpr
      ⟨hProvenance, hMissing⟩
  exact (pre4bNonbearingCallback?_eq_some_none_iff mol state cursor).mpr
    (Or.inr ⟨hSelector, hFact⟩)

/-- **Terminal vertices are integrated end to end.**  A real occurrence missing from the auxiliary
state whose centre has fewer than four lone-pair-augmented ligand positions receives `some none`
from the callback, purely from the geometric terminal-vertex fact. -/
theorem pre4bNonbearingCallback?_eq_some_none_of_real_missing_of_terminalVertex
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (hProvenance : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom)
    (hMissing : state.factAt? cursor.node = none)
    (hCount : (mol.ligandsWithLonePair cursor.node.atom).length < 4) :
    pre4bNonbearingCallback? mol state cursor = some none := by
  refine pre4bNonbearingCallback?_eq_some_none_of_real_missing_of_fact
    mol state cursor hProvenance hMissing ?_
  intro hNone
  rw [occurrenceStructuralNonbearingFact?_eq_some_terminalVertex
    mol cursor hProvenance hCount] at hNone
  exact Option.some_ne_none _ hNone

/-- **Uniform terminal arms are integrated end to end.**  The same upgrade holds when the actual
identical-atom/isotope terminal-arm data exists and the centre is not already covered by the
terminal-vertex branch. -/
theorem pre4bNonbearingCallback?_eq_some_none_of_real_missing_of_uniformTerminalArms
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (hProvenance : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom)
    (hMissing : state.factAt? cursor.node = none)
    (hArms : Nonempty (UniformTerminalArmData mol cursor))
    (hCount : ¬ (mol.ligandsWithLonePair cursor.node.atom).length < 4) :
    pre4bNonbearingCallback? mol state cursor = some none := by
  refine pre4bNonbearingCallback?_eq_some_none_of_real_missing_of_fact
    mol state cursor hProvenance hMissing ?_
  exact Option.ne_none_iff_isSome.mpr
    (occurrenceStructuralNonbearingFact?_isSome_of_uniformTerminalArms
      mol cursor hProvenance hArms hCount)

/-- **No annotation is not proof of nonchirality.**  Even when the tetrahedral candidate lookup
returns `none`, a real occurrence missing from the state and lacking a geometric fact stays
`unavailable` (`none`).  The annotation hypothesis is intentionally unused: it cannot by itself move
the callback. -/
theorem pre4bNonbearingCallback?_eq_none_of_no_annotation_alone
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (hProvenance : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom)
    (hMissing : state.factAt? cursor.node = none)
    (hFact : occurrenceStructuralNonbearingFact? mol cursor = none)
    (_hAnnotation : occurrenceTetrahedralCandidate? mol cursor.node = none) :
    pre4bNonbearingCallback? mol state cursor = none :=
  pre4bNonbearingCallback?_eq_none_of_real_missing_of_no_fact mol state cursor
    hProvenance hMissing hFact

/-! ## 9. Kernel-authority guards -/

assert_kernel_only atomZAt_eq_toMoleculeGraph_atomZ_of_lt
assert_kernel_only toMoleculeGraph_atomZ_eq_atomZAt
assert_kernel_only occurrenceLigandFrame?_eq_none_of_ligandCount_lt_four
assert_kernel_only legacyOccurrenceFact?_eq_none_of_ligandCount_lt_four
assert_kernel_only framedOccurrenceFact?_eq_none_of_ligandCount_lt_four
assert_kernel_only occurrenceFact?_eq_none_of_ligandCount_lt_four
assert_kernel_only occurrenceStructuralNonbearingFact?_eq_some_terminalVertex
assert_kernel_only occurrenceStructuralNonbearingFact?_eq_none_of_nonReal
assert_kernel_only occurrenceStructuralNonbearingFact?_eq_none_iff
assert_kernel_only occurrenceStructuralNonbearingFact?_isSome_iff
assert_kernel_only occurrenceStructuralNonbearingFact?_isSome_of_uniformTerminalArms
assert_kernel_only uniformTerminalArmData_completedTie
assert_kernel_only StructuralNonbearingFact.validated_of_terminalVertex
assert_kernel_only StructuralNonbearingFact.validated_of_uniformTerminalArms
assert_kernel_only StructuralNonbearingFact.validated
assert_kernel_only occurrenceSelectorChiralityClassification?_eq_toOptionOption_evidence
assert_kernel_only pre4bNonbearingCallback?_eq_evidence
assert_kernel_only pre4bNonbearingCallback?_eq_some_some_iff
assert_kernel_only pre4bNonbearingCallback?_eq_some_none_iff
assert_kernel_only pre4bNonbearingCallback?_eq_none_iff
assert_kernel_only pre4bNonbearingCallback?_eq_selector_of_fact_eq_none
assert_kernel_only pre4bNonbearingCallback?_eq_some_none_of_selector_eq_none_of_fact_ne_none
assert_kernel_only pre4bNonbearingCallback?_eq_selector_of_nonReal
assert_kernel_only pre4bNonbearingCallback?_eq_none_of_real_missing_of_no_fact
assert_kernel_only pre4bNonbearingCallback?_eq_some_none_of_real_missing_of_fact
assert_kernel_only pre4bNonbearingCallback?_eq_some_none_of_real_missing_of_terminalVertex
assert_kernel_only pre4bNonbearingCallback?_eq_some_none_of_real_missing_of_uniformTerminalArms
assert_kernel_only pre4bNonbearingCallback?_eq_none_of_no_annotation_alone

end

end OneCenter
end TetraStereo
