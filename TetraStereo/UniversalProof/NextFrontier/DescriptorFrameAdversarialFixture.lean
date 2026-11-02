import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorRuntime
import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorAdoptionFixture

set_option autoImplicit false






namespace TetraStereo.UniversalProof.NextFrontier.DescriptorFrameAdversarialFixture

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule

abbrev Adoption := TetraStereo.UniversalProof.FramedDescriptorAdoptionFixtureProofs.FramedDescriptorAdoptionFixture.nativeFixtureMol?

structure Context where
  mol : RawMolecule
  profile : FrameRuntime.Profile
  left : CanonicalRerootCursor
  right : CanonicalRerootCursor
  hydrogen : CanonicalRerootCursor

/-- Actual parser/profile setup; no hand-written molecule or replacement profile. -/
def context? : Option Context := do
  let mol ← Adoption
  let profile ← FrameRuntime.profile? mol (canonicalCenterRoot 1)
  let roots ← occurrenceLigandFrame? mol (canonicalCenterRoot 1)
  let left ← roots.find? (fun cursor => cursor.node.atom == 2)
  let right ← roots.find? (fun cursor => cursor.node.atom == 7)
  let hydrogen ← roots.find? (fun cursor => cursor.node.atom == 0)
  pure ⟨mol, profile, left, right, hydrogen⟩

/-- Preserve the atom/provenance but destroy its generated occurrence history. -/
def erasedHistory (ctx : Context) : CanonicalRerootCursor :=
  { ctx.left with node := { ctx.left.node with history := [] } }

/-- A real occurrence outside the parsed atom range, with a forged history and key. -/
def outsideAtomRange (ctx : Context) : CanonicalRerootCursor :=
  { node :=
      { atom := ctx.mol.atomCount
        parent := 1
        history := [ctx.mol.atomCount, 1]
        provenance := .realAtom } }

/-- Keep the genuine generated left node, but use the other arm as its previous node.
The other arm is not a neighbor of this occurrence; membership alone must not admit it. -/
def nonincidentPrevious (ctx : Context) : CanonicalRerootCursor :=
  { ctx.left with previous? := some ctx.right.node }

/-- Deliberately forge a matching node-local fact to tempt unchecked pure label projection. -/
def forgedFact (cursor : CanonicalRerootCursor) (uppercase : Bool) : OccurrenceAuxFact :=
  { key := canonicalOccurrenceKey cursor.node, atom := cursor.node.atom,
    descriptor := .R, uppercase := uppercase }

structure NegativeDiagnostic where
  nodeGenerated : Bool
  previousValid : Bool
  observedRefused : Bool
  rawRule4aPriority : Nat
  rawRule4cPriority : Nat
  descriptorRefused : Bool
  witnessRefused : Bool
  tiedRootRefused : Bool
  decisionRefused : Bool
  deriving Repr

/-- Zero fuel makes these precise admission probes: a forged strict node-local descriptor must
not bypass observation simply because no descendant recursion is requested. -/
def negativeDiagnostic (ctx : Context) (authoritative : Bool)
    (bad : CanonicalRerootCursor) : NegativeDiagnostic :=
  let uppercase : OccurrenceAuxState := [forgedFact bad true]
  let lowercase : OccurrenceAuxState := [forgedFact bad false]
  let pair : List (FrameRuntime.Cursor × FrameRuntime.Cursor) :=
    [(.actual bad, .actual ctx.right)]
  let before := FrameRuntime.compareDescriptorBranchAt? ctx.mol ctx.profile authoritative
    lowercase 0 .rule4c
  { nodeGenerated := ctx.profile.generated.contains bad.node
    previousValid := bad.previous?.all (fun previous =>
      ctx.profile.generated.contains previous && (bad.neighbors ctx.mol).contains previous)
    observedRefused := (FrameRuntime.cursor? ctx.mol ctx.profile (.actual bad)).isNone
    rawRule4aPriority := occurrenceNodePriority uppercase .rule4a true bad
    rawRule4cPriority := occurrenceNodePriority lowercase .rule4c true bad
    descriptorRefused := (FrameRuntime.compareDescriptorRule? ctx.mol ctx.profile authoritative
      uppercase before before .rule4a 0 pair).isNone
    witnessRefused := (FrameRuntime.compareRule4cWithWitness? ctx.mol ctx.profile authoritative
      lowercase before before 0 pair).isNone
    tiedRootRefused := (FrameRuntime.compareDescriptorAtTiedRoot? ctx.mol ctx.profile authoritative
      uppercase 0 .rule4a (.actual bad) (.actual ctx.right)).isNone
    decisionRefused := (FrameRuntime.decisionComplete? ctx.mol ctx.profile authoritative
      uppercase 0 bad ctx.right).isNone }

/-- Outer none is SETUP FAILURE, not a successful rejection. Each setup-success output contains
three cursor poisons, each tested in both modes. -/
def negativeDiagnostics : Option (List (String × Bool × NegativeDiagnostic)) := do
  let ctx ← context?
  let poisons : List (String × CanonicalRerootCursor) := [("erased_history", erasedHistory ctx),
    ("outside_atom_range", outsideAtomRange ctx),
    ("nonincident_previous", nonincidentPrevious ctx)]
  pure (poisons.flatMap fun entry => [false, true].map fun mode =>
    (entry.1, mode, negativeDiagnostic ctx mode entry.2))

structure RejectedPaddingDiagnostic where
  observedRefused : Bool
  descriptorRefused : Bool
  witnessRefused : Bool
  deriving Repr

/-- Invalid-parent padding is terminal but must not be accepted by a descriptor tie shortcut. -/
def rejectedPaddingDiagnostic (ctx : Context) (authoritative : Bool) : RejectedPaddingDiagnostic :=
  let bad : FrameRuntime.Cursor := .padding (.actual (erasedHistory ctx))
  let good : FrameRuntime.Cursor := .padding (.actual ctx.hydrogen)
  let before := FrameRuntime.compareDescriptorBranchAt? ctx.mol ctx.profile authoritative
    [] 0 .rule4c
  { observedRefused := (FrameRuntime.cursor? ctx.mol ctx.profile bad).isNone
    descriptorRefused := (FrameRuntime.compareDescriptorRule? ctx.mol ctx.profile authoritative
      [] before before .rule4a 0 [(bad, good)]).isNone
    witnessRefused := (FrameRuntime.compareRule4cWithWitness? ctx.mol ctx.profile authoritative
      [] before before 0 [(bad, good)]).isNone }

structure PaddingDiagnostic where
  parentObserved : Bool
  parentTerminal : Bool
  paddingObserved : Bool
  paddingDistanceFromParent : Bool
  paddingRawPriority : Nat
  descriptorSelfTie : Bool
  witnessSelfTie : Bool
  deriving Repr

/-- Positive padding control: actual terminal hydrogen parent, retained wrapper and phantom
projection. Even a forged fact at the padding key must have zero descriptor priority. -/
def paddingDiagnostic (ctx : Context) (authoritative : Bool) : PaddingDiagnostic :=
  let parent : FrameRuntime.Cursor := .actual ctx.hydrogen
  let padding : FrameRuntime.Cursor := .padding parent
  let state : OccurrenceAuxState := [forgedFact (padding.original ctx.mol) false]
  let before := FrameRuntime.compareDescriptorBranchAt? ctx.mol ctx.profile authoritative
    state 0 .rule4c
  { parentObserved := (FrameRuntime.cursor? ctx.mol ctx.profile parent).isSome
    parentTerminal := FrameRuntime.terminal ctx.mol parent
    paddingObserved := (FrameRuntime.cursor? ctx.mol ctx.profile padding).isSome
    paddingDistanceFromParent := FrameRuntime.cursor? ctx.mol ctx.profile padding ==
      (FrameRuntime.cursor? ctx.mol ctx.profile parent).map (fun distance => distance + 1)
    paddingRawPriority := occurrenceNodePriority state .rule4c true (padding.original ctx.mol)
    descriptorSelfTie := FrameRuntime.compareDescriptorRule? ctx.mol ctx.profile authoritative
      state before before .rule4a 0 [(padding, padding)] == some Ordering.eq
    witnessSelfTie := ((FrameRuntime.compareRule4cWithWitness? ctx.mol ctx.profile authoritative
      state before before 0 [(padding, padding)]).map (fun decision => decision.ordering)) ==
        some Ordering.eq }


theorem cursor_refuses_not_generated (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (cursor : CanonicalRerootCursor) (absent : profile.generated.contains cursor.node = false) :
    FrameRuntime.cursor? mol profile (.actual cursor) = none := by
  unfold FrameRuntime.cursor?
  rw [absent]
  rfl

theorem cursor_refuses_invalid_previous (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (cursor : CanonicalRerootCursor)
    (invalid : (cursor.previous?.all fun previous =>
      profile.generated.contains previous && (cursor.neighbors mol).contains previous) = false) :
    FrameRuntime.cursor? mol profile (.actual cursor) = none := by
  unfold FrameRuntime.cursor?
  rw [invalid]
  simp

theorem padding_refuses_rejected_parent (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (parent : FrameRuntime.Cursor) (refused : FrameRuntime.cursor? mol profile parent = none) :
    FrameRuntime.cursor? mol profile (.padding parent) = none := by
  simp [FrameRuntime.cursor?, refused]

theorem padding_observes_parent_distance (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (parent : FrameRuntime.Cursor) :
    FrameRuntime.cursor? mol profile (.padding parent) =
      (FrameRuntime.cursor? mol profile parent).map (fun distance => distance + 1) := rfl

/-! Computed observations only: NONE of these diagnostics has been run. -/
#eval context?.isSome
#eval negativeDiagnostics
#eval context?.map (fun ctx => [false, true].map (rejectedPaddingDiagnostic ctx))
#eval context?.map (fun ctx => [false, true].map (paddingDiagnostic ctx))

end TetraStereo.UniversalProof.NextFrontier.DescriptorFrameAdversarialFixture
