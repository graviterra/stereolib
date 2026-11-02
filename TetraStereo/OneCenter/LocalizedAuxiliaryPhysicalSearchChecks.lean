import TetraStereo.OneCenter.FiniteAuxiliaryBranchTransport
import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureAuxiliaryLetter
import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical
import TetraStereo.OneCenter.LocalizedRetainedContextGeneratedDescriptor
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-! Execution and source-relation controls for the nine-atom auxiliary context at atom 2. The
executable query uses the canonical molecule, coordinate-read configuration, complete atom list,
full retained history `[2, 0]`, and actual atom identifiers for the four center-2 neighbors. The
separate proposition proof below connects the actual occurrence and all distinct frame slots to
that obstruction; it does not evaluate the noncomputable frame object. -/

namespace TetraStereo.OneCenter.LocalizedAuxiliaryPhysicalSearchChecks

open TetraStereo.OneCenter
open TetraStereo.OneCenter.FiniteAuxiliaryBranchTransport
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureDomain
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureAuxiliaryLetter
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical
open TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.LocalizedRuleMajorReference
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness

private def atom (i : Fin 9) : symmetricCertified.Atom := i

/-- Atom identifiers used by the retained atom-2 occurrence. -/
def armNeighborAtoms : List (Fin 9) := [0, 3, 4, 6]

private theorem rootCenterAtom : rootFrames.center.1 = atom 0 := by
  rw [rootFrames.centerEq]
  simp [rootUnit, finalCenterUnit, OccurrenceUnit.atom, rootTetra, atom]
  apply Fin.ext
  rfl

private theorem rootArmTarget_history : rootArmTarget.1.node.history = [atom 2, atom 0] := by
  have rootReal : rootTarget.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
    finalOccurrence_provenance_real fixtureReference rootTetra
  have cursorEq := LocalizedCyclicRootArmReachability.rootSlot_eq_canonicalLigandCursor
    simple_bonded rootFrames rfl rootReal rootArmSlot
  change (rootFrames.frame.cursorAt rootArmSlot).occurrence.1.node.history = _
  rw [cursorEq]
  have ligandEq : symmetricCertified.canonicalLigandAtom rootFrames.center
      (symmetricCertified.canonicalLigandReindex rootFrames.center
        (rootFrames.detectedLigandPermutation rootArmSlot)) = atom 2 := by
    exact (symmetricCertified.canonicalLigandReindex_spec rootFrames.center
      (rootFrames.detectedLigandPermutation rootArmSlot)).symm.trans rootArmSlot_atom
  change [symmetricCertified.canonicalLigandAtom rootFrames.center
      (symmetricCertified.canonicalLigandReindex rootFrames.center
        (rootFrames.detectedLigandPermutation rootArmSlot)), rootFrames.center.1] =
    [atom 2, atom 0]
  rw [ligandEq, rootCenterAtom]

private theorem armContextCenterAtom : rootArmContextFrames.center.1 = atom 2 := by
  rw [rootArmContextFrames.centerEq, rootArmUnit_atom]
  rfl

private theorem armContextNeighbor (slot : Fin 4) :
    rootArmContextFrames.actualLigandAtoms slot ∈ [atom 0, atom 3, atom 4, atom 6] := by
  have hadj := symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt_adj
    rootArmContextFrames.center (rootArmContextFrames.detectedLigandPermutation slot)
  rw [armContextCenterAtom] at hadj
  have hindex := (adj_arm (rootArmContextFrames.actualLigandAtoms slot)).mp hadj
  simpa [ContextFrameCompilation.actualLigandAtoms, atom] using hindex

private theorem armContextLigand_injective :
    Function.Injective rootArmContextFrames.actualLigandAtoms := by
  intro a b hab
  apply rootArmContextFrames.detectedLigandPermutation.injective
  exact symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt_injective
    rootArmContextFrames.center hab

private theorem detectedAut_preservesZ
    (E : symmetricCertified.detectedMultiCenterMolecule.Aut) (v : symmetricCertified.Atom) :
    symmetricCertified.moleculeGraph.atomZ ((E : Equiv.Perm symmetricCertified.Atom) v) =
      symmetricCertified.moleculeGraph.atomZ v := by
  let e : symmetricCertified.moleculeGraph.Aut :=
    ⟨(E : Equiv.Perm symmetricCertified.Atom), E.property.1⟩
  exact MoleculeGraph.Aut.atomZ_eq (m := symmetricCertified.moleculeGraph) e v

private theorem canonicalAut_preservesZ
    (E : (actualCanonicalMolecule symmetricCertified).Aut) (v : Fin 9) :
    graph.atomZ (E.val v) = graph.atomZ v := by
  let e : graph.Aut := ⟨E.val, E.property.1⟩
  exact MoleculeGraph.Aut.atomZ_eq (m := graph) e v

private theorem z3 : graph.atomZ (3 : Fin 9) = 17 :=
  (atomZ_cases 3).2.1.mpr (by simp)

private theorem z4 : graph.atomZ (4 : Fin 9) = 6 :=
  (atomZ_cases 4).1.mpr (by simp)

private theorem z6 : graph.atomZ (6 : Fin 9) = 1 :=
  (atomZ_cases 6).2.2.mpr (by simp)

private theorem labelDistinct_of_367 {source target : Fin 9}
    (hs : source = 3 ∨ source = 4 ∨ source = 6)
    (ht : target = 3 ∨ target = 4 ∨ target = 6)
    (hne : source ≠ target) : graph.atomZ source ≠ graph.atomZ target := by
  rcases hs with hs | hs | hs <;> subst source
  · rcases ht with ht | ht | ht <;> subst target
    · exact (hne rfl).elim
    · intro h
      rw [z3, z4] at h
      norm_num at h
    · intro h
      rw [z3, z6] at h
      norm_num at h
  · rcases ht with ht | ht | ht <;> subst target
    · intro h
      rw [z4, z3] at h
      norm_num at h
    · exact (hne rfl).elim
    · intro h
      rw [z4, z6] at h
      norm_num at h
  · rcases ht with ht | ht | ht <;> subst target
    · intro h
      rw [z6, z3] at h
      norm_num at h
    · intro h
      rw [z6, z4] at h
      norm_num at h
    · exact (hne rfl).elim

private theorem noMapDistinctNeighbors (f : Fin 9 → Fin 9)
    (injective : Function.Injective f) (fix0 : f 0 = 0)
    (preservesZ : ∀ v, graph.atomZ (f v) = graph.atomZ v)
    {source target : Fin 9}
    (sourceMember : source ∈ [0, 3, 4, 6])
    (targetMember : target ∈ [0, 3, 4, 6]) (different : source ≠ target)
    (sent : f source = target) : False := by
  simp at sourceMember targetMember
  rcases sourceMember with rfl | rfl | rfl | rfl
  · rcases targetMember with rfl | rfl | rfl | rfl
    · exact different rfl
    · have h := sent
      rw [fix0] at h
      exact different h
    · have h := sent
      rw [fix0] at h
      exact different h
    · have h := sent
      rw [fix0] at h
      exact different h
  · rcases targetMember with rfl | rfl | rfl | rfl
    · have heq : f 3 = f 0 := by simpa [fix0] using sent
      have hs := injective heq
      exact different hs
    · exact different rfl
    · exact (labelDistinct_of_367 (by simp) (by simp) different)
        ((preservesZ 3).symm.trans (congrArg graph.atomZ sent))
    · exact (labelDistinct_of_367 (by simp) (by simp) different)
        ((preservesZ 3).symm.trans (congrArg graph.atomZ sent))
  · rcases targetMember with rfl | rfl | rfl | rfl
    · have heq : f 4 = f 0 := by simpa [fix0] using sent
      have hs := injective heq
      exact different hs
    · exact (labelDistinct_of_367 (by simp) (by simp) different)
        ((preservesZ 4).symm.trans (congrArg graph.atomZ sent))
    · exact different rfl
    · exact (labelDistinct_of_367 (by simp) (by simp) different)
        ((preservesZ 4).symm.trans (congrArg graph.atomZ sent))
  · rcases targetMember with rfl | rfl | rfl | rfl
    · have heq : f 6 = f 0 := by simpa [fix0] using sent
      have hs := injective heq
      exact different hs
    · exact (labelDistinct_of_367 (by simp) (by simp) different)
        ((preservesZ 6).symm.trans (congrArg graph.atomZ sent))
    · exact (labelDistinct_of_367 (by simp) (by simp) different)
        ((preservesZ 6).symm.trans (congrArg graph.atomZ sent))
    · exact different rfl

/-- Every distinct actual ligand pair at the atom-2 auxiliary occurrence is ruled out before
stereo signs are considered. A map fixing the complete retained history `[2,0]` cannot move atom 0;
injectivity also prevents a different source from mapping onto 0. The remaining neighbors have
pairwise distinct atomic numbers. -/
theorem noDistinctAuxiliaryBranchTransport
    (cfg : symmetricCertified.detectedMultiCenterMolecule.Configuration)
    (a b : Fin 4) (mirror : Bool) (different : a ≠ b) :
    ¬ ∃ σ : symmetricCertified.moleculeGraph.Aut,
      AuxiliaryBranchTransport rootArmContextFrames σ cfg a b mirror := by
  rintro ⟨σ, htransport⟩
  let E := symmetricCertified.physicalDetectedAut σ
  let source := symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt
    rootArmContextFrames.center (rootArmContextFrames.detectedLigandPermutation a)
  let targetAtom := symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt
    rootArmContextFrames.center (rootArmContextFrames.detectedLigandPermutation b)
  have sourceNeTarget : source ≠ targetAtom := by
    intro equal
    apply different
    apply rootArmContextFrames.detectedLigandPermutation.injective
    exact symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt_injective
      rootArmContextFrames.center equal
  have sourceMember : source ∈ [atom 0, atom 3, atom 4, atom 6] := by
    simpa [source, ContextFrameCompilation.actualLigandAtoms] using armContextNeighbor a
  have targetMember : targetAtom ∈ [atom 0, atom 3, atom 4, atom 6] := by
    simpa [targetAtom, ContextFrameCompilation.actualLigandAtoms] using armContextNeighbor b
  have fixedZero : (E : Equiv.Perm symmetricCertified.Atom) (atom 0) = atom 0 := by
    have h := htransport.historyFixed (atom 0) (by rw [rootArmTarget_history]; simp [atom])
    simpa [E, CertifiedLocalizedCIPInput.physicalDetectedAut] using h
  have sent : (E : Equiv.Perm symmetricCertified.Atom) source = targetAtom := by
    simpa [E, source, targetAtom, CertifiedLocalizedCIPInput.physicalDetectedAut] using
      htransport.ligandSent
  have preservesZ' : ∀ v : Fin 9, graph.atomZ ((E : Equiv.Perm symmetricCertified.Atom) v) =
      graph.atomZ v := by
    intro v
    exact detectedAut_preservesZ E v
  exact noMapDistinctNeighbors (E : Equiv.Perm symmetricCertified.Atom)
    (E : Equiv.Perm symmetricCertified.Atom).injective fixedZero preservesZ'
    (by simpa [source, atom] using sourceMember)
    (by simpa [targetAtom, atom] using targetMember) sourceNeTarget sent

/-- The exact canonical query has the same obstruction at every distinct actual neighbor pair.
This proof is independent of configuration signs; the decision theorem below makes the executed
boolean an exact representation of this relation. -/
theorem noCanonicalAuxiliaryComponentTransport
    (cfg : (actualCanonicalMolecule symmetricCertified).Configuration)
    (source target : Fin 9) (mirror : Bool)
    (sourceMember : source ∈ armNeighborAtoms)
    (targetMember : target ∈ armNeighborAtoms) (different : source ≠ target) :
    ¬ AuxiliaryComponentTransport (actualCanonicalMolecule symmetricCertified) cfg
      [atom 2, atom 0] source target mirror := by
  rintro ⟨E, hfixed, hsent, _⟩
  have fixed0 : E.val (atom 0) = atom 0 := by
    exact hfixed (atom 0) (by simp)
  have sourceMember' : source ∈ [0, 3, 4, 6] := by
    simpa [armNeighborAtoms] using sourceMember
  have targetMember' : target ∈ [0, 3, 4, 6] := by
    simpa [armNeighborAtoms] using targetMember
  exact noMapDistinctNeighbors E.val
    E.val.injective fixed0 (canonicalAut_preservesZ E)
    sourceMember' targetMember' different hsent

/-- Kernel-level correspondence for an actual-coordinate atom query on the canonical fixture. -/
theorem canonicalQuery_eq_true_iff
    (source target : Fin 9) (mirror : Bool) :
    decideAuxiliaryComponentTransport (actualCanonicalMolecule symmetricCertified)
      (coordinateCfg symmetricCertified) [atom 2, atom 0] source target mirror
      (List.finRange 9) = true ↔
      AuxiliaryComponentTransport (actualCanonicalMolecule symmetricCertified)
        (coordinateCfg symmetricCertified) [atom 2, atom 0] source target mirror := by
  exact decideAuxiliaryComponentTransport_iff _ _ _ _ _ _ (List.finRange 9)
    (List.nodup_finRange 9) (fun v => List.mem_finRange v)

theorem canonicalQuery_false_of_distinct_neighbors
    (source target : Fin 9) (mirror : Bool)
    (sourceMember : source ∈ armNeighborAtoms)
    (targetMember : target ∈ armNeighborAtoms) (different : source ≠ target) :
    decideAuxiliaryComponentTransport (actualCanonicalMolecule symmetricCertified)
      (coordinateCfg symmetricCertified) [atom 2, atom 0] source target mirror
      (List.finRange 9) = false := by
  cases hquery : decideAuxiliaryComponentTransport (actualCanonicalMolecule symmetricCertified)
      (coordinateCfg symmetricCertified) [atom 2, atom 0] source target mirror
      (List.finRange 9) with
  | false => rfl
  | true =>
      exact False.elim (noCanonicalAuxiliaryComponentTransport (coordinateCfg symmetricCertified)
        source target mirror sourceMember targetMember different
        ((canonicalQuery_eq_true_iff source target mirror).mp hquery))

/-! The executable atom query checks all twelve directed distinct-neighbor pairs. The map is over
all nine atoms; only the full retained-history and atom labels prune these instances, so signs are
irrelevant to the negative result. -/

def armDistinctDirectedPairs : List (Fin 9 × Fin 9) :=
  armNeighborAtoms.flatMap fun source =>
    (armNeighborAtoms.filter fun target => target ≠ source).map fun target => (source, target)

def allArmQueriesRefused (mirror : Bool) : Bool :=
  armDistinctDirectedPairs.all fun pair =>
    decideAuxiliaryComponentTransport (actualCanonicalMolecule symmetricCertified)
      (coordinateCfg symmetricCertified) [atom 2, atom 0] (atom pair.1) (atom pair.2) mirror
      (List.finRange 9) == false

/-- info: true -/
#guard_msgs in
#eval allArmQueriesRefused false

/-- info: true -/
#guard_msgs in
#eval allArmQueriesRefused true

/-- The historical final-root count is one at center 2; this is a distinct query from the
atom-2 auxiliary context, whose whole retained history includes both atoms 2 and 0. -/
theorem finalRoot2PhysicalPairCount_isOne :
    physicalEnantiomorphicPairCount canon calibratedCfg center2 = 1 :=
  physicalPairCountAt2

end TetraStereo.OneCenter.LocalizedAuxiliaryPhysicalSearchChecks

assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryPhysicalSearchChecks.rootArmTarget_history
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryPhysicalSearchChecks.armContextNeighbor
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryPhysicalSearchChecks.finalRoot2PhysicalPairCount_isOne
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryPhysicalSearchChecks.noDistinctAuxiliaryBranchTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryPhysicalSearchChecks.noCanonicalAuxiliaryComponentTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryPhysicalSearchChecks.canonicalQuery_eq_true_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryPhysicalSearchChecks.canonicalQuery_false_of_distinct_neighbors
