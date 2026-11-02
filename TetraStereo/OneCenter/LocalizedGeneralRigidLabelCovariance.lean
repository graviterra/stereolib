import TetraStereo.OneCenter.LocalizedRootZAutomorphismLabelCovariance
import TetraStereo.OneCenter.LocalizedRootZLabelSignEquivalence
import TetraStereo.OneCenter.LocalizedConstitutionalAutomorphismTransport
import TetraStereo.OneCenter.LocalizedActualRigidFrameCompleteness
import TetraStereo.OneCenter.LocalizedGeneralRigidCalibratedRootReader
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open AcyclicCutBranchAutomorphism






















































/-! ## Transporting a multi-center automorphism to the certified graph -/

/-- A multi-center automorphism of a carrier whose graph is the certified graph is an automorphism
of that certified graph.  The carrier and the graph live on the same vertex type, so the
underlying permutation is unchanged. -/
def multiCenterAutToGraphAut
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (mol : MoleculeGraph V) (molEq : m.mol = mol)
    (e : m.Aut) : mol.Aut :=
  ⟨(e : Equiv.Perm V), by
    rw [← molEq]
    exact MultiCenterMolecule.Aut.mem_molAut (m := m) e⟩

@[simp] theorem multiCenterAutToGraphAut_coe
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (mol : MoleculeGraph V) (molEq : m.mol = mol)
    (e : m.Aut) :
    (multiCenterAutToGraphAut m mol molEq e : Equiv.Perm V) = (e : Equiv.Perm V) := rfl

/-! ## The actual occurrence comparator is the constitutional comparator

On an actual rigid frame the prior Rules-4b/4c comparison is separated, hence decisive.  The
production through-Rule-5 comparison then reduces, in order, to the prior comparison, to the Rule-4a
cumulative comparison, and finally to the `constitutional` observable of the two actual Rule-4a
keys.  This is a statement about the actual builder only; no descriptor, sort or reader is
involved. -/

/-- **Constitutional reduction of the actual occurrence comparator.**  For a separated frame with
pairwise strictly distinct constitutional Rule-4a keys, the production occurrence comparator at two
distinct slots is the `OfficialRuleMajorKey.compare` of the two actual constitutional keys, with an
ordinary (non-pseudo) outcome. -/
theorem compareLocalizedOccurrenceThroughRule5At?_eq_constitutional
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (built : ∀ index : Fin 4,
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
        some (keys index))
    (separated : ConstitutionallySeparatedActualKeys input keys)
    (decisive : ∀ left right : Fin 4, left ≠ right →
      OfficialRuleMajorKey.compare (keys left).prior.rule4aKey.constitutional
        (keys right).prior.rule4aKey.constitutional ≠ Ordering.eq)
    (left right : Fin 4) (different : left ≠ right) :
    input.compareLocalizedOccurrenceThroughRule5At? target view frame left right =
      some { ordering := OfficialRuleMajorKey.compare
               (keys left).prior.rule4aKey.constitutional
               (keys right).prior.rule4aKey.constitutional,
             pseudo := false } := by
  have cumulativeEq :=
    input.compareLocalizedRerootCumulativeRule45Keys_eq_of_constitutional_ne
      (keys left).prior.rule4aKey (keys right).prior.rule4aKey
      (decisive left right different)
  have cumulativeNe :
      input.compareLocalizedRerootCumulativeRule45Keys
        (keys left).prior.rule4aKey (keys right).prior.rule4aKey ≠ Ordering.eq := by
    rw [cumulativeEq]
    exact decisive left right different
  have tailEq := input.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
    (keys left).prior (keys right).prior cumulativeNe
  have priorNe : input.compareLocalizedRerootCompoundRule4bcKeys
      (keys left).prior (keys right).prior ≠ Ordering.eq := by
    intro priorEq
    exact decisive left right different (cumulativeEq.symm.trans (tailEq.symm.trans priorEq))
  rw [input.compareLocalizedOccurrenceThroughRule5At?_eq_some_record
    target view frame keys built left right]
  rw [input.compareLocalizedRerootCompoundThroughRule5_eq_of_prior_ne
    (keys left) (keys right) priorNe]
  simp only [localizedOccurrenceRule45ComparisonRecord]
  rw [tailEq, cumulativeEq]

/-! ## Actual cursor correspondence between the two rigid frames

The two actual frames need not use the same ligand enumeration.  If the molecular slots are linked
by `alphaF` and `alphaG`, then the physical automorphism `e` maps the atom of slot `i` of the first
frame to the atom of slot `(alphaG⁻¹ * ligandPermAt e d * alphaF) i` of the second frame.  The
incoming cut of every frame cursor is the frame's target occurrence, so the previous-occurrence
clause of `LocalizedAutCursorCorrespondence` reduces to the actual centre atoms.  In particular the
original root is fixed but the current centres may be different atoms; they are never equated with
the root. -/

/-- **Cursor correspondence from actual frame linkage.**  At a slot whose atoms are linked by
`alphaF` and `alphaG`, the two actual frame cursors are related by the physical automorphism, with
the same fixed original root. -/
theorem exists_localizedAutCursorCorrespondence_of_actualFrame
    (input : LocalizedUniversalReference.Input)
    (m : MultiCenterMolecule input.certified.Atom)
    (molEq : m.mol = input.certified.moleculeGraph)
    (d : m.Center) (e : m.Aut) (root : input.certified.Atom)
    (rootFixed : (e : Equiv.Perm input.certified.Atom) root = root)
    (t u : LocalizedUniversalReference.Occurrence input)
    (rootF : t.1.root = root) (rootU : u.1.root = root)
    (F G : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derivedF : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame t F)
    (derivedG : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame u G)
    (centerF centerU : input.certified.TetrahedralCenter)
    (centerRealF : input.certified.RealTetrahedralCenterNode t.1.node centerF)
    (centerRealU : input.certified.RealTetrahedralCenterNode u.1.node centerU)
    (centerF_at : centerF.1 = d.1)
    (centerU_at : centerU.1 = (m.centerPerm e d).1)
    (alphaF alphaG : Equiv.Perm (Fin 4))
    (matchF : ActualFrameLigandMatch input m F d alphaF)
    (matchG : ActualFrameLigandMatch input m G (m.centerPerm e d) alphaG)
    (index : Fin 4) :
    LocalizedAutCursorCorrespondence input.certified
      (multiCenterAutToGraphAut m input.certified.moleculeGraph molEq e)
      root (F.cursorAt index)
      (G.cursorAt ((alphaG.symm * m.ligandPermAt e d * alphaF) index)) := by
  let p : Equiv.Perm (Fin 4) := alphaG.symm * m.ligandPermAt e d * alphaF
  have presentF : F.cursorAt index ∈ F.cursors := by
    unfold LocalizedOccurrenceFourLigandFrame.cursorAt
    exact List.get_mem F.cursors (Fin.cast F.length_eq.symm index)
  have presentG : G.cursorAt (p index) ∈ G.cursors := by
    unfold LocalizedOccurrenceFourLigandFrame.cursorAt
    exact List.get_mem G.cursors (Fin.cast G.length_eq.symm (p index))
  have childRootF : (F.cursorAt index).occurrence.1.root = t.1.root :=
    localizedRerootChildren_root_eq input.certified
      { occurrence := t, previous? := none } (F.cursorAt index) F.cursors derivedF.1 presentF
  have childRootG : (G.cursorAt (p index)).occurrence.1.root = u.1.root :=
    localizedRerootChildren_root_eq input.certified
      { occurrence := u, previous? := none } (G.cursorAt (p index)) G.cursors derivedG.1 presentG
  have prevF : (F.cursorAt index).previous? = some t := derivedF.1.2 _ presentF
  have prevG : (G.cursorAt (p index)).previous? = some u := derivedG.1.2 _ presentG
  have alphaApply : alphaG (p index) = m.ligandPermAt e d (alphaF index) := by
    dsimp [p]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact childRootF.trans rootF
  · exact childRootG.trans rootU
  · intro a b ha hb
    have aEq : m.ligandAtomAt d (alphaF index) = a :=
      Option.some.inj ((matchF.atom index).symm.trans ha)
    have bEq : m.ligandAtomAt (m.centerPerm e d) (alphaG (p index)) = b :=
      Option.some.inj ((matchG.atom (p index)).symm.trans hb)
    calc
      b = m.ligandAtomAt (m.centerPerm e d) (alphaG (p index)) := bEq.symm
      _ = m.ligandAtomAt (m.centerPerm e d) (m.ligandPermAt e d (alphaF index)) := by
            rw [alphaApply]
      _ = (e : Equiv.Perm input.certified.Atom) (m.ligandAtomAt d (alphaF index)) :=
            m.ligandAtomAt_ligandPermAt e d (alphaF index)
      _ = (multiCenterAutToGraphAut m input.certified.moleculeGraph molEq e :
              Equiv.Perm input.certified.Atom) (m.ligandAtomAt d (alphaF index)) := rfl
      _ = (multiCenterAutToGraphAut m input.certified.moleculeGraph molEq e :
              Equiv.Perm input.certified.Atom) a := by rw [aEq]
  · rw [prevF, prevG]
    simp
  · intro pOcc qOcc hp hq
    have pEq : pOcc = t := (Option.some.inj (prevF.symm.trans hp)).symm
    have qEq : qOcc = u := (Option.some.inj (prevG.symm.trans hq)).symm
    refine ⟨?_, ?_, ?_⟩
    · rw [pEq]
      exact rootF
    · rw [qEq]
      exact rootU
    · intro a b ha hb
      rw [pEq] at ha
      rw [qEq] at hb
      have aEq : centerF.1 = a :=
        Option.some.inj (centerRealF.2.symm.trans ha)
      have bEq : centerU.1 = b :=
        Option.some.inj (centerRealU.2.symm.trans hb)
      calc
        b = centerU.1 := bEq.symm
        _ = (m.centerPerm e d).1 := by rw [centerU_at]
        _ = (e : Equiv.Perm input.certified.Atom) d.1 := rfl
        _ = (e : Equiv.Perm input.certified.Atom) centerF.1 := by rw [centerF_at]
        _ = (multiCenterAutToGraphAut m input.certified.moleculeGraph molEq e :
              Equiv.Perm input.certified.Atom) centerF.1 := rfl
        _ = (multiCenterAutToGraphAut m input.certified.moleculeGraph molEq e :
              Equiv.Perm input.certified.Atom) a := by rw [aEq]








/-- The actual Rule-4a build of a frame slot is the prior Rule-4a key of the actual compound key. -/
theorem buildLocalizedRerootCompoundRule45Key?_rule4a_of_frame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (index : Fin 4) :
    input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
      some ((frame.compoundKeyAt input target view derived index).prior.rule4aKey) := by
  have prior :=
    (buildLocalizedRerootCompoundRule45Key?_prior_built input target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index)
      (frame.compoundKeyAt input target view derived index)
      (frame.compoundKeyAt_built input target view derived index)).1
  exact buildLocalizedRerootCompoundRule4bcKey?_rule4aKey input target view
    (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index)
    ((frame.compoundKeyAt input target view derived index).prior) prior

/-- **Pairwise constitutional comparison transport at actual rigid frames.**  At two distinct slots
of the first frame, the actual production `OfficialRuleMajorKey.compare` of the two constitutional
Rule-4a keys directly equals the same comparison at the corresponding slots of the second frame.
The correspondence is the actual physical automorphism transported to the certified graph; the slot
map is `alphaG⁻¹ * ligandPermAt e d * alphaF`. -/
theorem constitutionalCompare_transport_of_actualFrameCorrespondence
    (input : LocalizedUniversalReference.Input)
    (hsimple : input.certified.moleculeGraph.SimpleBonded)
    (hacyc : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (molEq : m.mol = input.certified.moleculeGraph)
    (d : m.Center) (e : m.Aut) (root : input.certified.Atom)
    (rootFixed : (e : Equiv.Perm input.certified.Atom) root = root)
    (t u : LocalizedUniversalReference.Occurrence input)
    (rootF : t.1.root = root) (rootU : u.1.root = root)
    (F G : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derivedF : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame t F)
    (derivedG : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame u G)
    (viewF : input.certified.LocalizedDependencyView t)
    (viewG : input.certified.LocalizedDependencyView u)
    (centerF centerU : input.certified.TetrahedralCenter)
    (centerRealF : input.certified.RealTetrahedralCenterNode t.1.node centerF)
    (centerRealU : input.certified.RealTetrahedralCenterNode u.1.node centerU)
    (centerF_at : centerF.1 = d.1)
    (centerU_at : centerU.1 = (m.centerPerm e d).1)
    (alphaF alphaG : Equiv.Perm (Fin 4))
    (matchF : ActualFrameLigandMatch input m F d alphaF)
    (matchG : ActualFrameLigandMatch input m G (m.centerPerm e d) alphaG)
    (left right : Fin 4) (different : left ≠ right) :
    OfficialRuleMajorKey.compare
        ((F.compoundKeyAt input.certified t viewF derivedF left).prior.rule4aKey.constitutional)
        ((F.compoundKeyAt input.certified t viewF derivedF right).prior.rule4aKey.constitutional) =
      OfficialRuleMajorKey.compare
        ((G.compoundKeyAt input.certified u viewG derivedG
            ((alphaG.symm * m.ligandPermAt e d * alphaF) left)).prior.rule4aKey.constitutional)
        ((G.compoundKeyAt input.certified u viewG derivedG
            ((alphaG.symm * m.ligandPermAt e d * alphaF) right)).prior.rule4aKey.constitutional) := by
  let p : Equiv.Perm (Fin 4) := alphaG.symm * m.ligandPermAt e d * alphaF
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    simp [LocalizedUniversalReference.carrierFuel,
      LocalizedExtendedShortCircuit.carrierFuel,
      LocalizedReference.Input.molecule]
  have rootFixedGraph :
      (multiCenterAutToGraphAut m input.certified.moleculeGraph molEq e :
        Equiv.Perm input.certified.Atom) root = root := by
    simpa using rootFixed
  have corrLeft : LocalizedAutCursorCorrespondence input.certified
      (multiCenterAutToGraphAut m input.certified.moleculeGraph molEq e)
      root (F.cursorAt left) (G.cursorAt (p left)) :=
    exists_localizedAutCursorCorrespondence_of_actualFrame input m molEq d e root rootFixed
      t u rootF rootU F G derivedF derivedG centerF centerU centerRealF centerRealU
      centerF_at centerU_at alphaF alphaG matchF matchG left
  have corrRight : LocalizedAutCursorCorrespondence input.certified
      (multiCenterAutToGraphAut m input.certified.moleculeGraph molEq e)
      root (F.cursorAt right) (G.cursorAt (p right)) :=
    exists_localizedAutCursorCorrespondence_of_actualFrame input m molEq d e root rootFixed
      t u rootF rootU F G derivedF derivedG centerF centerU centerRealF centerRealU
      centerF_at centerU_at alphaF alphaG matchF matchG right
  obtain ⟨firstLeftKey, secondLeftKey, firstRightKey, secondRightKey,
    firstLeftComputed, secondLeftComputed, firstRightComputed, secondRightComputed, keyEq⟩ :=
    input.certified.compare_eq_of_automorphism_correspondence_pair
      hsimple hacyc enough rootFixedGraph corrLeft corrRight
      (F.cursorAt_valid input.certified t derivedF left)
      (G.cursorAt_valid input.certified u derivedG (p left))
      (F.cursorAt_valid input.certified t derivedF right)
      (G.cursorAt_valid input.certified u derivedG (p right))
      .rule4a t viewF
      .rule4a u viewG
      .rule4a t viewF
      .rule4a u viewG
  have firstLeftEq : firstLeftKey =
      (F.compoundKeyAt input.certified t viewF derivedF left).prior.rule4aKey :=
    Option.some.inj (firstLeftComputed.symm.trans
      (buildLocalizedRerootCompoundRule45Key?_rule4a_of_frame
        input.certified t viewF F derivedF left))
  have secondLeftEq : secondLeftKey =
      (F.compoundKeyAt input.certified t viewF derivedF right).prior.rule4aKey :=
    Option.some.inj (secondLeftComputed.symm.trans
      (buildLocalizedRerootCompoundRule45Key?_rule4a_of_frame
        input.certified t viewF F derivedF right))
  have firstRightEq : firstRightKey =
      (G.compoundKeyAt input.certified u viewG derivedG (p left)).prior.rule4aKey :=
    Option.some.inj (firstRightComputed.symm.trans
      (buildLocalizedRerootCompoundRule45Key?_rule4a_of_frame
        input.certified u viewG G derivedG (p left)))
  have secondRightEq : secondRightKey =
      (G.compoundKeyAt input.certified u viewG derivedG (p right)).prior.rule4aKey :=
    Option.some.inj (secondRightComputed.symm.trans
      (buildLocalizedRerootCompoundRule45Key?_rule4a_of_frame
        input.certified u viewG G derivedG (p right)))
  rw [firstLeftEq, secondLeftEq, firstRightEq, secondRightEq] at keyEq
  simpa [p] using keyEq








/-- **Actual compound-key rank comparison covariance.**  At corresponding slots of the two actual
constitutionally rigid frames, the comparison of the actual `compoundKeyRank` values is the same on
both sides.  Both frames' separations and both constitutional domination facts are derived from
their actual graph-level rigidity; only the actual frame linkage and physical automorphism are
assumed. -/
theorem compoundKeyRank_compare_eq_of_actualFrameCorrespondence
    (input : LocalizedUniversalReference.Input)
    (hsimple : input.certified.moleculeGraph.SimpleBonded)
    (hacyc : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (m : MultiCenterMolecule input.certified.Atom)
    (molEq : m.mol = input.certified.moleculeGraph)
    (d : m.Center) (e : m.Aut) (root : input.certified.Atom)
    (rootFixed : (e : Equiv.Perm input.certified.Atom) root = root)
    (t u : LocalizedUniversalReference.Occurrence input)
    (rootF : t.1.root = root) (rootU : u.1.root = root)
    (F G : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derivedF : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame t F)
    (derivedG : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame u G)
    (viewF : input.certified.LocalizedDependencyView t)
    (viewG : input.certified.LocalizedDependencyView u)
    (centerF centerU : input.certified.TetrahedralCenter)
    (centerRealF : input.certified.RealTetrahedralCenterNode t.1.node centerF)
    (centerRealU : input.certified.RealTetrahedralCenterNode u.1.node centerU)
    (centerF_at : centerF.1 = d.1)
    (centerU_at : centerU.1 = (m.centerPerm e d).1)
    (rigidF : ConstitutionallyRigidGraphAt input.certified.moleculeGraph centerF.1)
    (rigidU : ConstitutionallyRigidGraphAt input.certified.moleculeGraph centerU.1)
    (alphaF alphaG : Equiv.Perm (Fin 4))
    (matchF : ActualFrameLigandMatch input m F d alphaF)
    (matchG : ActualFrameLigandMatch input m G (m.centerPerm e d) alphaG)
    (left right : Fin 4) (different : left ≠ right) :
    compare
        (input.certified.compoundKeyRank
          (G.compoundKeyAt input.certified u viewG derivedG)
          ((alphaG.symm * m.ligandPermAt e d * alphaF) left))
        (input.certified.compoundKeyRank
          (G.compoundKeyAt input.certified u viewG derivedG)
          ((alphaG.symm * m.ligandPermAt e d * alphaF) right)) =
      compare
        (input.certified.compoundKeyRank
          (F.compoundKeyAt input.certified t viewF derivedF) left)
        (input.certified.compoundKeyRank
          (F.compoundKeyAt input.certified t viewF derivedF) right) := by
  let p : Equiv.Perm (Fin 4) := alphaG.symm * m.ligandPermAt e d * alphaF
  let keysF : Fin 4 → input.certified.LocalizedRerootCompoundRule45Key :=
    F.compoundKeyAt input.certified t viewF derivedF
  let keysG : Fin 4 → input.certified.LocalizedRerootCompoundRule45Key :=
    G.compoundKeyAt input.certified u viewG derivedG
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    simp [LocalizedUniversalReference.carrierFuel,
      LocalizedExtendedShortCircuit.carrierFuel,
      LocalizedReference.Input.molecule]
  have separatedF : ConstitutionallySeparatedActualKeys input.certified keysF :=
    constitutionallySeparatedActualFrameKeys_of_actualFrame input.certified t viewF F derivedF
      centerF centerRealF rigidF hacyc hsimple hcharge enough
  have separatedG : ConstitutionallySeparatedActualKeys input.certified keysG :=
    constitutionallySeparatedActualFrameKeys_of_actualFrame input.certified u viewG G derivedG
      centerU centerRealU rigidU hacyc hsimple hcharge enough
  have builtF : ∀ index : Fin 4,
      input.certified.buildLocalizedRerootCompoundRule45Key? t viewF
          (localizedOccurrenceRerootEvaluationFuel
            (LocalizedUniversalReference.carrierFuel input)) (F.cursorAt index) =
        some (keysF index) :=
    fun index => F.compoundKeyAt_built input.certified t viewF derivedF index
  have builtG : ∀ index : Fin 4,
      input.certified.buildLocalizedRerootCompoundRule45Key? u viewG
          (localizedOccurrenceRerootEvaluationFuel
            (LocalizedUniversalReference.carrierFuel input)) (G.cursorAt index) =
        some (keysG index) :=
    fun index => G.compoundKeyAt_built input.certified u viewG derivedG index
  have decisiveF : ∀ left right : Fin 4, left ≠ right →
      OfficialRuleMajorKey.compare (keysF left).prior.rule4aKey.constitutional
        (keysF right).prior.rule4aKey.constitutional ≠ Ordering.eq :=
    fun left right different =>
      constitutionalCompare_ne_at_actualFrame_of_graphRigid_derived input.certified t viewF F
        derivedF centerF centerRealF rigidF hacyc hsimple hcharge enough left right different
  have decisiveG : ∀ left right : Fin 4, left ≠ right →
      OfficialRuleMajorKey.compare (keysG left).prior.rule4aKey.constitutional
        (keysG right).prior.rule4aKey.constitutional ≠ Ordering.eq :=
    fun left right different =>
      constitutionalCompare_ne_at_actualFrame_of_graphRigid_derived input.certified u viewG G
        derivedG centerU centerRealU rigidU hacyc hsimple hcharge enough left right different
  have pDifferent : p left ≠ p right := fun same => different (p.injective same)
  have productionF :=
    compareLocalizedOccurrenceThroughRule5At?_eq_constitutional input.certified t viewF F
      keysF builtF separatedF decisiveF left right different
  have productionG :=
    compareLocalizedOccurrenceThroughRule5At?_eq_constitutional input.certified u viewG G
      keysG builtG separatedG decisiveG (p left) (p right) pDifferent
  have rankF :=
    input.certified.compareLocalizedOccurrenceThroughRule5At?_eq_strictRankComparison
      t viewF F keysF builtF separatedF left right different
  have rankG :=
    input.certified.compareLocalizedOccurrenceThroughRule5At?_eq_strictRankComparison
      u viewG G keysG builtG separatedG (p left) (p right) pDifferent
  have constitutionalTransport :=
    constitutionalCompare_transport_of_actualFrameCorrespondence input hsimple hacyc m molEq d e
      root rootFixed t u rootF rootU F G derivedF derivedG viewF viewG centerF centerU centerRealF
      centerRealU centerF_at centerU_at alphaF alphaG matchF matchG left right different
  have combined :
      strictRankComparison (input.certified.compoundKeyRank keysG) (p left) (p right) =
        strictRankComparison (input.certified.compoundKeyRank keysF) left right := by
    rw [← rankG, productionG, ← constitutionalTransport, ← productionF, rankF]
  have recordEq :
      ({ ordering := compare
            (input.certified.compoundKeyRank keysG (p left))
            (input.certified.compoundKeyRank keysG (p right)),
          pseudo := false } : ConstitutionalDescriptorHierarchyComparison) =
        { ordering := compare
            (input.certified.compoundKeyRank keysF left)
            (input.certified.compoundKeyRank keysF right),
          pseudo := false } := by
    simpa [strictRankComparison] using combined
  have orderEq := congrArg
    (fun record : ConstitutionalDescriptorHierarchyComparison => record.ordering) recordEq
  simpa [p, keysF, keysG] using orderEq

/-! ## Actual sorted-priority covariance

The two actual frames need not enumerate their ligands in the same order.  Given the actual tracked
orders of the executable sorter, the actual compound-key rank transport at corresponding slots
identifies the two sorted lists up to the physical slot correspondence `p`.  Only the rank
comparison transport and injectivity of the target rank are used; the lists themselves are the
actual executable outputs. -/

/-- **Actual sorted-priority covariance.**  If both tracked orders are permutations with strictly
descending actual `compoundKeyRank`, the target rank is injective, and the actual rank comparison is
the same at corresponding slots, then the two actual sorted slot lists are related by `p`. -/
theorem trackedHighestFirst_eq_map_of_compoundKeyRankTransport
    (input : CertifiedLocalizedCIPInput)
    (keysF keysG : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (p : Equiv.Perm (Fin 4))
    (trackedF trackedG : TrackedLocalizedLigandOrder)
    (permutationF : trackedF.highestFirst.Perm (List.finRange 4))
    (strictF : trackedF.highestFirst.Pairwise (fun left right =>
      input.compoundKeyRank keysF right < input.compoundKeyRank keysF left))
    (permutationG : trackedG.highestFirst.Perm (List.finRange 4))
    (strictG : trackedG.highestFirst.Pairwise (fun left right =>
      input.compoundKeyRank keysG right < input.compoundKeyRank keysG left))
    (injectiveG : Function.Injective (input.compoundKeyRank keysG))
    (rankTransport : ∀ left right : Fin 4, left ≠ right →
      compare (input.compoundKeyRank keysG (p left))
          (input.compoundKeyRank keysG (p right)) =
        compare (input.compoundKeyRank keysF left)
          (input.compoundKeyRank keysF right)) :
    trackedG.highestFirst = trackedF.highestFirst.map p := by
  have permutationTransport : List.Perm trackedG.highestFirst
      (trackedF.highestFirst.map p) := by
    have mapped : List.Perm (trackedF.highestFirst.map p) (List.finRange 4) :=
      (permutationF.map p).trans (Equiv.Perm.map_finRange_perm p)
    exact permutationG.trans mapped.symm
  refine List.Perm.eq_of_pairwise
    (le := fun left right =>
      ¬ input.compoundKeyRank keysG left < input.compoundKeyRank keysG right)
    ?_ ?_ ?_ permutationTransport
  · intro left right _ _ notLeft notRight
    exact injectiveG
      (le_antisymm (Nat.le_of_not_lt notRight) (Nat.le_of_not_lt notLeft))
  · exact strictG.imp (by
      intro left right higher
      exact Nat.not_lt_of_ge (Nat.le_of_lt higher))
  · rw [List.pairwise_map]
    exact strictF.imp (by
      intro left right higher
      have different : left ≠ right := by
        intro same
        subst same
        exact Nat.lt_irrefl _ higher
      have compared : compare (input.compoundKeyRank keysG (p left))
          (input.compoundKeyRank keysG (p right)) = Ordering.gt := by
        rw [rankTransport left right different]
        exact Nat.compare_eq_gt.mpr higher
      exact Nat.not_lt_of_ge (Nat.le_of_lt (Nat.compare_eq_gt.mp compared)))









private theorem generalMul_eq_one_or_neg_one {first second : ℝ}
    (firstCases : first = 1 ∨ first = -1)
    (secondCases : second = 1 ∨ second = -1) :
    first * second = 1 ∨ first * second = -1 := by
  rcases firstCases with rfl | rfl <;> rcases secondCases with rfl | rfl <;> norm_num

/-- **Actual normalized-label covariance at general constitutionally rigid physical centers.**

For paired actual real occurrences `t`, `u` at distinguished physical centers `d`, `e d`, with
actual four-ligand frames `F`, `G`, actual graph linkage through slot equivalences `alphaF`,
`alphaG`, graph-level constitutional rigidity at both actual centres, nondegenerate actual
coordinates calibrated to the same physical configuration `cfg`, and the physical local sign law,
the actual generated reference state at `u` is the uppercase reflection of the actual generated
reference state at `t` exactly when the sign law has `epsilon = -1`.

The original root is fixed by the automorphism but may differ from both current centers; the two
current centers are not identified with each other or with the root.  Neither the sorted order, the
descriptor equality, nor the reader relation is assumed: they are derived from the actual frames,
the actual executable comparator and the physical calibration. -/
theorem referenceState_generalRigidAutomorphism_label_covariance
    (input : LocalizedUniversalReference.Input)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (hsimple : input.certified.moleculeGraph.SimpleBonded)
    (hacyc : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (m : MultiCenterMolecule input.certified.Atom)
    (molEq : m.mol = input.certified.moleculeGraph)
    (cfg : m.Configuration) (d : m.Center) (e : m.Aut) (mirror : Bool)
    (root : input.certified.Atom)
    (rootFixed : (e : Equiv.Perm input.certified.Atom) root = root)
    (t u : LocalizedUniversalReference.Occurrence input)
    (rootF : t.1.root = root) (rootU : u.1.root = root)
    (F G : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derivedF : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame t F)
    (derivedG : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame u G)
    (centerF centerU : input.certified.TetrahedralCenter)
    (centerRealF : input.certified.RealTetrahedralCenterNode t.1.node centerF)
    (centerRealU : input.certified.RealTetrahedralCenterNode u.1.node centerU)
    (centerF_at : centerF.1 = d.1)
    (centerU_at : centerU.1 = (m.centerPerm e d).1)
    (rigidF : ConstitutionallyRigidGraphAt input.certified.moleculeGraph centerF.1)
    (rigidU : ConstitutionallyRigidGraphAt input.certified.moleculeGraph centerU.1)
    (alphaF alphaG : Equiv.Perm (Fin 4))
    (matchF : ActualFrameLigandMatch input m F d alphaF)
    (matchG : ActualFrameLigandMatch input m G (m.centerPerm e d) alphaG)
    (pointsF pointsU : Fin 4 → CartesianPoint3)
    (spatialF : ∀ index,
      input.certified.localizedRerootCursorSpatialPoint? (F.cursorAt index) =
        some (pointsF index))
    (spatialU : ∀ index,
      input.certified.localizedRerootCursorSpatialPoint? (G.cursorAt index) =
        some (pointsU index))
    (calibrationF : PhysicalFrameCalibration m cfg d alphaF pointsF)
    (calibrationU : PhysicalFrameCalibration m cfg (m.centerPerm e d) alphaG pointsU)
    (signLaw :
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        (if mirror then -1 else 1) *
          m.configurationSign cfg (m.centerPerm e d)) :
    LocalizedUniversalReference.referenceState input u =
      (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input t) := by
  let viewF : input.certified.LocalizedDependencyView t :=
    input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) t
  let viewU : input.certified.LocalizedDependencyView u :=
    input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) u
  let keysF : Fin 4 → input.certified.LocalizedRerootCompoundRule45Key :=
    F.compoundKeyAt input.certified t viewF derivedF
  let keysU : Fin 4 → input.certified.LocalizedRerootCompoundRule45Key :=
    G.compoundKeyAt input.certified u viewU derivedG
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    simp [LocalizedUniversalReference.carrierFuel,
      LocalizedExtendedShortCircuit.carrierFuel,
      LocalizedReference.Input.molecule]
  have separatedF : ConstitutionallySeparatedActualKeys input.certified keysF :=
    constitutionallySeparatedActualFrameKeys_of_actualFrame input.certified t viewF F derivedF
      centerF centerRealF rigidF hacyc hsimple hcharge enough
  have separatedU : ConstitutionallySeparatedActualKeys input.certified keysU :=
    constitutionallySeparatedActualFrameKeys_of_actualFrame input.certified u viewU G derivedG
      centerU centerRealU rigidU hacyc hsimple hcharge enough
  obtain ⟨trackedF, computedF, permutationF, strictF, _pseudoF⟩ :=
    input.certified.exists_trackedOrder_of_constitutionallySeparatedActualKeys
      t viewF F derivedF keysF
      (fun index => F.compoundKeyAt_built input.certified t viewF derivedF index)
      separatedF
  obtain ⟨trackedU, computedU, permutationU, strictU, _pseudoU⟩ :=
    input.certified.exists_trackedOrder_of_constitutionallySeparatedActualKeys
      u viewU G derivedG keysU
      (fun index => G.compoundKeyAt_built input.certified u viewU derivedG index)
      separatedU
  have injectiveU : Function.Injective (input.certified.compoundKeyRank keysU) :=
    input.certified.compoundKeyRank_injective keysU
      (input.certified.compoundKeyOffDiagonalStrict_of_priorSeparated keysU separatedU)
  have rankTransport : ∀ left right : Fin 4, left ≠ right →
      compare (input.certified.compoundKeyRank keysU
          ((alphaG.symm * m.ligandPermAt e d * alphaF) left))
        (input.certified.compoundKeyRank keysU
          ((alphaG.symm * m.ligandPermAt e d * alphaF) right)) =
      compare (input.certified.compoundKeyRank keysF left)
        (input.certified.compoundKeyRank keysF right) :=
    fun left right different =>
      compoundKeyRank_compare_eq_of_actualFrameCorrespondence
        input hsimple hacyc hcharge m molEq d e root rootFixed t u rootF rootU F G
        derivedF derivedG viewF viewU centerF centerU centerRealF centerRealU
        centerF_at centerU_at rigidF rigidU alphaF alphaG matchF matchG
        left right different
  have sortedTransport : trackedU.highestFirst =
      trackedF.highestFirst.map
        (alphaG.symm * m.ligandPermAt e d * alphaF) :=
    trackedHighestFirst_eq_map_of_compoundKeyRankTransport input.certified keysF keysU
      (alphaG.symm * m.ligandPermAt e d * alphaF) trackedF trackedU
      permutationF strictF permutationU strictU injectiveU rankTransport
  let sF : ℝ := rationalVolumeSign
    (CartesianPoint3.orientedVolume (pointsF 0) (pointsF 1) (pointsF 2) (pointsF 3))
  let sU : ℝ := rationalVolumeSign
    (CartesianPoint3.orientedVolume (pointsU 0) (pointsU 1) (pointsU 2) (pointsU 3))
  have volumeF_nonzero : CartesianPoint3.orientedVolume
      (pointsF 0) (pointsF 1) (pointsF 2) (pointsF 3) ≠ 0 :=
    calibrationF.written_nondegenerate
  have volumeU_nonzero : CartesianPoint3.orientedVolume
      (pointsU 0) (pointsU 1) (pointsU 2) (pointsU 3) ≠ 0 :=
    calibrationU.written_nondegenerate
  let parityF : TetrahedralInputParity := parityOfVolumeSign sF
  let parityU : TetrahedralInputParity := parityOfVolumeSign sU
  have writtenParityF : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsF 0, pointsF 1, pointsF 2, pointsF 3] parityF :=
    rationalTetrahedralInputParity_parityOfVolumeSign
      (pointsF 0) (pointsF 1) (pointsF 2) (pointsF 3) volumeF_nonzero
  have writtenParityU : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsU 0, pointsU 1, pointsU 2, pointsU 3] parityU :=
    rationalTetrahedralInputParity_parityOfVolumeSign
      (pointsU 0) (pointsU 1) (pointsU 2) (pointsU 3) volumeU_nonzero
  obtain ⟨alphaCanonF, ligandLinkF⟩ :=
    exists_ligandPermutation_of_actualFrame input.certified t F derivedF centerF centerRealF
      hsimple hacyc enough
  obtain ⟨alphaCanonU, ligandLinkU⟩ :=
    exists_ligandPermutation_of_actualFrame input.certified u G derivedG centerU centerRealU
      hsimple hacyc enough
  obtain ⟨trackedF141, computedF141, _pseudoF141, stateF⟩ :=
    referenceState_reader_eq_chiral_of_constitutionallyRigidFrame_noInterface
      input noDouble t F derivedF centerF centerRealF rigidF hacyc hsimple hcharge
      alphaCanonF ligandLinkF pointsF spatialF parityF writtenParityF
  obtain ⟨trackedU141, computedU141, _pseudoU141, stateU⟩ :=
    referenceState_reader_eq_chiral_of_constitutionallyRigidFrame_noInterface
      input noDouble u G derivedG centerU centerRealU rigidU hacyc hsimple hcharge
      alphaCanonU ligandLinkU pointsU spatialU parityU writtenParityU
  have trackedF_eq : trackedF141 = trackedF := by
    rw [computedF141] at computedF
    exact Option.some.inj computedF
  have trackedU_eq : trackedU141 = trackedU := by
    rw [computedU141] at computedU
    exact Option.some.inj computedU
  rw [trackedF_eq] at stateF
  rw [trackedU_eq] at stateU
  let eF : ℝ := parityFactor
    (RawMolecule.permutationIsEven (trackedF.highestFirst.map Fin.val))
  let eU : ℝ := parityFactor
    (RawMolecule.permutationIsEven (trackedU.highestFirst.map Fin.val))
  have labelF_eq :
      RawMolecule.descriptorOfParity parityF
        (RawMolecule.permutationIsEven
          (trackedF.highestFirst.map Fin.val)) =
        RS.ofHandedness (sF * eF) := by
    simpa [parityF, sF, eF] using
      descriptorOfParity_parityOfVolumeSign
        (pointsF 0) (pointsF 1) (pointsF 2) (pointsF 3) volumeF_nonzero
        (RawMolecule.permutationIsEven (trackedF.highestFirst.map Fin.val))
  have labelU_eq :
      RawMolecule.descriptorOfParity parityU
        (RawMolecule.permutationIsEven
          (trackedU.highestFirst.map Fin.val)) =
        RS.ofHandedness (sU * eU) := by
    simpa [parityU, sU, eU] using
      descriptorOfParity_parityOfVolumeSign
        (pointsU 0) (pointsU 1) (pointsU 2) (pointsU 3) volumeU_nonzero
        (RawMolecule.permutationIsEven (trackedU.highestFirst.map Fin.val))
  have permutationSign : permHandedness
      (alphaG.symm * m.ligandPermAt e d * alphaF) =
      permHandedness alphaG * permHandedness (m.ligandPermAt e d) *
        permHandedness alphaF := by
    change permHandedness (alphaG⁻¹ * m.ligandPermAt e d * alphaF) =
      permHandedness alphaG * permHandedness (m.ligandPermAt e d) *
        permHandedness alphaF
    simp only [permHandedness_mul, permHandedness_inv]
  have parityTransport : eU =
      permHandedness (alphaG.symm * m.ligandPermAt e d * alphaF) * eF := by
    have transported := parityFactor_permutationIsEven_map
      trackedF.highestFirst
      (alphaG.symm * m.ligandPermAt e d * alphaF) permutationF
    rw [← sortedTransport] at transported
    simpa [eU, eF] using transported
  have signF : sF =
      m.configurationSign cfg d * permHandedness alphaF :=
    calibrationF.sign_eq_configurationSign_mul
  have signU : sU =
      m.configurationSign cfg (m.centerPerm e d) *
        permHandedness alphaG :=
    calibrationU.sign_eq_configurationSign_mul
  have signProduct : sU * eU =
      (if mirror then (-1 : ℝ) else 1) * (sF * eF) := by
    have ligandSignSquared :
        permHandedness (m.ligandPermAt e d) *
          permHandedness (m.ligandPermAt e d) = 1 :=
      permHandedness_mul_self (m.ligandPermAt e d)
    have frameSignSquared :
        permHandedness alphaG * permHandedness alphaG = 1 :=
      permHandedness_mul_self alphaG
    have epsilonSquared :
        (if mirror then (-1 : ℝ) else 1) *
          (if mirror then (-1 : ℝ) else 1) = 1 := by
      cases mirror <;> norm_num
    have reversedSignLaw :
        m.configurationSign cfg (m.centerPerm e d) *
          permHandedness (m.ligandPermAt e d) =
          (if mirror then (-1 : ℝ) else 1) * m.configurationSign cfg d := by
      calc
        m.configurationSign cfg (m.centerPerm e d) *
            permHandedness (m.ligandPermAt e d)
            = ((if mirror then (-1 : ℝ) else 1) *
                  (if mirror then (-1 : ℝ) else 1)) *
                (m.configurationSign cfg (m.centerPerm e d) *
                  permHandedness (m.ligandPermAt e d)) := by
              rw [epsilonSquared]
              ring
        _ = (if mirror then (-1 : ℝ) else 1) *
              (((if mirror then (-1 : ℝ) else 1) *
                  m.configurationSign cfg (m.centerPerm e d)) *
                permHandedness (m.ligandPermAt e d)) := by ring
        _ = (if mirror then (-1 : ℝ) else 1) *
              (m.configurationSign cfg d *
                permHandedness (m.ligandPermAt e d)) *
                permHandedness (m.ligandPermAt e d) := by
              rw [← signLaw]
              ring
        _ = ((if mirror then (-1 : ℝ) else 1) *
                m.configurationSign cfg d) *
              (permHandedness (m.ligandPermAt e d) *
                permHandedness (m.ligandPermAt e d)) := by ring
        _ = (if mirror then (-1 : ℝ) else 1) *
              m.configurationSign cfg d := by
              rw [ligandSignSquared]
              ring
    calc
      sU * eU =
          (m.configurationSign cfg (m.centerPerm e d) *
              permHandedness alphaG) *
            ((permHandedness alphaG *
                permHandedness (m.ligandPermAt e d) *
                permHandedness alphaF) * eF) := by
            rw [signU, parityTransport, permutationSign]
      _ = ((m.configurationSign cfg (m.centerPerm e d) *
                permHandedness (m.ligandPermAt e d)) *
              (permHandedness alphaF * eF)) *
            (permHandedness alphaG * permHandedness alphaG) := by ring
      _ = (m.configurationSign cfg (m.centerPerm e d) *
              permHandedness (m.ligandPermAt e d)) *
            (permHandedness alphaF * eF) := by
            rw [frameSignSquared]
            ring
      _ = ((if mirror then (-1 : ℝ) else 1) *
              m.configurationSign cfg d) *
            (permHandedness alphaF * eF) := by
            rw [reversedSignLaw]
      _ = (if mirror then (-1 : ℝ) else 1) * (sF * eF) := by
            rw [signF]
            ring
  have signF_eq_one_or_neg_one : sF = 1 ∨ sF = -1 := by
    rw [signF]
    exact generalMul_eq_one_or_neg_one
      (permHandedness_eq_one_or_eq_neg_one (cfg d))
      (permHandedness_eq_one_or_eq_neg_one alphaF)
  have productSign : sF * eF = 1 ∨ sF * eF = -1 :=
    generalMul_eq_one_or_neg_one signF_eq_one_or_neg_one
      (parityFactor_eq_one_or_neg_one _)
  have reflectedLabel : RS.ofHandedness (sU * eU) =
      (if mirror then RS.swap (RS.ofHandedness (sF * eF))
        else RS.ofHandedness (sF * eF)) := by
    rw [signProduct]
    cases mirror with
    | false => simp
    | true =>
        rw [show (if true then (-1 : ℝ) else 1) = -1 by norm_num]
        rw [neg_mul, one_mul, RS.ofHandedness_neg (sF * eF) productSign]
        simp
  rw [stateU, labelU_eq, stateF, labelF_eq, reflectedLabel]
  cases mirror <;> rfl








/-- **Actual positivity of the generated reference state at a general rigid physical frame.**  At
an actual real occurrence with a four-ligand frame, a real tetrahedral centre whose graph is
constitutionally rigid, and nondegenerate actual rational coordinates, the generated reference state
is `some (.chiral rs)` for an actual descriptor `rs`.  No desired label, sign, sort covariance or
reader relation is assumed. -/
theorem exists_chiral_referenceState_of_generalRigidFrame
    (input : LocalizedUniversalReference.Input)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigidGraphAt input.certified.moleculeGraph center.1)
    (hacyc : input.certified.moleculeGraph.Acyclic)
    (hsimple : input.certified.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt index) =
        some (pointsAt index))
    (nonzero : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0) :
    ∃ rs : RS, LocalizedUniversalReference.referenceState input target = some (.chiral rs) := by
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    simp [LocalizedUniversalReference.carrierFuel,
      LocalizedExtendedShortCircuit.carrierFuel,
      LocalizedReference.Input.molecule]
  obtain ⟨alpha, ligandLink⟩ :=
    exists_ligandPermutation_of_actualFrame input.certified target frame derived center centerReal
      hsimple hacyc enough
  have writtenParity :
      AuthoritativeChemicalInput.RationalTetrahedralInputParity
        [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3]
        (parityOfVolumeSign
          (rationalVolumeSign
            (CartesianPoint3.orientedVolume
              (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3)))) :=
    rationalTetrahedralInputParity_parityOfVolumeSign
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) nonzero
  obtain ⟨tracked, _computed, _pseudo, state⟩ :=
    referenceState_reader_eq_chiral_of_constitutionallyRigidFrame_noInterface
      input noDouble target frame derived center centerReal rigid hacyc hsimple hcharge
      alpha ligandLink pointsAt spatial
      (parityOfVolumeSign
        (rationalVolumeSign
          (CartesianPoint3.orientedVolume
            (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3))))
      writtenParity
  exact ⟨_, state⟩












theorem referenceState_generalRigidAutomorphism_label_sign_iff
    (input : LocalizedUniversalReference.Input)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (hsimple : input.certified.moleculeGraph.SimpleBonded)
    (hacyc : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (m : MultiCenterMolecule input.certified.Atom)
    (molEq : m.mol = input.certified.moleculeGraph)
    (cfg : m.Configuration) (d : m.Center) (e : m.Aut) (mirror : Bool)
    (root : input.certified.Atom)
    (rootFixed : (e : Equiv.Perm input.certified.Atom) root = root)
    (t u : LocalizedUniversalReference.Occurrence input)
    (rootF : t.1.root = root) (rootU : u.1.root = root)
    (F G : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derivedF : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame t F)
    (derivedG : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame u G)
    (centerF centerU : input.certified.TetrahedralCenter)
    (centerRealF : input.certified.RealTetrahedralCenterNode t.1.node centerF)
    (centerRealU : input.certified.RealTetrahedralCenterNode u.1.node centerU)
    (centerF_at : centerF.1 = d.1)
    (centerU_at : centerU.1 = (m.centerPerm e d).1)
    (rigidF : ConstitutionallyRigidGraphAt input.certified.moleculeGraph centerF.1)
    (rigidU : ConstitutionallyRigidGraphAt input.certified.moleculeGraph centerU.1)
    (alphaF alphaG : Equiv.Perm (Fin 4))
    (matchF : ActualFrameLigandMatch input m F d alphaF)
    (matchG : ActualFrameLigandMatch input m G (m.centerPerm e d) alphaG)
    (pointsF pointsU : Fin 4 → CartesianPoint3)
    (spatialF : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (F.cursorAt index) =
        some (pointsF index))
    (spatialU : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (G.cursorAt index) =
        some (pointsU index))
    (calibrationF : PhysicalFrameCalibration m cfg d alphaF pointsF)
    (calibrationU : PhysicalFrameCalibration m cfg (m.centerPerm e d) alphaG pointsU) :
    LocalizedUniversalReference.referenceState input u =
      (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input t) ↔
    m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
      (if mirror then -1 else 1) *
        m.configurationSign cfg (m.centerPerm e d) := by
  constructor
  · -- Actual label relation `→` physical sign law.  No desired sign is assumed.
    intro stateEq
    by_contra signFails
    have hA : m.configurationSign cfg d = 1 ∨ m.configurationSign cfg d = -1 :=
      permHandedness_eq_one_or_eq_neg_one (cfg d)
    have hB :
        m.configurationSign cfg (m.centerPerm e d) = 1 ∨
          m.configurationSign cfg (m.centerPerm e d) = -1 :=
      permHandedness_eq_one_or_eq_neg_one (cfg (m.centerPerm e d))
    have hL :
        permHandedness (m.ligandPermAt e d) = 1 ∨
          permHandedness (m.ligandPermAt e d) = -1 :=
      permHandedness_eq_one_or_eq_neg_one (m.ligandPermAt e d)
    have oppositeSignLaw :
        m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
          (if (!mirror) then (-1 : ℝ) else 1) *
            m.configurationSign cfg (m.centerPerm e d) :=
      signLaw_eq_opposite_of_not_eq hA hB hL mirror signFails
    have oppositeState :
        LocalizedUniversalReference.referenceState input u =
          (if (!mirror) then
              CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel
            else id)
            (LocalizedUniversalReference.referenceState input t) :=
      referenceState_generalRigidAutomorphism_label_covariance
        input noDouble hsimple hacyc hcharge m molEq cfg d e (!mirror) root rootFixed
        t u rootF rootU F G derivedF derivedG centerF centerU centerRealF centerRealU
        centerF_at centerU_at rigidF rigidU alphaF alphaG matchF matchG
        pointsF pointsU spatialF spatialU calibrationF calibrationU oppositeSignLaw
    have statesAgree :
        (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
            (LocalizedUniversalReference.referenceState input t) =
          (if (!mirror) then
              CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel
            else id)
            (LocalizedUniversalReference.referenceState input t) :=
      stateEq.symm.trans oppositeState
    have reflected :
        LocalizedUniversalReference.referenceState input t =
          CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel
            (LocalizedUniversalReference.referenceState input t) := by
      cases mirror with
      | false => simpa using statesAgree
      | true => simpa using statesAgree.symm
    obtain ⟨rs, rsEq⟩ :=
      exists_chiral_referenceState_of_generalRigidFrame
        input noDouble t F derivedF centerF centerRealF rigidF hacyc hsimple hcharge
        pointsF spatialF calibrationF.written_nondegenerate
    rw [rsEq] at reflected
    cases rs <;>
      simp [CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel,
        CertifiedLocalizedCIPInput.reflectUppercaseAuxiliaryLabel, RS.swap] at reflected
  · -- Physical sign law `→` actual label relation (general forward covariance).
    intro signLaw
    exact referenceState_generalRigidAutomorphism_label_covariance
      input noDouble hsimple hacyc hcharge m molEq cfg d e mirror root rootFixed
      t u rootF rootU F G derivedF derivedG centerF centerU centerRealF centerRealU
      centerF_at centerU_at rigidF rigidU alphaF alphaG matchF matchG
      pointsF pointsU spatialF spatialU calibrationF calibrationU signLaw

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.multiCenterAutToGraphAut
assert_kernel_only TetraStereo.OneCenter.multiCenterAutToGraphAut_coe
assert_kernel_only TetraStereo.OneCenter.compareLocalizedOccurrenceThroughRule5At?_eq_constitutional
assert_kernel_only TetraStereo.OneCenter.exists_localizedAutCursorCorrespondence_of_actualFrame
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCompoundRule45Key?_rule4a_of_frame
assert_kernel_only TetraStereo.OneCenter.constitutionalCompare_transport_of_actualFrameCorrespondence
assert_kernel_only TetraStereo.OneCenter.compoundKeyRank_compare_eq_of_actualFrameCorrespondence
assert_kernel_only TetraStereo.OneCenter.trackedHighestFirst_eq_map_of_compoundKeyRankTransport
assert_kernel_only TetraStereo.OneCenter.referenceState_generalRigidAutomorphism_label_covariance
assert_kernel_only TetraStereo.OneCenter.exists_chiral_referenceState_of_generalRigidFrame
assert_kernel_only TetraStereo.OneCenter.referenceState_generalRigidAutomorphism_label_sign_iff

end TetraStereo.OneCenter
