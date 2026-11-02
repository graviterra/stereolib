import TetraStereo.OneCenter.FinitePhysicalBranchTransport
import TetraStereo.OneCenter.FinitePrunedMapSearch
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.FinitePhysicalBranchSearch

open FinitePhysicalBranchTransport RootedTetrahedralBranchSymmetry

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (m : MultiCenterMolecule V)

/-- The checks already forced by an assignment on the sources in `seen`. Bond constraints are
checked on every pair in the prefix, so a failed edge or non-edge can prune before completion. -/
def PrefixCompatible (f : V → V) (seen : List V) (c : m.Center) (i j : Fin 4) : Prop :=
  (∀ u ∈ seen, ∀ v ∈ seen, f u = f v → u = v) ∧
  (∀ v ∈ seen, m.mol.atomZ (f v) = m.mol.atomZ v) ∧
  (∀ v ∈ seen, m.mol.atomMass (f v) = m.mol.atomMass v) ∧
  (∀ v ∈ seen, m.mol.formalCharge (f v) = m.mol.formalCharge v) ∧
  (∀ v ∈ seen, v ∈ m.centers ↔ f v ∈ m.centers) ∧
  (∀ u ∈ seen, ∀ v ∈ seen, m.mol.bond (f u) (f v) = m.mol.bond u v) ∧
  (c.1 ∈ seen → f c.1 = c.1) ∧
  (m.ligandAtomAt c i ∈ seen → f (m.ligandAtomAt c i) = m.ligandAtomAt c j)

theorem prefixCompatible_congr {f g : V → V} {seen : List V}
    (c : m.Center) (i j : Fin 4)
    (agree : ∀ v ∈ seen, f v = g v) :
    PrefixCompatible m f seen c i j ↔ PrefixCompatible m g seen c i j := by
  unfold PrefixCompatible
  constructor
  · rintro ⟨hinj, hz, hm, hq, hc, hb, hr, hl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu v hv hEq
      apply hinj u hu v hv
      rw [agree u hu, agree v hv]
      exact hEq
    · intro v hv; rw [← agree v hv]; exact hz v hv
    · intro v hv; rw [← agree v hv]; exact hm v hv
    · intro v hv; rw [← agree v hv]; exact hq v hv
    · intro v hv; rw [← agree v hv]; exact hc v hv
    · intro u hu v hv; rw [← agree u hu, ← agree v hv]; exact hb u hu v hv
    · intro hv; rw [← agree c.1 hv]; exact hr hv
    · intro hv; rw [← agree (m.ligandAtomAt c i) hv]; exact hl hv
  · rintro ⟨hinj, hz, hm, hq, hc, hb, hr, hl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu v hv hEq
      apply hinj u hu v hv
      rw [← agree u hu, ← agree v hv]
      exact hEq
    · intro v hv; rw [agree v hv]; exact hz v hv
    · intro v hv; rw [agree v hv]; exact hm v hv
    · intro v hv; rw [agree v hv]; exact hq v hv
    · intro v hv; rw [agree v hv]; exact hc v hv
    · intro u hu v hv; rw [agree u hu, agree v hv]; exact hb u hu v hv
    · intro hv; rw [agree c.1 hv]; exact hr hv
    · intro hv; rw [agree (m.ligandAtomAt c i) hv]; exact hl hv

omit [Fintype V] in
theorem update_agrees_on_seen {f : V → V} {seen : List V} {x y : V}
    (hx : x ∉ seen) : ∀ v ∈ seen, Function.update f x y v = f v := by
  intro v hv
  apply Function.update_of_ne
  intro h
  subst x
  exact hx hv

theorem prefixCompatible_update_congr {f : V → V} {seen : List V} {x y : V}
    (c : m.Center) (i j : Fin 4)
    (hx : x ∉ seen) :
    PrefixCompatible m (Function.update f x y) seen c i j ↔ PrefixCompatible m f seen c i j := by
  apply prefixCompatible_congr m c i j (update_agrees_on_seen hx)

/-- A valid full automorphism satisfies every prefix constraint on any list of already assigned
sources. This is the pruning soundness fact used by guided completeness. -/
theorem prefixCompatible_of_fullCandidate (E : m.Aut) (c : m.Center) (i j : Fin 4)
    (rootFixed : (E : Equiv.Perm V) c.1 = c.1)
    (ligandMapped : (E : Equiv.Perm V) (m.ligandAtomAt c i) = m.ligandAtomAt c j)
    (f : V → V) (seen : List V)
    (agree : ∀ v ∈ seen, f v = (E : Equiv.Perm V) v) :
    PrefixCompatible m f seen c i j := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu v hv hEq
    have h := (E : Equiv.Perm V).injective
    apply h
    rw [← agree u hu, ← agree v hv]
    exact hEq
  · intro v hv
    rw [agree v hv]
    exact (MoleculeGraph.Aut.atomZ_eq (m := m.mol) ⟨(E : Equiv.Perm V), E.property.1⟩ v)
  · intro v hv
    rw [agree v hv]
    exact (MoleculeGraph.Aut.atomMass_eq (m := m.mol) ⟨(E : Equiv.Perm V), E.property.1⟩ v)
  · intro v hv
    rw [agree v hv]
    exact (MoleculeGraph.Aut.formalCharge_eq (m := m.mol) ⟨(E : Equiv.Perm V), E.property.1⟩ v)
  · intro v hv
    rw [agree v hv]
    exact (MultiCenterMolecule.Aut.mem_centers_iff (m := m) E v)
  · intro u hu v hv
    rw [agree u hu, agree v hv]
    exact (MoleculeGraph.Aut.bond_eq (m := m.mol) ⟨(E : Equiv.Perm V), E.property.1⟩ u v)
  · intro hc
    rw [agree c.1 hc]
    exact rootFixed
  · intro hi
    rw [agree (m.ligandAtomAt c i) hi]
    exact ligandMapped

/-- Forward sign equation computed from a total function. Its executable definition needs no
permutation inverse; on a genuine automorphism it is exactly the accepted `signOK`. -/
def functionSignOK (cfg : m.Configuration) (mirror : Bool)
    (f : V → V) (d : m.Center) : Bool :=
  if h : f d.1 ∈ m.centers then
    decide (Equiv.Perm.sign (cfg d) *
      funSign (fun k => ligIndex m ⟨f d.1, h⟩ (f (m.ligandAtomAt d k))) =
      (if mirror then -1 else 1) * Equiv.Perm.sign (cfg ⟨f d.1, h⟩))
  else false

/-- Full forward checks over a total function. At leaves the search additionally checks
injectivity, making this exactly the existing automorphism and global-sign candidate condition. -/
def fullFunctionCandidateOK (cfg : m.Configuration) (c : m.Center) (i j : Fin 4)
    (mirror : Bool) (f : V → V) : Bool :=
  decide (Function.Injective f) &&
    decide (((∀ v, m.mol.atomZ (f v) = m.mol.atomZ v) ∧
      (∀ v, m.mol.atomMass (f v) = m.mol.atomMass v) ∧
      (∀ v, m.mol.formalCharge (f v) = m.mol.formalCharge v) ∧
      (∀ u v, m.mol.bond (f u) (f v) = m.mol.bond u v)) ∧
      (∀ v, v ∈ m.centers ↔ f v ∈ m.centers)) &&
    decide (f c.1 = c.1) &&
    decide (f (m.ligandAtomAt c i) = m.ligandAtomAt c j) &&
    decide (∀ d : m.Center, d.1 ∈ branchReachSet m c i →
      functionSignOK m cfg mirror f d = true)

theorem functionSignOK_perm (cfg : m.Configuration) (mirror : Bool) (E : Equiv.Perm V)
    (d : m.Center) :
    functionSignOK m cfg mirror E d = signOK m cfg mirror E d := by
  unfold functionSignOK signOK localFun
  split_ifs <;> rfl

theorem fullFunctionCandidateOK_perm (cfg : m.Configuration) (c : m.Center) (i j : Fin 4)
    (mirror : Bool) (E : Equiv.Perm V) :
    fullFunctionCandidateOK m cfg c i j mirror E = candidateOK m cfg c i j mirror E := by
  have hInjective : Function.Injective (E : V → V) := E.injective
  simp [fullFunctionCandidateOK, candidateOK, isAutCheck, functionSignOK_perm,
    hInjective]

/-- Boolean realization of `PrefixCompatible`, using finite folds rather than a classical
proposition decider. -/
def prefixCompatibleCheck (f : V → V) (seen : List V) (c : m.Center)
    (i j : Fin 4) : Bool :=
  seen.all (fun u => seen.all (fun v => decide (f u = f v → u = v))) &&
  seen.all (fun v => decide (m.mol.atomZ (f v) = m.mol.atomZ v)) &&
  seen.all (fun v => decide (m.mol.atomMass (f v) = m.mol.atomMass v)) &&
  seen.all (fun v => decide (m.mol.formalCharge (f v) = m.mol.formalCharge v)) &&
  seen.all (fun v => decide (v ∈ m.centers ↔ f v ∈ m.centers)) &&
    seen.all (fun u => seen.all (fun v => decide (m.mol.bond (f u) (f v) = m.mol.bond u v))) &&
    (if c.1 ∈ seen then decide (f c.1 = c.1) else true) &&
    (if m.ligandAtomAt c i ∈ seen then
      decide (f (m.ligandAtomAt c i) = m.ligandAtomAt c j) else true)

theorem prefixCompatibleCheck_eq_true_iff (f : V → V) (seen : List V)
    (c : m.Center) (i j : Fin 4) :
    prefixCompatibleCheck m f seen c i j = true ↔ PrefixCompatible m f seen c i j := by
  unfold prefixCompatibleCheck PrefixCompatible
  simp [List.all_eq_true, decide_eq_true_eq, and_assoc, imp_iff_not_or]

/-- Prefix-pruned depth-first search. It expands one source vertex per step and considers only
target images that preserve all currently mapped constraints. -/
def searchAux (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) (mirror : Bool)
    (targets : List V) :
    List V → List V → (V → V) → Bool
  := FinitePrunedMapSearch.searchAux
    (fun f seen => prefixCompatibleCheck m f seen c i j)
    (fun f => fullFunctionCandidateOK m cfg c i j mirror f) targets

/-- Proof-level trace of a successful search, including every incremental prefix gate. -/
def SearchTrace (targets : List V) (c : m.Center) (i j : Fin 4) :
    List V → List V → (V → V) → (V → V) → Prop
  := FinitePrunedMapSearch.SearchTrace
    (fun f seen => prefixCompatibleCheck m f seen c i j) targets

theorem searchAux_eq_true_iff_trace (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) (mirror : Bool) (targets sources seen : List V) (f : V → V) :
    searchAux m cfg c i j mirror targets sources seen f = true ↔
      ∃ result, SearchTrace m targets c i j sources seen f result ∧
        fullFunctionCandidateOK m cfg c i j mirror result = true := by
  simpa [searchAux, SearchTrace] using
    (FinitePrunedMapSearch.searchAux_eq_true_iff_trace
      (fun f seen => prefixCompatibleCheck m f seen c i j)
      (fun f => fullFunctionCandidateOK m cfg c i j mirror f)
      targets sources seen f)

theorem fullFunctionCandidateOK_true_exists_candidate (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) (mirror : Bool) (f : V → V)
    (h : fullFunctionCandidateOK m cfg c i j mirror f = true) :
    ∃ e : Equiv.Perm V, candidateOK m cfg c i j mirror e = true := by
  have hparts := h
  simp only [fullFunctionCandidateOK, Bool.and_eq_true, decide_eq_true_eq] at hparts
  have hinj : Function.Injective f := hparts.1.1.1.1
  let e : Equiv.Perm V := Equiv.ofBijective f
    ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  refine ⟨e, ?_⟩
  rw [← fullFunctionCandidateOK_perm m cfg c i j mirror e]
  simpa [e] using h

theorem searchAux_sound (cfg : m.Configuration) (c : m.Center) (i j : Fin 4)
    (mirror : Bool) (targets sources seen : List V) (f : V → V)
    (h : searchAux m cfg c i j mirror targets sources seen f = true) :
    ∃ e : Equiv.Perm V, candidateOK m cfg c i j mirror e = true := by
  obtain ⟨result, _trace, hfull⟩ :=
    (searchAux_eq_true_iff_trace m cfg c i j mirror targets sources seen f).mp h
  exact fullFunctionCandidateOK_true_exists_candidate m cfg c i j mirror result hfull

theorem searchAux_true_of_candidate (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) (mirror : Bool) (targets sources seen : List V) (f : V → V)
    (E : Equiv.Perm V) (candidate : candidateOK m cfg c i j mirror E = true)
    (sourcesNodup : sources.Nodup)
    (sourcesFresh : ∀ v ∈ sources, v ∉ seen)
    (sourcesCovered : ∀ v, v ∈ sources ∨ v ∈ seen)
    (targetsCovered : ∀ v, v ∈ targets)
    (agreement : ∀ v ∈ seen, f v = E v) :
    searchAux m cfg c i j mirror targets sources seen f = true := by
  have parts := candidate
  simp only [candidateOK, Bool.and_eq_true, decide_eq_true_eq] at parts
  rcases parts with ⟨⟨⟨haut, hroot⟩, hlig⟩, _hsigns⟩
  let A : m.Aut := ⟨E, (isAutCheck_iff m E).mp haut⟩
  have leafValid : fullFunctionCandidateOK m cfg c i j mirror E = true := by
    rw [fullFunctionCandidateOK_perm m cfg c i j mirror E]
    exact candidate
  have prefixValid : ∀ (g : V → V) (assigned : List V),
      (∀ v ∈ assigned, g v = E v) → ∀ x, x ∉ assigned →
        prefixCompatibleCheck m (Function.update g x (E x)) (x :: assigned) c i j = true := by
    intro g assigned agree x hx
    let g' := Function.update g x (E x)
    have agree' : ∀ v ∈ x :: assigned, g' v = E v := by
      intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · simp [g', Function.update_self]
      · have hne : x ≠ v := by
          intro h
          subst x
          exact hx hv
        change Function.update g x (E x) v = E v
        rw [Function.update_of_ne hne.symm]
        exact agree v hv
    rw [prefixCompatibleCheck_eq_true_iff]
    exact prefixCompatible_of_fullCandidate m A c i j hroot hlig g' (x :: assigned) agree'
  exact FinitePrunedMapSearch.searchAux_true_of_target
    (fun g assigned => prefixCompatibleCheck m g assigned c i j)
    (fun g => fullFunctionCandidateOK m cfg c i j mirror g)
    targets sources seen f E leafValid sourcesNodup sourcesFresh sourcesCovered
    targetsCovered agreement prefixValid

/-- The public pruned decision. `vertices` is an explicit executable enumeration of the finite
atom type; specialization adapters use `List.finRange` for `Fin n`. -/
def decideBranchTransportPruned (cfg : m.Configuration) (c : m.Center) (i j : Fin 4)
    (mirror : Bool) (vertices : List V) : Bool :=
  searchAux m cfg c i j mirror vertices vertices [] id

theorem decideBranchTransportPruned_eq_decideBranchTransport
    (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) (mirror : Bool)
    (vertices : List V) (verticesNodup : vertices.Nodup)
    (verticesComplete : ∀ v, v ∈ vertices) :
    decideBranchTransportPruned m cfg c i j mirror vertices =
      decideBranchTransport m cfg c i j mirror := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    obtain ⟨e, he⟩ := searchAux_sound m cfg c i j mirror vertices vertices [] id h
    exact (decide_eq_true_iff).2 ⟨e, he⟩
  · intro h
    have candidate : ∃ e : Equiv.Perm V, candidateOK m cfg c i j mirror e = true := by
      exact (decide_eq_true_iff).1 h
    obtain ⟨e, he⟩ := candidate
    exact searchAux_true_of_candidate m cfg c i j mirror vertices vertices [] id e he
      verticesNodup (by simp)
      (fun v => Or.inl (verticesComplete v)) verticesComplete (by simp)

def decideProperTransportPruned (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) (vertices : List V) : Bool :=
  decideBranchTransportPruned m cfg c i j false vertices

def decideMirrorTransportPruned (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) (vertices : List V) : Bool :=
  decideBranchTransportPruned m cfg c i j true vertices

def decideEnantiomorphicPruned (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) (vertices : List V) : Bool :=
  decide (i ≠ j) && decideMirrorTransportPruned m cfg c i j vertices &&
    !decideProperTransportPruned m cfg c i j vertices

def computedPairCountPruned (cfg : m.Configuration) (c : m.Center)
    (vertices : List V) : ℕ :=
  sourceEnantiomorphicPairCount
    (fun a b : Fin 4 => decideEnantiomorphicPruned m cfg c a b vertices = true)

theorem decideProperTransportPruned_eq (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) (vertices : List V) (verticesNodup : vertices.Nodup)
    (verticesComplete : ∀ v, v ∈ vertices) :
    decideProperTransportPruned m cfg c i j vertices = decideProperTransport m cfg c i j := by
  exact decideBranchTransportPruned_eq_decideBranchTransport m cfg c i j false vertices
    verticesNodup verticesComplete

theorem decideMirrorTransportPruned_eq (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) (vertices : List V) (verticesNodup : vertices.Nodup)
    (verticesComplete : ∀ v, v ∈ vertices) :
    decideMirrorTransportPruned m cfg c i j vertices = decideMirrorTransport m cfg c i j := by
  exact decideBranchTransportPruned_eq_decideBranchTransport m cfg c i j true vertices
    verticesNodup verticesComplete

theorem decideEnantiomorphicPruned_eq (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) (vertices : List V) (verticesNodup : vertices.Nodup)
    (verticesComplete : ∀ v, v ∈ vertices) :
    decideEnantiomorphicPruned m cfg c i j vertices = decideEnantiomorphic m cfg c i j := by
  simp [decideEnantiomorphicPruned, decideEnantiomorphic,
    decideMirrorTransportPruned_eq m cfg c i j vertices verticesNodup verticesComplete,
    decideProperTransportPruned_eq m cfg c i j vertices verticesNodup verticesComplete]

theorem computedPairCountPruned_eq (cfg : m.Configuration) (c : m.Center)
    (vertices : List V) (verticesNodup : vertices.Nodup)
    (verticesComplete : ∀ v, v ∈ vertices) :
    computedPairCountPruned m cfg c vertices = computedPairCount m cfg c := by
  unfold computedPairCountPruned computedPairCount
  apply sourceEnantiomorphicPairCount_congr
  intro a b _
  rw [decideEnantiomorphicPruned_eq m cfg c a b vertices verticesNodup verticesComplete]

end TetraStereo.OneCenter.FinitePhysicalBranchSearch

assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchSearch.prefixCompatible_congr
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchSearch.update_agrees_on_seen
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchSearch.prefixCompatible_update_congr
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchSearch.prefixCompatible_of_fullCandidate
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchSearch.prefixCompatibleCheck_eq_true_iff
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchSearch.functionSignOK_perm
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchSearch.fullFunctionCandidateOK_perm
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchSearch.searchAux_eq_true_iff_trace
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchSearch.fullFunctionCandidateOK_true_exists_candidate
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchSearch.searchAux_sound
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchSearch.searchAux_true_of_candidate
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchSearch.decideBranchTransportPruned_eq_decideBranchTransport
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchSearch.decideProperTransportPruned_eq
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchSearch.decideMirrorTransportPruned_eq
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchSearch.decideEnantiomorphicPruned_eq
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchSearch.computedPairCountPruned_eq
