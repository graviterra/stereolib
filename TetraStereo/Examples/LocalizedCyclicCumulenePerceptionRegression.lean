import TetraStereo.OneCenter.LocalizedCyclicCumuleneAuthorityAnalysis

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedCyclicCumulenePerceptionRegression

open OneCenter

private def carbon : PeriodicElement :=
  { atomicNumber := 6, positive := by decide, atMost118 := by decide }

/-- Constitution-level fixture matching the eleven-membered all-double-ring topology used for
the P-31.1.3.3 `cycloundecaundecaene` parent example.  Geometry and a final stereodescriptor are
intentionally absent: this regression tests fully cyclic cumulene *perception* only. -/
private def cyclicUndecaeneInput : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := List.replicate 11 { element := carbon }
        interactions :=
          [{ participants := [0, 1], kind := .covalent 2 },
           { participants := [1, 2], kind := .covalent 2 },
           { participants := [2, 3], kind := .covalent 2 },
           { participants := [3, 4], kind := .covalent 2 },
           { participants := [4, 5], kind := .covalent 2 },
           { participants := [5, 6], kind := .covalent 2 },
           { participants := [6, 7], kind := .covalent 2 },
           { participants := [7, 8], kind := .covalent 2 },
           { participants := [8, 9], kind := .covalent 2 },
           { participants := [9, 10], kind := .covalent 2 },
           { participants := [10, 0], kind := .covalent 2 }] } }

private def certifiedCyclicUndecaene : CertifiedAuthoritativeChemicalInput :=
  { input := cyclicUndecaeneInput
    structurallyWellFormed :=
      (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
        cyclicUndecaeneInput).mp (by decide) }

private def localizedCyclicUndecaene : CertifiedLocalizedCIPInput :=
  { certified := certifiedCyclicUndecaene
    graphReady :=
      (SemanticMolecule.localizedCIPGraphReady?_eq_true_iff
        certifiedCyclicUndecaene.input.molecule).mp (by decide) }

private def atom0 : localizedCyclicUndecaene.Atom := ⟨0, by decide⟩
private def atom1 : localizedCyclicUndecaene.Atom := ⟨1, by decide⟩
private def atom2 : localizedCyclicUndecaene.Atom := ⟨2, by decide⟩
private def atom3 : localizedCyclicUndecaene.Atom := ⟨3, by decide⟩
private def atom4 : localizedCyclicUndecaene.Atom := ⟨4, by decide⟩
private def atom5 : localizedCyclicUndecaene.Atom := ⟨5, by decide⟩
private def atom6 : localizedCyclicUndecaene.Atom := ⟨6, by decide⟩
private def atom7 : localizedCyclicUndecaene.Atom := ⟨7, by decide⟩
private def atom8 : localizedCyclicUndecaene.Atom := ⟨8, by decide⟩
private def atom9 : localizedCyclicUndecaene.Atom := ⟨9, by decide⟩
private def atom10 : localizedCyclicUndecaene.Atom := ⟨10, by decide⟩

private theorem reachable_from_atom0
    (atom : localizedCyclicUndecaene.Atom) :
    localizedCyclicUndecaene.localizedOrderTwoSimpleGraph.Reachable atom0 atom := by
  have edge01 : localizedCyclicUndecaene.localizedOrderTwoSimpleGraph.Adj atom0 atom1 :=
    by rw [localizedCyclicUndecaene.localizedOrderTwoSimpleGraph_adj]; decide
  have edge12 : localizedCyclicUndecaene.localizedOrderTwoSimpleGraph.Adj atom1 atom2 :=
    by rw [localizedCyclicUndecaene.localizedOrderTwoSimpleGraph_adj]; decide
  have edge23 : localizedCyclicUndecaene.localizedOrderTwoSimpleGraph.Adj atom2 atom3 :=
    by rw [localizedCyclicUndecaene.localizedOrderTwoSimpleGraph_adj]; decide
  have edge34 : localizedCyclicUndecaene.localizedOrderTwoSimpleGraph.Adj atom3 atom4 :=
    by rw [localizedCyclicUndecaene.localizedOrderTwoSimpleGraph_adj]; decide
  have edge45 : localizedCyclicUndecaene.localizedOrderTwoSimpleGraph.Adj atom4 atom5 :=
    by rw [localizedCyclicUndecaene.localizedOrderTwoSimpleGraph_adj]; decide
  have edge56 : localizedCyclicUndecaene.localizedOrderTwoSimpleGraph.Adj atom5 atom6 :=
    by rw [localizedCyclicUndecaene.localizedOrderTwoSimpleGraph_adj]; decide
  have edge67 : localizedCyclicUndecaene.localizedOrderTwoSimpleGraph.Adj atom6 atom7 :=
    by rw [localizedCyclicUndecaene.localizedOrderTwoSimpleGraph_adj]; decide
  have edge78 : localizedCyclicUndecaene.localizedOrderTwoSimpleGraph.Adj atom7 atom8 :=
    by rw [localizedCyclicUndecaene.localizedOrderTwoSimpleGraph_adj]; decide
  have edge89 : localizedCyclicUndecaene.localizedOrderTwoSimpleGraph.Adj atom8 atom9 :=
    by rw [localizedCyclicUndecaene.localizedOrderTwoSimpleGraph_adj]; decide
  have edge910 : localizedCyclicUndecaene.localizedOrderTwoSimpleGraph.Adj atom9 atom10 :=
    by rw [localizedCyclicUndecaene.localizedOrderTwoSimpleGraph_adj]; decide
  fin_cases atom
  · exact .rfl
  · simpa [atom0, atom1] using edge01.reachable
  · simpa [atom0, atom2] using edge01.reachable.trans edge12.reachable
  · simpa [atom0, atom3] using
      edge01.reachable.trans edge12.reachable |>.trans edge23.reachable
  · simpa [atom0, atom4] using
      ((edge01.reachable.trans edge12.reachable).trans edge23.reachable).trans
        edge34.reachable
  · simpa [atom0, atom5] using
      (((edge01.reachable.trans edge12.reachable).trans edge23.reachable).trans
        edge34.reachable).trans edge45.reachable
  · simpa [atom0, atom6] using
      ((((edge01.reachable.trans edge12.reachable).trans edge23.reachable).trans
        edge34.reachable).trans edge45.reachable).trans edge56.reachable
  · simpa [atom0, atom7] using
      (((((edge01.reachable.trans edge12.reachable).trans edge23.reachable).trans
        edge34.reachable).trans edge45.reachable).trans edge56.reachable).trans
          edge67.reachable
  · simpa [atom0, atom8] using
      ((((((edge01.reachable.trans edge12.reachable).trans edge23.reachable).trans
        edge34.reachable).trans edge45.reachable).trans edge56.reachable).trans
          edge67.reachable).trans edge78.reachable
  · simpa [atom0, atom9] using
      (((((((edge01.reachable.trans edge12.reachable).trans edge23.reachable).trans
        edge34.reachable).trans edge45.reachable).trans edge56.reachable).trans
          edge67.reachable).trans edge78.reachable).trans edge89.reachable
  · simpa [atom0, atom10] using
      ((((((((edge01.reachable.trans edge12.reachable).trans edge23.reachable).trans
        edge34.reachable).trans edge45.reachable).trans edge56.reachable).trans
          edge67.reachable).trans edge78.reachable).trans edge89.reachable).trans
            edge910.reachable

private theorem componentAtoms_atom0_eq_univ :
    localizedCyclicUndecaene.localizedOrderTwoComponentAtoms atom0 = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro atom
  rw [localizedCyclicUndecaene.mem_localizedOrderTwoComponentAtoms_iff]
  exact reachable_from_atom0 atom

private def cyclicComponent :
    localizedCyclicUndecaene.LocalizedCyclicCumuleneComponent :=
  { representative := atom0 }

private theorem cyclicComponent_declarative :
    localizedCyclicUndecaene.DeclarativeLocalizedCyclicCumuleneComponent
      cyclicComponent := by
  change localizedCyclicUndecaene.DeclarativeLocalizedCyclicCumuleneComponentAt atom0
  constructor
  · rw [componentAtoms_atom0_eq_univ]
    decide
  constructor
  · intro atom _member
    unfold CertifiedLocalizedCIPInput.localizedOrderTwoNeighbors
    rw [Finset.length_sort]
    fin_cases atom <;> decide
  · intro atom _member
    change 0 ≤ atom.val
    omega

/-- The complete eleven-membered all-double component is discovered exactly once. -/
theorem cyclic_undecaene_component_is_discovered :
    cyclicComponent ∈ localizedCyclicUndecaene.localizedCyclicCumuleneComponents :=
  (localizedCyclicUndecaene.mem_localizedCyclicCumuleneComponents_iff
    cyclicComponent).mpr cyclicComponent_declarative

/-- The fully cyclic component cannot be reinterpreted as an open axial terminal root. -/
theorem cyclic_undecaene_has_no_open_axial_root
    (atom : localizedCyclicUndecaene.Atom) :
    localizedCyclicUndecaene.localizedAxialRootCandidateAt? atom = none := by
  apply OneCenter.CertifiedLocalizedCIPInput.DeclarativeLocalizedCyclicCumuleneComponent.no_open_axial_root
    localizedCyclicUndecaene cyclicComponent_declarative atom
  change atom ∈ localizedCyclicUndecaene.localizedOrderTwoComponentAtoms atom0
  rw [componentAtoms_atom0_eq_univ]
  simp

/-- Its authority route is the P-31 fully cyclic parent class, not P-93's open-terminal
cumulene descriptor schema. -/
theorem cyclic_undecaene_authority_boundary :
    BlueBookP93.Cyclic.P31FullyCyclicCumuleneParentApplies .fullyCyclicCumulene ∧
      ¬BlueBookP93.Cyclic.OpenTerminalCumuleneSchemaApplies .fullyCyclicCumulene :=
  cyclicComponent_declarative.authority_topology

private def cyclicAuthorityBoundary :
    localizedCyclicUndecaene.LocalizedFullyCyclicCumuleneAuthorityBoundary :=
  { component := cyclicComponent }

/-- The public molecule-wide boundary analysis retains the P-31 component instead of silently
dropping it when no open-terminal cumulene descriptor family applies. -/
theorem cyclic_undecaene_authority_boundary_is_reported :
    cyclicAuthorityBoundary ∈
      localizedCyclicUndecaene.analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries := by
  apply (OneCenter.CertifiedLocalizedCIPInput.mem_analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries_iff
      localizedCyclicUndecaene cyclicAuthorityBoundary).mpr
  exact OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedFullyCyclicCumuleneAuthorityBoundary_of_component
      localizedCyclicUndecaene cyclicComponent cyclicComponent_declarative

/-- In particular, neither parity branch of the P-93 terminal-ligand cumulene schema can assign
any descriptor to this closed component. -/
theorem cyclic_undecaene_has_no_open_terminal_cumulene_descriptor
    (parity : BlueBookP93.Cyclic.OpenCumuleneParity)
    (descriptor : BlueBookP93.Acyclic.Descriptor) :
    ¬BlueBookP93.Cyclic.OpenTerminalCumuleneDescriptorApplies
      .fullyCyclicCumulene parity descriptor :=
  BlueBookP93.Cyclic.fully_cyclic_cumulene_has_no_open_terminal_descriptor
    parity descriptor

#check OneCenter.CertifiedLocalizedCIPInput.localizedCyclicCumuleneComponentAt?_eq_some_iff
#check OneCenter.CertifiedLocalizedCIPInput.mem_localizedCyclicCumuleneComponents_iff
#check OneCenter.CertifiedLocalizedCIPInput.localizedCyclicCumuleneComponents_nodup
#check OneCenter.CertifiedLocalizedCIPInput.localizedCyclicCumuleneComponentContaining?_eq_some_iff
#check OneCenter.CertifiedLocalizedCIPInput.DeclarativeLocalizedCyclicCumuleneComponent.no_open_axial_root
#check OneCenter.CertifiedLocalizedCIPInput.mem_analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries_iff

end TetraStereo.Examples.LocalizedCyclicCumulenePerceptionRegression
