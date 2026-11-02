import TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs.DiagramTopologyConsistency
import TetraStereo.KernelOnly

set_option autoImplicit false






















namespace TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs

open TetraStereo.OneCenter

private def carbon : PeriodicElement := (PeriodicElement.ofAtomicNumber? 6).get (by decide)

private def carbonAtom : SemanticAtom := { element := carbon }

private def hydrogen : PeriodicElement := (PeriodicElement.ofAtomicNumber? 1).get (by decide)

private def hydrogenAtom : SemanticAtom := { element := hydrogen }

private def boron : PeriodicElement := (PeriodicElement.ofAtomicNumber? 5).get (by decide)

private def boronAtom : SemanticAtom := { element := boron }

/-! ### Closed parser directional-bond acceptance -/

/-- A two-carbon molecule whose only recorded bond is a directional (`up`) bond. -/
private def directionalMolecule : RawMolecule where
  atoms := [AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C]
  bonds := [{ source := 0, target := 1, kind := ParsedBondKind.up }]

theorem parser_directional_bond_converts :
    directionalMolecule.toAuthoritativeChemicalInput?.isSome = true := by decide

/-- The input actually materialized from the directional parser bond is topology-consistent. -/
theorem parser_directional_bond_topology_consistent :
    (match directionalMolecule.toAuthoritativeChemicalInput? with
      | some source => source.diagramBinaryTopologyConsistent?
      | none => false) = true := by decide

/-- The consistency of any input materialized from the directional parser bond follows from the
general derivation, assuming only successful conversion — no consistency premise. -/
theorem parser_directional_bond_derived_consistency
    (source : AuthoritativeChemicalInput)
    (converted : directionalMolecule.toAuthoritativeChemicalInput? = some source) :
    source.DiagramBinaryTopologyConsistent :=
  directionalMolecule.toAuthoritativeChemicalInput?_diagramTopologyConsistent source converted

/-! ### Dangling in-range wedge refusal -/

/-- Two disconnected carbon atoms (no interactions) with a single in-range `solidWedge`.  This is
exactly the case `DiagramIndicesWellFormed` accepts on bounds alone. -/
private def danglingWedge : AuthoritativeChemicalInput where
  molecule := { atoms := [carbonAtom, carbonAtom], interactions := [] }
  diagram? :=
    some { bonds := [{ source := 0, target := 1, style := DiagramBondStyle.solidWedge }] }

/-- Structural admission is unchanged: the dangling wedge is still structurally admitted. -/
theorem dangling_wedge_structurally_admitted :
    danglingWedge.structurallyWellFormed? = true := by decide

/-- The bounds-only diagram check accepts the dangling wedge. -/
theorem dangling_wedge_indices_well_formed :
    danglingWedge.diagramIndicesWellFormed? = true := by decide

/-- The independent binary-topology contract refuses it: no interaction names `[0, 1]`. -/
theorem dangling_wedge_topology_refused :
    danglingWedge.diagramBinaryTopologyConsistent? = false := by decide

/-- The refusal in proposition form, transported through the kernel reflection. -/
theorem dangling_wedge_not_topology_consistent :
    ¬ danglingWedge.DiagramBinaryTopologyConsistent := by
  intro consistent
  have accepted :=
    (danglingWedge.diagramBinaryTopologyConsistent?_eq_true_iff).mpr consistent
  rw [dangling_wedge_topology_refused] at accepted
  exact Bool.false_ne_true accepted

/-! ### Reverse-orientation acceptance -/

/-- The interaction is written `[0, 1]` but the diagram bond is written `1 → 0`; the reverse
disjunct licenses it, so the orientation is preserved rather than forced. -/
private def reversedWedge : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [carbonAtom, carbonAtom]
      interactions := [{ participants := [0, 1], kind := SemanticInteractionKind.covalent 1 }] }
  diagram? := some { bonds := [{ source := 1, target := 0, style := DiagramBondStyle.plain }] }

theorem reversed_wedge_topology_consistent :
    reversedWedge.diagramBinaryTopologyConsistent? = true := by decide

/-! ### Separation from multicenter conventions -/

/-- A genuine three-centre interaction does not license a binary wedge between two of its centres;
the contract compares the participant list exactly and does not encode multicenter conventions. -/
private def multicenterWedge : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [boronAtom, hydrogenAtom, hydrogenAtom]
      interactions :=
        [{ participants := [0, 1, 2], kind := SemanticInteractionKind.multicenter 2 }] }
  diagram? :=
    some { bonds := [{ source := 0, target := 1, style := DiagramBondStyle.solidWedge }] }

theorem three_participant_interaction_does_not_witness_binary_wedge :
    multicenterWedge.diagramBinaryTopologyConsistent? = false := by decide

/-! ### Absent diagram and non-directional parser bonds -/

private def noDiagramInput : AuthoritativeChemicalInput where
  molecule := { atoms := [carbonAtom], interactions := [] }

/-- No diagram evidence means the contract is vacuously satisfied. -/
theorem absent_diagram_is_vacuously_consistent :
    noDiagramInput.diagramBinaryTopologyConsistent? = true := by decide

private def plainBondMolecule : RawMolecule where
  atoms := [AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C]
  bonds := [{ source := 0, target := 1, kind := ParsedBondKind.single }]

/-- A non-directional parsed bond is dropped by `toDiagramConfiguration`, so the materialized
diagram retains no binary bond. -/
theorem parser_plain_bond_retains_no_diagram_bond :
    (match plainBondMolecule.toAuthoritativeChemicalInput? with
      | some source => source.diagram?.map (fun diagram => diagram.bonds.length)
      | none => none) = some 0 := by decide

/-! ### Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeChemicalInput.diagramBinaryTopologyConsistent?_eq_true_iff

assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.toDiagramConfiguration_bonds

assert_kernel_only
  TetraStereo.OneCenter.diagramBondOfRawBond?_endpoints

assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.diagramTopologyConsistent_of_structureAgreement

assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.toAuthoritativeChemicalInput?_diagramTopologyConsistent

assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.toAuthoritativeChemicalInputWithSpatial?_diagramTopologyConsistent

assert_kernel_only
  TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs.parser_directional_bond_converts

assert_kernel_only
  TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs.parser_directional_bond_topology_consistent

assert_kernel_only
  TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs.parser_directional_bond_derived_consistency

assert_kernel_only
  TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs.dangling_wedge_structurally_admitted

assert_kernel_only
  TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs.dangling_wedge_indices_well_formed

assert_kernel_only
  TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs.dangling_wedge_topology_refused

assert_kernel_only
  TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs.dangling_wedge_not_topology_consistent

assert_kernel_only
  TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs.reversed_wedge_topology_consistent

assert_kernel_only
  TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs.three_participant_interaction_does_not_witness_binary_wedge

assert_kernel_only
  TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs.absent_diagram_is_vacuously_consistent

assert_kernel_only
  TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs.parser_plain_bond_retains_no_diagram_bond

/-- The optional topology contract ignores the interaction kind. A literal two-participant
multicenter record satisfies it; no chemical or drawing interpretation is claimed. -/
private def twoParticipantMulticenterWedge : AuthoritativeChemicalInput :=
  { multicenterWedge with
    molecule := { multicenterWedge.molecule with
      interactions := [{ participants := [0, 1], kind := .multicenter 2 }] } }

theorem two_participant_multicenter_satisfies_topology :
    twoParticipantMulticenterWedge.diagramBinaryTopologyConsistent? = true := by decide

end TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs

assert_kernel_only TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs.two_participant_multicenter_satisfies_topology
