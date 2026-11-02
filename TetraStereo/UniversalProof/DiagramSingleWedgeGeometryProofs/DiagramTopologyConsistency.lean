import TetraStereo.OneCenter.AuthoritativeChemicalInput

set_option autoImplicit false

/-!
# Diagram binary-topology consistency

`AuthoritativeChemicalInput.DiagramIndicesWellFormed`
(`TetraStereo/OneCenter/AuthoritativeChemicalInput.lean:277-289`) checks only index bounds: a
`DiagramBond` whose two endpoints are distinct and in range is accepted there whether or not the
molecule actually carries a corresponding interaction.  A directional/wedge bond drawn on two
disconnected in-range atoms is therefore structurally admitted, and the existing structural
admission says nothing about whether the retained diagram reflects the semantic interaction list.

This module adds an independent, optional contract that closes exactly that graph-level gap while
leaving the existing structural admission untouched:

* `AuthoritativeChemicalInput.DiagramBinaryTopologyConsistent` states that every retained
  `DiagramBond` is realized by a semantic interaction whose participant list is *exactly* the
  ordered pair `[source, target]` or its reverse `[target, source]`.

The executable `Bool` mirror `diagramBinaryTopologyConsistent?` is an actual finite `all`/`any`
check, and `diagramBinaryTopologyConsistent?_eq_true_iff` reflects it into the kernel.  The
contract is then *derived* for any input produced by the real parser materialization
(`RawMolecule.toAuthoritativeChemicalInput?` and its spatial variant) with no consistency premise
assumed: the parser's directional-bond retention provably realizes the invariant.

## What this contract is not

The contract is deliberately **optional and separate**, and every statement below is additive:

* It is **not** folded into `AuthoritativeChemicalInput.StructurallyWellFormed`, so no existing
  admission is narrowed silently.  A dangling in-range wedge is still structurally admitted; it is
  only the separate topology contract that refuses it.
* It does **not** encode multicenter/delocalized coordination conventions.  An interaction
  with three or more participants cannot itself witness this binary participant-list contract.
  Interaction kind and diagram style are unchecked: a two-participant `.multicenter`, ionic or
  hydrogen-bond record can witness it. No drawing convention or chemical-bond approval follows.
* It does **not** assert chemical admissibility, physical three-dimensional drawing interpretation
  (that a wedge means a particular parity or geometry), or source faithfulness.
-/

namespace TetraStereo.OneCenter

/-- The exact single-step materialization performed by `RawMolecule.toDiagramConfiguration`:
directional (`up`/`down`) parsed bonds are retained as directional diagram bonds and every other
parsed bond is dropped.  Named so the binary-topology derivation can reason about the precise
`filterMap` that produces `diagram.bonds` without depending on the source module's inline lambda. -/
def diagramBondOfRawBond? (bond : RawBond) : Option DiagramBond :=
  match bond.kind with
  | .up => some { source := bond.source, target := bond.target, style := .directionalUp }
  | .down => some { source := bond.source, target := bond.target, style := .directionalDown }
  | _ => none

namespace RawMolecule

/-- `toDiagramConfiguration`'s retained-bond list is exactly the named `filterMap` above. -/
theorem toDiagramConfiguration_bonds (molecule : RawMolecule) :
    molecule.toDiagramConfiguration.bonds =
      molecule.bonds.filterMap diagramBondOfRawBond? := rfl

end RawMolecule

/-- A retained diagram bond reproduces the endpoints of the raw bond that materialized it.  This is
the small actual graph invariant the derivation relies on: for the two directional parsed-bond
kinds the materialized diagram bond copies `source` and `target` verbatim. -/
theorem diagramBondOfRawBond?_endpoints {raw : RawBond} {bond : DiagramBond}
    (materialized : diagramBondOfRawBond? raw = some bond) :
    bond.source = raw.source ∧ bond.target = raw.target := by
  rcases raw with ⟨source, target, kind⟩
  cases kind <;> simp only [diagramBondOfRawBond?] at materialized
  all_goals (cases materialized <;> simp)

namespace AuthoritativeChemicalInput

/-- Every retained binary diagram bond is realized by a semantic interaction whose participant
list is exactly `[source, target]` or `[target, source]`.

A `DiagramBond` is inherently binary (one `source`, one `target`); "retained" means it is a member
of `diagram.bonds`.  The contract is vacuous when the diagram evidence channel is absent
(`diagram? = none`).  It compares participant *lists* exactly, so a two-centre wedge is licensed
only by a two-participant interaction naming the same ordered pair (`source`→`target`, the parser's
written orientation) or its reverse. -/
def DiagramBinaryTopologyConsistent (input : AuthoritativeChemicalInput) : Prop :=
  match input.diagram? with
  | none => True
  | some diagram =>
      ∀ bond, bond ∈ diagram.bonds →
        ∃ interaction, interaction ∈ input.molecule.interactions ∧
          (interaction.participants = [bond.source, bond.target] ∨
            interaction.participants = [bond.target, bond.source])

/-- Executable finite `all`/`any` mirror of `DiagramBinaryTopologyConsistent`: for every retained
diagram bond, some semantic interaction has participants exactly `[source, target]` or its reverse.
Vacuously `true` when no diagram evidence is attached. -/
def diagramBinaryTopologyConsistent? (input : AuthoritativeChemicalInput) : Bool :=
  match input.diagram? with
  | none => true
  | some diagram =>
      diagram.bonds.all fun bond =>
        input.molecule.interactions.any fun interaction =>
          decide (interaction.participants = [bond.source, bond.target]) ||
            decide (interaction.participants = [bond.target, bond.source])

/-- Kernel reflection of the executable binary-topology check into its proposition. -/
@[simp] theorem diagramBinaryTopologyConsistent?_eq_true_iff
    (input : AuthoritativeChemicalInput) :
    input.diagramBinaryTopologyConsistent? = true ↔ input.DiagramBinaryTopologyConsistent := by
  cases observed : input.diagram? with
  | none => simp [diagramBinaryTopologyConsistent?, DiagramBinaryTopologyConsistent, observed]
  | some diagram =>
      simp [diagramBinaryTopologyConsistent?, DiagramBinaryTopologyConsistent, observed]

end AuthoritativeChemicalInput

namespace RawMolecule

/-- Any input whose diagram evidence is the actual parser materialization for `molecule` satisfies
diagram binary-topology consistency.  The parser retains only directional bonds, and each retained
bond is the exact pair recorded by the matching `RawBond.toSemanticInteraction`, so the written
orientation `[source, target]` realizes the forward disjunct. -/
theorem diagramTopologyConsistent_of_structureAgreement
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source) :
    source.DiagramBinaryTopologyConsistent := by
  obtain ⟨semanticConverted, diagramConverted⟩ := agreement
  have interactionsConverted :
      source.molecule.interactions = molecule.bonds.map RawBond.toSemanticInteraction :=
    molecule.toSemanticMolecule?_interactions source.molecule semanticConverted
  simp only [AuthoritativeChemicalInput.DiagramBinaryTopologyConsistent, diagramConverted]
  intro bond member
  rw [molecule.toDiagramConfiguration_bonds] at member
  obtain ⟨raw, rawMember, materialized⟩ := List.mem_filterMap.mp member
  obtain ⟨sourceExact, targetExact⟩ := diagramBondOfRawBond?_endpoints materialized
  refine ⟨raw.toSemanticInteraction, ?_, ?_⟩
  · rw [interactionsConverted]
    exact List.mem_map.mpr ⟨raw, rawMember, rfl⟩
  · left
    have participantsExact :
        raw.toSemanticInteraction.participants = [raw.source, raw.target] := rfl
    simp only [participantsExact, sourceExact, targetExact]

/-- Successful parser ingestion yields diagram binary-topology consistency for the produced input.
No consistency premise is assumed: the conclusion is derived from the actual conversion and its
exact `filterMap` materialization. -/
theorem toAuthoritativeChemicalInput?_diagramTopologyConsistent
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toAuthoritativeChemicalInput? = some source) :
    source.DiagramBinaryTopologyConsistent :=
  molecule.diagramTopologyConsistent_of_structureAgreement source
    (molecule.authoritativeStructureAgreement_of_toAuthoritativeChemicalInput? source converted)

/-- The spatial-enriched ingestion preserves the same checked parser diagram, so it satisfies the
same diagram binary-topology consistency with no separate consistency premise. -/
theorem toAuthoritativeChemicalInputWithSpatial?_diagramTopologyConsistent
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toAuthoritativeChemicalInputWithSpatial? spatial = some source) :
    source.DiagramBinaryTopologyConsistent :=
  molecule.diagramTopologyConsistent_of_structureAgreement source
    (molecule.toAuthoritativeChemicalInputWithSpatial?_exact spatial source converted).1

end RawMolecule

end TetraStereo.OneCenter
