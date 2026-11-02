import Mathlib.Logic.Equiv.Basic
import TetraStereo.OneCenter.P93MolecularFullereneNumberedCageCompiler
import TetraStereo.OneCenter.P93MolecularFullereneTopologySourceAdapter
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open TetraStereo.OneCenter.BlueBookP93.Cyclic

noncomputable section

/-!
# Broad semantic encoding of a supplied numbered fullerene cage

`MolecularFullereneNumberedCagePackage` is the descriptor-free source topology boundary: it
supplies atom locants, one canonical undirected edge table, and the supplied oriented facial
cycles, with `MolecularFullereneNumberedCagePackage.Certificate` carrying the independent
molecular/topological proof.  This module does not recognize fullerenes and does not enumerate a
C60/C70 catalogue.  It constructs, from *any* such package together with

* broad per-atom `SemanticAtom` labels (all 1..118 `PeriodicElement`s, isotope, charge, unpaired
  electrons, aromatic input),
* arbitrary addend/appendage interactions over the same atom universe, and
* optional exact spatial data,

a `SemanticMolecule`, an `AuthoritativeChemicalInput`, and a
`CertifiedAuthoritativeChemicalInput`.  The supplied numbering and face orientations are retained
as representation data; no preferred numbering or handedness is selected or solved for.  Since the
broad input types carry neither face loops nor a numbering boundary, the module also constructs a
compact `FullereneSourceBundle` that retains those data as a sidecar and from which the numbered
package is recovered directly and exactly.

The module also isolates the exact broad-element seam: `RawMolecule` can only reach elements in
the parser vocabulary (`Element.toPeriodic?` rejects `.wildcard`), while the encoding labels accept
every `PeriodicElement`; in particular helium and any atom with nonzero `unpairedElectrons` have no
raw preimage.  Finally, atom-index relabelling by a permutation of the numbered cage carrier is
implemented as transport of the same encoding: undirected adjacency reflects exactly through a
canonical increasing-endpoint edge table, the atom map is injective on the carrier, face-edge
orientation is preserved, labels of atoms outside the carrier are unchanged, and spatial positions
are permuted by the inverse atom permutation.  The edge transport is structural: it preserves the
canonical table shape and exact undirected incidence, but it does not synthesize a reindexed
`RawMolecule`, so the source `Certificate` is not transported to the relabelled package.

Scope: this is representation coverage for the existing, supplied fullerene class.  It does not
claim that the five/six-cycle face carrier models every cage, nor that every organic molecule is a
fullerene.
-/

/-! ## Cage interaction encoding and exact decoder -/

/-- Semantic interaction representing one undirected numbered cage edge.  The orientation is the
canonical `edgeTable` orientation; only adjacency is asserted, never a Kekule bond order. -/
def cageInteraction (edge : ℕ × ℕ) : SemanticInteraction :=
  { participants := [edge.1, edge.2]
    kind := .unspecifiedCovalent }

@[simp] theorem cageInteraction_participants (edge : ℕ × ℕ) :
    (cageInteraction edge).participants = [edge.1, edge.2] := rfl

@[simp] theorem cageInteraction_kind (edge : ℕ × ℕ) :
    (cageInteraction edge).kind = .unspecifiedCovalent := rfl

/-- Decode one semantic interaction as a canonical cage edge.  Anything other than an unordered
two-participant `unspecifiedCovalent` interaction fails. -/
def cageEdgeOfInteraction? (interaction : SemanticInteraction) : Option (ℕ × ℕ) :=
  match interaction.participants with
  | [left, right] =>
      match interaction.kind with
      | .unspecifiedCovalent => some (left, right)
      | _ => none
  | _ => none

/-- Structural decoder for a list of cage interactions. -/
def cageEdges? : List SemanticInteraction → Option (List (ℕ × ℕ))
  | [] => some []
  | interaction :: rest =>
      match cageEdgeOfInteraction? interaction, cageEdges? rest with
      | some edge, some tail => some (edge :: tail)
      | _, _ => none

@[simp] theorem cageEdgeOfInteraction?_cageInteraction (edge : ℕ × ℕ) :
    cageEdgeOfInteraction? (cageInteraction edge) = some edge := by
  cases edge with
  | mk left right => rfl

@[simp] theorem cageEdges?_map_cageInteraction (edges : List (ℕ × ℕ)) :
    cageEdges? (edges.map cageInteraction) = some edges := by
  induction edges with
  | nil => rfl
  | cons edge rest inductionHypothesis =>
      simp [cageEdges?, inductionHypothesis]

/-- Underlying natural-number list of a list of bounded atom indices.  This explicit recursion keeps
the encoded participant list in constructor form, so its length, duplication, and bounds are
structural facts about the same list rather than properties of an intermediate `List.map`. -/
def boundedAtomListToNat {atomCount : ℕ} : List (Fin atomCount) → List ℕ
  | [] => []
  | atom :: rest => (atom : ℕ) :: boundedAtomListToNat rest

@[simp] theorem boundedAtomListToNat_length {atomCount : ℕ}
    (atoms : List (Fin atomCount)) :
    (boundedAtomListToNat atoms).length = atoms.length := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      simp [boundedAtomListToNat, inductionHypothesis]

theorem boundedAtomListToNat_mem {atomCount : ℕ} {atoms : List (Fin atomCount)}
    {atom : Fin atomCount} (present : (atom : ℕ) ∈ boundedAtomListToNat atoms) :
    atom ∈ atoms := by
  induction atoms with
  | nil => simp [boundedAtomListToNat] at present
  | cons head rest inductionHypothesis =>
      simp only [boundedAtomListToNat, List.mem_cons] at present ⊢
      rcases present with equal | tailPresent
      · exact Or.inl (Fin.ext equal)
      · exact Or.inr (inductionHypothesis tailPresent)

theorem boundedAtomListToNat_nodup {atomCount : ℕ} {atoms : List (Fin atomCount)}
    (nodup : atoms.Nodup) : (boundedAtomListToNat atoms).Nodup := by
  induction atoms with
  | nil => simp [boundedAtomListToNat]
  | cons atom rest inductionHypothesis =>
      simp only [boundedAtomListToNat, List.nodup_cons] at nodup ⊢
      exact ⟨fun present => nodup.1 (boundedAtomListToNat_mem present),
        inductionHypothesis nodup.2⟩

theorem boundedAtomListToNat_all_lt {atomCount : ℕ}
    (atoms : List (Fin atomCount)) :
    (boundedAtomListToNat atoms).all
      (fun atom => decide (atom < atomCount)) = true := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      simp [boundedAtomListToNat, inductionHypothesis]

/-- Semantic interaction representing one supplied addend/appendage interaction.  Participants are
`Fin atomCount` values, so index validity is enforced by construction rather than by a side
condition. -/
def addendInteraction {atomCount : ℕ}
    (interaction : List (Fin atomCount) × SemanticInteractionKind) : SemanticInteraction :=
  { participants := boundedAtomListToNat interaction.1
    kind := interaction.2 }

@[simp] theorem addendInteraction_participants {atomCount : ℕ}
    (interaction : List (Fin atomCount) × SemanticInteractionKind) :
    (addendInteraction interaction).participants =
      boundedAtomListToNat interaction.1 := rfl

@[simp] theorem addendInteraction_kind {atomCount : ℕ}
    (interaction : List (Fin atomCount) × SemanticInteractionKind) :
    (addendInteraction interaction).kind = interaction.2 := rfl

namespace SemanticMolecule

/-- Recover the canonical numbered cage edge table from a molecule whose interaction list is the
cage encoding.  Any interaction that is not an unordered `unspecifiedCovalent` pair makes the
decoding fail, so a successful decode is exact rather than approximate. -/
def cageEdges? (molecule : SemanticMolecule) : Option (List (ℕ × ℕ)) :=
  TetraStereo.OneCenter.cageEdges? molecule.interactions

end SemanticMolecule

/-! ## The source encoding -/

/-- Constructive broad representation of one supplied numbered fullerene cage together with
external (addend) atom labels and interactions.

The cage data are exactly the supplied `package`; the encoding adds no derived numbering, no
Kekule assignment, and no preferred face orientation.  All atom labels are arbitrary
`SemanticAtom`s, including elements outside the parser vocabulary.  `atomCount` is the finite atom
universe of the representation; every cage locant, edge endpoint, and face atom is required to lie
below it. -/
structure FullereneSourceEncoding where
  package : MolecularFullereneNumberedCagePackage
  atomCount : ℕ
  atomData : Fin atomCount → SemanticAtom
  addendInteractions : List (List (Fin atomCount) × SemanticInteractionKind) := []
  spatial? : Option SpatialConfiguration := none
  locantBound : ∀ atom ∈ package.atomsByLocant, atom < atomCount
  edgeBound : ∀ edge ∈ package.edgeTable, edge.1 < atomCount ∧ edge.2 < atomCount
  edgeDistinct : ∀ edge ∈ package.edgeTable, edge.1 ≠ edge.2
  edgeCarrier : ∀ edge ∈ package.edgeTable,
    edge.1 ∈ package.carrier ∧ edge.2 ∈ package.carrier
  faceCarrier : ∀ face ∈ package.faces, ∀ atom ∈ face, atom ∈ package.carrier
  faceNodup : ∀ face ∈ package.faces, face.Nodup
  addendArity : ∀ interaction ∈ addendInteractions, 2 ≤ interaction.1.length
  addendNodup : ∀ interaction ∈ addendInteractions, interaction.1.Nodup
  spatialLength : ∀ spatial, spatial? = some spatial → spatial.positions.length = atomCount

namespace FullereneSourceEncoding

/-- The configuration input is exactly the package's descriptor-free topology input: the supplied
carrier and the supplied oriented faces, with no additional structure. -/
def configurationInput (source : FullereneSourceEncoding) :
    MolecularFullereneConfigurationInput :=
  source.package.topologyInput

@[simp] theorem configurationInput_carrier (source : FullereneSourceEncoding) :
    source.configurationInput.carrier = source.package.carrier := rfl

@[simp] theorem configurationInput_faces (source : FullereneSourceEncoding) :
    source.configurationInput.faces = source.package.faces := rfl

@[simp] theorem configurationInput_exact (source : FullereneSourceEncoding) :
    source.configurationInput = source.package.topologyInput := rfl

/-- Every source locant is a carrier atom. -/
theorem locant_mem_carrier (source : FullereneSourceEncoding) {atom : ℕ}
    (member : atom ∈ source.package.atomsByLocant) : atom ∈ source.package.carrier :=
  List.mem_toFinset.mpr member

/-- Every carrier atom lies in the finite representation universe. -/
theorem carrierBound (source : FullereneSourceEncoding) {atom : ℕ}
    (member : atom ∈ source.package.carrier) : atom < source.atomCount := by
  rw [MolecularFullereneNumberedCagePackage.carrier, List.mem_toFinset] at member
  exact source.locantBound atom member

/-! ### Carrier permutation as a total atom map -/

/-- The existing carrier permutation map, viewed through this source's configuration input. -/
def cageMap (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (atom : ℕ) : ℕ :=
  mapMolecularFullereneCarrierAtom source.configurationInput symmetry atom

theorem cageMap_of_mem (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (atom : ℕ) (member : atom ∈ source.package.carrier) :
    source.cageMap symmetry atom = (symmetry ⟨atom, member⟩).1 := by
  have member' : atom ∈ source.configurationInput.carrier := member
  simpa [cageMap] using
    (mapMolecularFullereneCarrierAtom_of_mem source.configurationInput symmetry atom member')

theorem cageMap_of_not_mem (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (atom : ℕ) (notMem : atom ∉ source.package.carrier) :
    source.cageMap symmetry atom = atom := by
  unfold cageMap mapMolecularFullereneCarrierAtom
  exact dif_neg notMem

theorem cageMap_mem (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    {atom : ℕ} (member : atom ∈ source.package.carrier) :
    source.cageMap symmetry atom ∈ source.package.carrier := by
  rw [source.cageMap_of_mem symmetry atom member]
  exact (symmetry ⟨atom, member⟩).2

theorem cageMap_lt (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    {atom : ℕ} (member : atom ∈ source.package.carrier) :
    source.cageMap symmetry atom < source.atomCount :=
  source.carrierBound (source.cageMap_mem symmetry member)

/-- The total atom map is injective on the numbered carrier. -/
theorem cageMap_injective_on_carrier (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    {left right : ℕ} (leftCarrier : left ∈ source.package.carrier)
    (rightCarrier : right ∈ source.package.carrier)
    (mapped : source.cageMap symmetry left = source.cageMap symmetry right) : left = right := by
  have leftCarrier' : left ∈ source.configurationInput.carrier := leftCarrier
  have rightCarrier' : right ∈ source.configurationInput.carrier := rightCarrier
  exact mapMolecularFullereneCarrierAtom_injective_on_carrier source.configurationInput symmetry
    leftCarrier' rightCarrier' mapped

/-! ### The encoded molecule -/

/-- Semantic interactions of the numbered cage, in the supplied edge-table order. -/
def cageInteractions (source : FullereneSourceEncoding) : List SemanticInteraction :=
  source.package.edgeTable.map cageInteraction

/-- Semantic interactions of the supplied addends/appendages. -/
def addendInteractionsNat (source : FullereneSourceEncoding) : List SemanticInteraction :=
  source.addendInteractions.map addendInteraction

/-- Complete interaction list: cage interactions first, then addend interactions. -/
def interactionList (source : FullereneSourceEncoding) : List SemanticInteraction :=
  source.cageInteractions ++ source.addendInteractionsNat

/-- Broad semantic molecule: arbitrary per-atom `SemanticAtom` labels plus cage and addend
interactions. -/
def molecule (source : FullereneSourceEncoding) : SemanticMolecule :=
  { atoms := List.ofFn source.atomData
    interactions := source.interactionList }

/-- Cage-only semantic molecule, used to state the exact cage-incidence roundtrip. -/
def cageMolecule (source : FullereneSourceEncoding) : SemanticMolecule :=
  { atoms := List.ofFn source.atomData
    interactions := source.cageInteractions }

@[simp] theorem molecule_atoms (source : FullereneSourceEncoding) :
    source.molecule.atoms = List.ofFn source.atomData := rfl

@[simp] theorem molecule_interactions (source : FullereneSourceEncoding) :
    source.molecule.interactions = source.interactionList := rfl

@[simp] theorem molecule_interactionList (source : FullereneSourceEncoding) :
    source.interactionList = source.cageInteractions ++ source.addendInteractionsNat := rfl

@[simp] theorem cageMolecule_atoms (source : FullereneSourceEncoding) :
    source.cageMolecule.atoms = List.ofFn source.atomData := rfl

@[simp] theorem cageMolecule_interactions (source : FullereneSourceEncoding) :
    source.cageMolecule.interactions = source.cageInteractions := rfl

@[simp] theorem molecule_atomCount (source : FullereneSourceEncoding) :
    source.molecule.atomCount = source.atomCount := by
  simp [SemanticMolecule.atomCount]

@[simp] theorem cageMolecule_atomCount (source : FullereneSourceEncoding) :
    source.cageMolecule.atomCount = source.atomCount := by
  simp [SemanticMolecule.atomCount]

/-! ### Exact lookup of source atoms and cage edges -/

/-- Lookup in `List.ofFn` for the repository's local `listGet?`. -/
theorem listGet?_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (index : ℕ) :
    listGet? (List.ofFn f) index =
      if h : index < n then some (f ⟨index, h⟩) else none := by
  induction n generalizing index with
  | zero =>
      simp [List.ofFn_zero, listGet?]
  | succ n inductionHypothesis =>
      rw [List.ofFn_succ]
      cases index with
      | zero =>
          simp [listGet?]
      | succ index =>
          simp only [listGet?]
          rw [inductionHypothesis (fun i => f i.succ) index]
          by_cases h : index < n
          · rw [dif_pos h]
            have h' : index + 1 < n + 1 := Nat.succ_lt_succ h
            rw [dif_pos h']
            congr 1
          · rw [dif_neg h]
            have h' : ¬ index + 1 < n + 1 := fun c => h (Nat.succ_lt_succ_iff.mp c)
            rw [dif_neg h']

/-- Every represented atom position returns exactly its broad label. -/
theorem molecule_atomAt (source : FullereneSourceEncoding) (index : Fin source.atomCount) :
    listGet? source.molecule.atoms index = some (source.atomData index) := by
  simp [molecule, listGet?_ofFn, index.isLt]

/-- Source-locant roundtrip: reading a supplied locant returns the broad label attached to that
same atom index. -/
theorem molecule_atomAt_of_locant (source : FullereneSourceEncoding) {atom : ℕ}
    (member : atom ∈ source.package.atomsByLocant) :
    listGet? source.molecule.atoms atom =
      some (source.atomData ⟨atom, source.locantBound atom member⟩) :=
  source.molecule_atomAt ⟨atom, source.locantBound atom member⟩

/-- Exact decoder roundtrip: the encoded cage interaction list decodes to the supplied edge table. -/
@[simp] theorem cageMolecule_cageEdges? (source : FullereneSourceEncoding) :
    SemanticMolecule.cageEdges? source.cageMolecule = some source.package.edgeTable := by
  simp [SemanticMolecule.cageEdges?, cageMolecule, cageInteractions,
    cageEdges?_map_cageInteraction]

/-- Combined source roundtrip for atom positions, cage incidence, carrier, and oriented faces. -/
theorem source_roundtrip (source : FullereneSourceEncoding) :
    (∀ index : Fin source.atomCount,
      listGet? source.molecule.atoms index = some (source.atomData index)) ∧
    SemanticMolecule.cageEdges? source.cageMolecule = some source.package.edgeTable ∧
    source.configurationInput.carrier = source.package.carrier ∧
    source.configurationInput.faces = source.package.faces :=
  ⟨source.molecule_atomAt, source.cageMolecule_cageEdges?, rfl, rfl⟩

/-! ### Structural certification -/

theorem cageInteraction_wellFormed_iff (source : FullereneSourceEncoding) (edge : ℕ × ℕ) :
    (cageInteraction edge).WellFormed source.atomCount ↔
      edge.1 < source.atomCount ∧ edge.2 < source.atomCount ∧ edge.1 ≠ edge.2 := by
  simp [SemanticInteraction.WellFormed, cageInteraction, and_left_comm, and_comm]

theorem addendInteraction_wellFormed (source : FullereneSourceEncoding)
    (interaction : List (Fin source.atomCount) × SemanticInteractionKind)
    (present : interaction ∈ source.addendInteractions) :
    (addendInteraction interaction).WellFormed source.atomCount := by
  obtain ⟨participants, kind⟩ := interaction
  refine ⟨?_, ?_, ?_⟩
  · simpa [addendInteraction, boundedAtomListToNat_length] using
      source.addendArity (participants, kind) present
  · simpa [addendInteraction] using
      boundedAtomListToNat_nodup (source.addendNodup (participants, kind) present)
  · simpa [addendInteraction] using boundedAtomListToNat_all_lt participants

theorem cageMolecule_structurallyWellFormed (source : FullereneSourceEncoding) :
    source.cageMolecule.StructurallyWellFormed := by
  unfold SemanticMolecule.StructurallyWellFormed
  apply List.all_eq_true.mpr
  intro interaction present
  rw [SemanticInteraction.wellFormed?_eq_true_iff, source.cageMolecule_atomCount]
  simp only [cageMolecule_interactions, cageInteractions, List.mem_map] at present
  obtain ⟨edge, edgePresent, rfl⟩ := present
  exact (source.cageInteraction_wellFormed_iff edge).mpr
    ⟨(source.edgeBound edge edgePresent).1, (source.edgeBound edge edgePresent).2,
      source.edgeDistinct edge edgePresent⟩

theorem molecule_structurallyWellFormed (source : FullereneSourceEncoding) :
    source.molecule.StructurallyWellFormed := by
  unfold SemanticMolecule.StructurallyWellFormed
  apply List.all_eq_true.mpr
  intro interaction present
  rw [SemanticInteraction.wellFormed?_eq_true_iff, source.molecule_atomCount]
  simp only [molecule_interactions, molecule_interactionList, List.mem_append, cageInteractions,
    addendInteractionsNat, List.mem_map] at present
  rcases present with ⟨edge, edgePresent, rfl⟩ | ⟨addend, addendPresent, rfl⟩
  · exact (source.cageInteraction_wellFormed_iff edge).mpr
      ⟨(source.edgeBound edge edgePresent).1, (source.edgeBound edge edgePresent).2,
        source.edgeDistinct edge edgePresent⟩
  · exact source.addendInteraction_wellFormed addend addendPresent

/-- The authoritative input retains the exact molecule and the optional spatial evidence. -/
def toAuthoritativeChemicalInput (source : FullereneSourceEncoding) :
    AuthoritativeChemicalInput :=
  { molecule := source.molecule
    spatial? := source.spatial?
    diagram? := none }

theorem toAuthoritativeChemicalInput_spatialIndicesWellFormed
    (source : FullereneSourceEncoding) :
    source.toAuthoritativeChemicalInput.SpatialIndicesWellFormed := by
  unfold AuthoritativeChemicalInput.SpatialIndicesWellFormed
  cases observed : source.spatial? with
  | none => simp [toAuthoritativeChemicalInput, observed]
  | some spatial =>
      simp [toAuthoritativeChemicalInput, observed, source.molecule_atomCount,
        source.spatialLength spatial observed]

theorem toAuthoritativeChemicalInput_diagramIndicesWellFormed
    (source : FullereneSourceEncoding) :
    source.toAuthoritativeChemicalInput.DiagramIndicesWellFormed := by
  simp [AuthoritativeChemicalInput.DiagramIndicesWellFormed, toAuthoritativeChemicalInput]

theorem toAuthoritativeChemicalInput_structurallyWellFormed
    (source : FullereneSourceEncoding) :
    source.toAuthoritativeChemicalInput.StructurallyWellFormed :=
  ⟨source.molecule_structurallyWellFormed,
    source.toAuthoritativeChemicalInput_spatialIndicesWellFormed,
    source.toAuthoritativeChemicalInput_diagramIndicesWellFormed⟩

/-- Kernel-admitted broad input constructed from the supplied cage, broad labels, and addends. -/
def toCertifiedAuthoritativeChemicalInput (source : FullereneSourceEncoding) :
    CertifiedAuthoritativeChemicalInput :=
  { input := source.toAuthoritativeChemicalInput
    structurallyWellFormed := source.toAuthoritativeChemicalInput_structurallyWellFormed }

theorem toAuthoritativeChemicalInput_certify_isSome (source : FullereneSourceEncoding) :
    source.toAuthoritativeChemicalInput.certify?.isSome = true := by
  have checked : source.toAuthoritativeChemicalInput.structurallyWellFormed? = true :=
    (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff _).mpr
      source.toAuthoritativeChemicalInput_structurallyWellFormed
  simp [AuthoritativeChemicalInput.certify?, checked]

/-! ### Exact cage adjacency -/

/-- Cage adjacency in the encoded cage molecule is exactly membership in the supplied edge table
(up to undirected orientation). -/
theorem cageAdjacent_iff_edgeTable (source : FullereneSourceEncoding) (left right : ℕ) :
    source.cageMolecule.MolecularFullereneCageAdjacent left right ↔
      (left, right) ∈ source.package.edgeTable ∨
        (right, left) ∈ source.package.edgeTable := by
  simp only [SemanticMolecule.MolecularFullereneCageAdjacent, cageMolecule, cageInteractions,
    List.mem_map]
  constructor
  · rintro ⟨interaction, ⟨edge, edgePresent, rfl⟩, endpoints, _kind⟩
    simp only [cageInteraction] at endpoints
    rcases endpoints with forward | reverse
    · simp at forward
      obtain ⟨firstEq, secondEq⟩ := forward
      have pairEq : (left, right) = edge := by
        cases edge with
        | mk first second => exact Prod.ext firstEq.symm secondEq.symm
      exact Or.inl (pairEq ▸ edgePresent)
    · simp at reverse
      obtain ⟨firstEq, secondEq⟩ := reverse
      have pairEq : (right, left) = edge := by
        cases edge with
        | mk first second => exact Prod.ext firstEq.symm secondEq.symm
      exact Or.inr (pairEq ▸ edgePresent)
  · rintro (edgePresent | edgePresent)
    · refine ⟨cageInteraction (left, right), ?_, ?_, ?_⟩
      · exact ⟨(left, right), edgePresent, rfl⟩
      · simp [cageInteraction]
      · rfl
    · refine ⟨cageInteraction (right, left), ?_, ?_, ?_⟩
      · exact ⟨(right, left), edgePresent, rfl⟩
      · simp [cageInteraction]
      · rfl

/-- Reuse of the existing package certificate: the decoded encoded cage is exactly the certified
induced positive-bond set of the source raw molecule on its carrier. -/
theorem cageEdges?_toFinset_eq_certified (source : FullereneSourceEncoding)
    (core : RawMolecule) (certificate : source.package.Certificate core) :
    (SemanticMolecule.cageEdges? source.cageMolecule).map (fun edges => edges.toFinset) =
      some (molecularFullereneCageEdges core source.package.carrier) := by
  rw [source.cageMolecule_cageEdges?]
  obtain ⟨_, _, _, edgeExact⟩ :=
    MolecularFullereneNumberedCagePackage.Certificate.tableJudgment core source.package certificate
  change some (source.package.edgeTable.toFinset) =
    some (molecularFullereneCageEdges core source.package.carrier)
  rw [edgeExact]

end FullereneSourceEncoding

/-! ## Full encoded bundle and direct recovery of the numbered cage

`AuthoritativeChemicalInput` carries atoms, interactions, spatial data, and diagrams, but no face
loops and no numbering boundary.  The following compact bundle retains those numbered-cage data as
a sidecar next to the broad input, so that the complete encoded object remains self-contained and
the numbered cage can be recovered from the bundle alone.  Nothing is fetched from the original
`FullereneSourceEncoding` during recovery. -/

/-- Compact self-contained encoded bundle: the broad authoritative input together with the
numbered-cage sidecar.  The sidecar consists of the cage-only semantic molecule (whose decoder
returns the canonical edge table), the supplied locant numbering boundary, and the supplied oriented
face loops.  No preferred numbering, face orientation, or Kekule order is selected. -/
structure FullereneSourceBundle where
  input : AuthoritativeChemicalInput
  cage : SemanticMolecule
  atomCount : ℕ
  locants : List ℕ
  faces : List (List ℕ)
  locantBound : ∀ atom ∈ locants, atom < atomCount
  faceCarrier : ∀ face ∈ faces, ∀ atom ∈ face, atom ∈ locants.toFinset
  faceNodup : ∀ face ∈ faces, face.Nodup

namespace FullereneSourceBundle

/-- Decode the supplied numbered cage from the bundle alone.  The edge table is read from the
bundle's cage-only molecule; the locant list and oriented face loops are the bundle sidecar. -/
def recoverPackage? (bundle : FullereneSourceBundle) :
    Option MolecularFullereneNumberedCagePackage :=
  Option.map
    (fun edges =>
      { atomsByLocant := bundle.locants
        edgeTable := edges
        faces := bundle.faces })
    (SemanticMolecule.cageEdges? bundle.cage)

/-- Decode the descriptor-free topology input from the bundle alone. -/
def recoverConfigurationInput? (bundle : FullereneSourceBundle) :
    Option MolecularFullereneConfigurationInput :=
  Option.map MolecularFullereneNumberedCagePackage.topologyInput bundle.recoverPackage?

/-- Any package returned by bundle recovery has exactly the bundle's locants and faces, and its edge
table is exactly the decoder image of the bundle's cage molecule.  The proof inspects only bundle
fields and the bundle's own decoder. -/
theorem recoverPackage?_exact (bundle : FullereneSourceBundle)
    {package : MolecularFullereneNumberedCagePackage}
    (recovered : bundle.recoverPackage? = some package) :
    package.atomsByLocant = bundle.locants ∧
      SemanticMolecule.cageEdges? bundle.cage = some package.edgeTable ∧
      package.faces = bundle.faces := by
  unfold recoverPackage? at recovered
  cases observed : SemanticMolecule.cageEdges? bundle.cage with
  | none => simp [observed] at recovered
  | some edges =>
      simp only [observed, Option.map_some, Option.some.injEq] at recovered
      subst package
      exact ⟨rfl, rfl, rfl⟩

/-- Recovered carriers are exactly the finsets of the bundle's locant boundary. -/
theorem recoverPackage?_carrier (bundle : FullereneSourceBundle)
    {package : MolecularFullereneNumberedCagePackage}
    (recovered : bundle.recoverPackage? = some package) :
    package.carrier = bundle.locants.toFinset := by
  obtain ⟨locantsEq, _, _⟩ := bundle.recoverPackage?_exact recovered
  unfold MolecularFullereneNumberedCagePackage.carrier
  rw [locantsEq]

/-- Recovered face loops are exactly the bundle's face sidecar. -/
theorem recoverPackage?_faces (bundle : FullereneSourceBundle)
    {package : MolecularFullereneNumberedCagePackage}
    (recovered : bundle.recoverPackage? = some package) :
    package.faces = bundle.faces :=
  (bundle.recoverPackage?_exact recovered).2.2

/-- Recovered edge tables are exactly the decoded bundle cage molecule. -/
theorem recoverPackage?_edgeTable (bundle : FullereneSourceBundle)
    {package : MolecularFullereneNumberedCagePackage}
    (recovered : bundle.recoverPackage? = some package) :
    SemanticMolecule.cageEdges? bundle.cage = some package.edgeTable :=
  (bundle.recoverPackage?_exact recovered).2.1

end FullereneSourceBundle

namespace FullereneSourceEncoding

/-- The full encoded bundle.  The sidecar is built from the same supplied representation data as the
encoding; recovery reads only the resulting bundle. -/
def toBundle (source : FullereneSourceEncoding) : FullereneSourceBundle where
  input := source.toAuthoritativeChemicalInput
  cage := source.cageMolecule
  atomCount := source.atomCount
  locants := source.package.atomsByLocant
  faces := source.package.faces
  locantBound := source.locantBound
  faceCarrier := source.faceCarrier
  faceNodup := source.faceNodup

@[simp] theorem toBundle_input (source : FullereneSourceEncoding) :
    source.toBundle.input = source.toAuthoritativeChemicalInput := rfl

@[simp] theorem toBundle_cage (source : FullereneSourceEncoding) :
    source.toBundle.cage = source.cageMolecule := rfl

@[simp] theorem toBundle_atomCount (source : FullereneSourceEncoding) :
    source.toBundle.atomCount = source.atomCount := rfl

@[simp] theorem toBundle_locants (source : FullereneSourceEncoding) :
    source.toBundle.locants = source.package.atomsByLocant := rfl

@[simp] theorem toBundle_faces (source : FullereneSourceEncoding) :
    source.toBundle.faces = source.package.faces := rfl

/-- Direct exact recovery from the bundle: decoding the bundle's cage molecule together with its
locant and face sidecar returns the supplied numbered package. -/
theorem toBundle_recoverPackage? (source : FullereneSourceEncoding) :
    source.toBundle.recoverPackage? = some source.package := by
  simp [toBundle, FullereneSourceBundle.recoverPackage?]

/-- Direct exact recovery of the descriptor-free topology input from the bundle. -/
theorem toBundle_recoverConfigurationInput? (source : FullereneSourceEncoding) :
    source.toBundle.recoverConfigurationInput? = some source.configurationInput := by
  simp [FullereneSourceBundle.recoverConfigurationInput?, toBundle_recoverPackage?,
    configurationInput]

/-- Recovery from the bundle returns exactly the supplied numbered package, with the recovered
carrier and faces read from the bundle's own sidecar fields and the recovered edge table read from
the bundle's own cage molecule. -/
theorem toBundle_recovery_exact (source : FullereneSourceEncoding) :
    ∃ recovered, source.toBundle.recoverPackage? = some recovered ∧
      recovered.carrier = source.toBundle.locants.toFinset ∧
      recovered.faces = source.toBundle.faces ∧
      SemanticMolecule.cageEdges? source.toBundle.cage = some recovered.edgeTable := by
  refine ⟨source.package, source.toBundle_recoverPackage?, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact source.cageMolecule_cageEdges?

/-! ### Atom-index relabelling transport of the numbered cage -/

/-- One relabelled cage edge with the endpoint images kept in their supplied order.  This raw
orientation is not again required to be increasing; `relabelEdgeCanonical` is the
orientation-normalized transport used by the package. -/
def relabelEdge (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (edge : ℕ × ℕ) : ℕ × ℕ :=
  (source.cageMap symmetry edge.1, source.cageMap symmetry edge.2)

/-- Canonical orientation of one relabelled edge: the same unordered endpoint pair, stored with the
smaller atom index first.  A permutation of atom indices need not preserve an increasing-endpoint
convention, so package transport normalizes the orientation explicitly. -/
def relabelEdgeCanonical (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (edge : ℕ × ℕ) : ℕ × ℕ :=
  if source.cageMap symmetry edge.1 ≤ source.cageMap symmetry edge.2 then
    (source.cageMap symmetry edge.1, source.cageMap symmetry edge.2)
  else
    (source.cageMap symmetry edge.2, source.cageMap symmetry edge.1)

/-- Relabelling the fixed supplied numbering: locants, canonical edge endpoints, and every oriented
face traversal are transported by the same carrier permutation.  The face list is not reoriented or
re-indexed in any other way. -/
def relabelPackage (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput)) :
    MolecularFullereneNumberedCagePackage where
  atomsByLocant := source.package.atomsByLocant.map (source.cageMap symmetry)
  edgeTable := source.package.edgeTable.map (source.relabelEdgeCanonical symmetry)
  faces := source.package.faces.map
    (mapMolecularFullereneFace source.configurationInput symmetry)

@[simp] theorem relabelPackage_atomsByLocant (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput)) :
    (source.relabelPackage symmetry).atomsByLocant =
      source.package.atomsByLocant.map (source.cageMap symmetry) := rfl

@[simp] theorem relabelPackage_edgeTable (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput)) :
    (source.relabelPackage symmetry).edgeTable =
      source.package.edgeTable.map (source.relabelEdgeCanonical symmetry) := rfl

@[simp] theorem relabelPackage_faces (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput)) :
    (source.relabelPackage symmetry).faces =
      source.package.faces.map
        (mapMolecularFullereneFace source.configurationInput symmetry) := rfl

theorem relabelPackage_edgeTable_mem (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    {edge : ℕ × ℕ} :
    edge ∈ (source.relabelPackage symmetry).edgeTable ↔
      ∃ original ∈ source.package.edgeTable,
        source.relabelEdgeCanonical symmetry original = edge := by
  simp [relabelPackage, List.mem_map]

theorem relabelPackage_faces_mem (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    {face : List ℕ} :
    face ∈ (source.relabelPackage symmetry).faces ↔
      ∃ original ∈ source.package.faces,
        mapMolecularFullereneFace source.configurationInput symmetry original = face := by
  simp [relabelPackage, List.mem_map]

/-- The image of a carrier atom under relabelling remains a carrier atom of the relabelled
package. -/
theorem cageMap_mem_relabelCarrier (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    {atom : ℕ} (member : atom ∈ source.package.carrier) :
    source.cageMap symmetry atom ∈ (source.relabelPackage symmetry).carrier := by
  simp only [relabelPackage, MolecularFullereneNumberedCagePackage.carrier, List.mem_toFinset,
    List.mem_map]
  rw [MolecularFullereneNumberedCagePackage.carrier, List.mem_toFinset] at member
  exact ⟨atom, member, rfl⟩

/-- The canonical relabelled edge is ordered by construction. -/
theorem relabelEdgeCanonical_ordered (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (edge : ℕ × ℕ) :
    (source.relabelEdgeCanonical symmetry edge).1 ≤
      (source.relabelEdgeCanonical symmetry edge).2 := by
  unfold relabelEdgeCanonical
  split
  · assumption
  · exact Nat.le_of_not_le ‹¬ _ ≤ _›

/-- The canonical relabelled edge has the same endpoints, hence the same bounds, as the raw
relabelled edge. -/
theorem relabelEdgeCanonical_bound (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    {edge : ℕ × ℕ} (edgePresent : edge ∈ source.package.edgeTable) :
    (source.relabelEdgeCanonical symmetry edge).1 < source.atomCount ∧
      (source.relabelEdgeCanonical symmetry edge).2 < source.atomCount := by
  have firstBound := source.cageMap_lt symmetry (source.edgeCarrier edge edgePresent).1
  have secondBound := source.cageMap_lt symmetry (source.edgeCarrier edge edgePresent).2
  unfold relabelEdgeCanonical
  split
  · exact ⟨firstBound, secondBound⟩
  · exact ⟨secondBound, firstBound⟩

/-- Canonicalization preserves endpoint distinctness. -/
theorem relabelEdgeCanonical_distinct (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    {edge : ℕ × ℕ} (edgePresent : edge ∈ source.package.edgeTable) :
    (source.relabelEdgeCanonical symmetry edge).1 ≠
      (source.relabelEdgeCanonical symmetry edge).2 := by
  have firstCarrier := (source.edgeCarrier edge edgePresent).1
  have secondCarrier := (source.edgeCarrier edge edgePresent).2
  have mappedDistinct : source.cageMap symmetry edge.1 ≠ source.cageMap symmetry edge.2 :=
    fun equal => source.edgeDistinct edge edgePresent
      (source.cageMap_injective_on_carrier symmetry firstCarrier secondCarrier equal)
  unfold relabelEdgeCanonical
  split
  · exact mappedDistinct
  · exact fun equal => mappedDistinct equal.symm

/-- Canonical relabelled edges lie in the relabelled carrier. -/
theorem relabelEdgeCanonical_mem_relabelCarrier (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    {edge : ℕ × ℕ} (edgePresent : edge ∈ source.package.edgeTable) :
    (source.relabelEdgeCanonical symmetry edge).1 ∈
        (source.relabelPackage symmetry).carrier ∧
      (source.relabelEdgeCanonical symmetry edge).2 ∈
        (source.relabelPackage symmetry).carrier := by
  have firstCarrier := (source.edgeCarrier edge edgePresent).1
  have secondCarrier := (source.edgeCarrier edge edgePresent).2
  unfold relabelEdgeCanonical
  split
  · exact
      ⟨source.cageMap_mem_relabelCarrier symmetry firstCarrier,
        source.cageMap_mem_relabelCarrier symmetry secondCarrier⟩
  · exact
      ⟨source.cageMap_mem_relabelCarrier symmetry secondCarrier,
        source.cageMap_mem_relabelCarrier symmetry firstCarrier⟩

/-- The relabelled edge table is a canonical (increasing-endpoint) table whenever the source table
has the same endpoints in its carrier. -/
theorem relabelPackage_edgeTable_ordered (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    {edge : ℕ × ℕ} (edgeMember : edge ∈ (source.relabelPackage symmetry).edgeTable) :
    edge.1 ≤ edge.2 := by
  rw [relabelPackage_edgeTable_mem] at edgeMember
  obtain ⟨original, _, rfl⟩ := edgeMember
  exact source.relabelEdgeCanonical_ordered symmetry original

/-- The canonical relabelled edge is either the raw relabelled edge or its swap.  This is the only
loss introduced by normalization: undirected incidence is unchanged, while the raw orientation is
recoverable only up to swap. -/
theorem relabelEdgeCanonical_eq_raw_or_swap (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (edge : ℕ × ℕ) :
    source.relabelEdgeCanonical symmetry edge = source.relabelEdge symmetry edge ∨
      source.relabelEdgeCanonical symmetry edge =
        (source.relabelEdge symmetry edge).swap := by
  unfold relabelEdgeCanonical relabelEdge
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Unordered incidence of a single edge is exactly preserved by canonicalization. -/
theorem relabelEdgeCanonical_unordered_iff (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (edge : ℕ × ℕ) (left right : ℕ) :
    (source.relabelEdgeCanonical symmetry edge = (left, right) ∨
        source.relabelEdgeCanonical symmetry edge = (right, left)) ↔
      (source.relabelEdge symmetry edge = (left, right) ∨
        source.relabelEdge symmetry edge = (right, left)) := by
  unfold relabelEdgeCanonical relabelEdge
  split
  · rfl
  · simp only [Prod.mk.injEq]
    constructor
    · rintro (⟨firstEq, secondEq⟩ | ⟨firstEq, secondEq⟩)
      · exact Or.inr ⟨secondEq, firstEq⟩
      · exact Or.inl ⟨secondEq, firstEq⟩
    · rintro (⟨firstEq, secondEq⟩ | ⟨firstEq, secondEq⟩)
      · exact Or.inr ⟨secondEq, firstEq⟩
      · exact Or.inl ⟨secondEq, firstEq⟩

/-- A canonical relabelled edge whose endpoints are the images of `left` and `right` can only come
from a source edge incident with `left` and `right`.  Injectivity of the carrier permutation makes
the source orientation exact. -/
theorem relabelEdgeCanonical_image_mem_source (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    {edge : ℕ × ℕ} (edgePresent : edge ∈ source.package.edgeTable)
    {left right : ℕ} (leftCarrier : left ∈ source.package.carrier)
    (rightCarrier : right ∈ source.package.carrier)
    (image : source.relabelEdgeCanonical symmetry edge =
      (source.cageMap symmetry left, source.cageMap symmetry right)) :
    (left, right) ∈ source.package.edgeTable ∨
      (right, left) ∈ source.package.edgeTable := by
  have firstCarrier := (source.edgeCarrier edge edgePresent).1
  have secondCarrier := (source.edgeCarrier edge edgePresent).2
  unfold relabelEdgeCanonical at image
  by_cases order :
      source.cageMap symmetry edge.1 ≤ source.cageMap symmetry edge.2
  · rw [if_pos order] at image
    simp only [Prod.mk.injEq] at image
    obtain ⟨firstEq, secondEq⟩ := image
    have firstIs : edge.1 = left :=
      source.cageMap_injective_on_carrier symmetry firstCarrier leftCarrier firstEq
    have secondIs : edge.2 = right :=
      source.cageMap_injective_on_carrier symmetry secondCarrier rightCarrier secondEq
    have pairEq : edge = (left, right) := Prod.ext firstIs secondIs
    exact Or.inl (by rwa [pairEq] at edgePresent)
  · rw [if_neg order] at image
    simp only [Prod.mk.injEq] at image
    obtain ⟨secondEq, firstEq⟩ := image
    have firstIs : edge.1 = right :=
      source.cageMap_injective_on_carrier symmetry firstCarrier rightCarrier firstEq
    have secondIs : edge.2 = left :=
      source.cageMap_injective_on_carrier symmetry secondCarrier leftCarrier secondEq
    have pairEq : edge = (right, left) := Prod.ext firstIs secondIs
    exact Or.inr (by rwa [pairEq] at edgePresent)

/-- Exact undirected edge-incidence reflection for the canonical relabelled package. -/
theorem mem_relabelledEdgeTable_unordered_iff (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    {left right : ℕ} (leftCarrier : left ∈ source.package.carrier)
    (rightCarrier : right ∈ source.package.carrier) :
    ((source.cageMap symmetry left, source.cageMap symmetry right) ∈
          (source.relabelPackage symmetry).edgeTable ∨
        (source.cageMap symmetry right, source.cageMap symmetry left) ∈
          (source.relabelPackage symmetry).edgeTable) ↔
      ((left, right) ∈ source.package.edgeTable ∨
        (right, left) ∈ source.package.edgeTable) := by
  simp only [relabelPackage_edgeTable, List.mem_map]
  constructor
  · rintro (⟨edge, edgePresent, image⟩ | ⟨edge, edgePresent, image⟩)
    · exact source.relabelEdgeCanonical_image_mem_source symmetry edgePresent
        leftCarrier rightCarrier image
    · have swapped := source.relabelEdgeCanonical_image_mem_source symmetry edgePresent
        rightCarrier leftCarrier image
      rcases swapped with present | present
      · exact Or.inr present
      · exact Or.inl present
  · rintro (present | present)
    · by_cases order :
          source.cageMap symmetry left ≤ source.cageMap symmetry right
      · exact Or.inl ⟨(left, right), present, by
          unfold relabelEdgeCanonical
          rw [if_pos order]⟩
      · exact Or.inr ⟨(left, right), present, by
          unfold relabelEdgeCanonical
          rw [if_neg order]⟩
    · by_cases order :
          source.cageMap symmetry right ≤ source.cageMap symmetry left
      · exact Or.inr ⟨(right, left), present, by
          unfold relabelEdgeCanonical
          rw [if_pos order]⟩
      · exact Or.inl ⟨(right, left), present, by
          unfold relabelEdgeCanonical
          rw [if_neg order]⟩

/-- Full atom-index equivalence from the numbered carrier into the finite representation universe,
acting only on carrier indices. -/
def carrierFinEquiv (source : FullereneSourceEncoding) :
    MolecularFullereneCarrierAtom source.configurationInput ≃
      { index : Fin source.atomCount // (index : ℕ) ∈ source.package.carrier } where
  toFun atom := ⟨⟨atom.1, source.carrierBound atom.2⟩, atom.2⟩
  invFun index := ⟨index.1.1, index.2⟩
  left_inv atom := by
    apply Subtype.ext
    rfl
  right_inv index := by
    apply Subtype.ext
    apply Fin.ext
    rfl

/-- The induced permutation of all atom indices: the carrier permutation on carrier atoms and the
identity everywhere else.  This is Mathlib's `Equiv.Perm.extendDomain` applied along
`carrierFinEquiv`, so no inverse law is reproved here. -/
def relabelFinEquiv (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput)) :
    Equiv.Perm (Fin source.atomCount) :=
  symmetry.extendDomain source.carrierFinEquiv

/-- On carrier indices the induced permutation is exactly the carrier permutation, transported
back to `Fin atomCount`. -/
theorem relabelFinEquiv_apply_mem (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (index : Fin source.atomCount)
    (member : (index : ℕ) ∈ source.package.carrier) :
    source.relabelFinEquiv symmetry index =
      (source.carrierFinEquiv
        (symmetry (source.carrierFinEquiv.symm ⟨index, member⟩)) : Fin source.atomCount) := by
  change symmetry.extendDomain source.carrierFinEquiv index = _
  exact Equiv.Perm.extendDomain_apply_subtype (e := symmetry)
    (f := source.carrierFinEquiv) (b := index) member

/-- Outside the carrier the induced permutation fixes every atom index. -/
theorem relabelFinEquiv_apply_not_mem (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (index : Fin source.atomCount)
    (notMem : (index : ℕ) ∉ source.package.carrier) :
    source.relabelFinEquiv symmetry index = index := by
  change symmetry.extendDomain source.carrierFinEquiv index = index
  exact Equiv.Perm.extendDomain_apply_not_subtype (e := symmetry)
    (f := source.carrierFinEquiv) (b := index) notMem

/-- The inverse induced permutation also fixes every index outside the carrier. -/
theorem relabelFinEquiv_symm_apply_not_mem (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (index : Fin source.atomCount)
    (notMem : (index : ℕ) ∉ source.package.carrier) :
    (source.relabelFinEquiv symmetry).symm index = index := by
  change (symmetry.extendDomain source.carrierFinEquiv).symm index = index
  rw [Equiv.Perm.extendDomain_symm]
  exact Equiv.Perm.extendDomain_apply_not_subtype (e := symmetry.symm)
    (f := source.carrierFinEquiv) (b := index) notMem

/-- Reference coordinate used only when a source position list is shorter than the atom universe.
A valid source encoding never takes this branch: `spatialLength` supplies a position for every atom,
and `relabelPositions_getElem?` shows the transported lookup agrees with the source at every index
that exists in the source list. -/
def originPoint3 : CartesianPoint3 := ⟨0, 0, 0⟩

/-- Spatial positions transported by the inverse induced atom permutation.  `SpatialConfiguration`
addresses positions by atom index, so relabelling atoms must permute the position list.  The new
position at index `j` is the old position at `(relabelFinEquiv symmetry).symm j`; positions outside
the carrier are therefore not moved.  The list is total, so the definition itself needs no length
hypothesis; the source `spatialLength` obligation is used only to prove that every transported
lookup is an actual source lookup. -/
def relabelPositions (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (positions : List CartesianPoint3) : List CartesianPoint3 :=
  List.ofFn fun index : Fin source.atomCount =>
    (positions[(((source.relabelFinEquiv symmetry).symm index : Fin source.atomCount) : ℕ)]?).getD
      originPoint3

/-- Spatial configuration transported by the inverse induced atom permutation. -/
def relabelSpatial (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (spatial : SpatialConfiguration) : SpatialConfiguration where
  positions := source.relabelPositions symmetry spatial.positions

@[simp] theorem relabelPositions_length (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (positions : List CartesianPoint3) :
    (source.relabelPositions symmetry positions).length = source.atomCount := by
  simp [relabelPositions]

/-- The defining value equation for transported positions: the new position at the image of an atom
is exactly that atom's old position.  The source length obligation makes the two lookups land in
range, so the fallback branch of `getD` is never used. -/
theorem relabelPositions_getElem? (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (positions : List CartesianPoint3)
    (length : positions.length = source.atomCount)
    (index : Fin source.atomCount) :
    (source.relabelPositions symmetry positions)[
        (((source.relabelFinEquiv symmetry index : Fin source.atomCount) : ℕ))]? =
      positions[(index : ℕ)]? := by
  rw [relabelPositions, List.getElem?_ofFn]
  rw [dif_pos (source.relabelFinEquiv symmetry index).isLt]
  have firstBound :
      ((((source.relabelFinEquiv symmetry).symm
        ((source.relabelFinEquiv symmetry) index) : Fin source.atomCount) : ℕ)) <
        positions.length := by
    rw [length]
    exact ((source.relabelFinEquiv symmetry).symm
      ((source.relabelFinEquiv symmetry) index)).isLt
  rw [getElem?_pos positions _ firstBound]
  rw [getElem?_pos positions ((index : ℕ)) (by rw [length]; exact index.isLt)]
  simp only [Option.getD_some]
  congr 1
  congr 1
  simp [Equiv.symm_apply_apply]

/-- The new position at the image of an atom is the old position at that atom, stated for the
transported spatial configuration. -/
theorem relabelSpatial_positions_getElem? (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (spatial : SpatialConfiguration)
    (length : spatial.positions.length = source.atomCount)
    (index : Fin source.atomCount) :
    (source.relabelSpatial symmetry spatial).positions[
        (((source.relabelFinEquiv symmetry index : Fin source.atomCount) : ℕ))]? =
      spatial.positions[(index : ℕ)]? :=
  source.relabelPositions_getElem? symmetry spatial.positions length index

/-- The relabelled source encoding.  Cage numbering, canonical edge table, faces, broad atom labels,
addend interactions, and optional spatial positions are all transported by the same carrier
permutation; positions use the inverse index permutation so that the value at an atom's image is
that atom's original coordinate. -/
def relabel (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput)) :
    FullereneSourceEncoding where
  package := source.relabelPackage symmetry
  atomCount := source.atomCount
  atomData := fun index => source.atomData ((source.relabelFinEquiv symmetry).symm index)
  addendInteractions := source.addendInteractions.map (fun interaction =>
    (interaction.1.map (source.relabelFinEquiv symmetry), interaction.2))
  spatial? := source.spatial?.map (source.relabelSpatial symmetry)
  locantBound := by
    intro atom member
    simp only [relabelPackage, List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    exact source.cageMap_lt symmetry (source.locant_mem_carrier originalMember)
  edgeBound := by
    intro edge member
    simp only [relabelPackage, List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    exact source.relabelEdgeCanonical_bound symmetry originalMember
  edgeDistinct := by
    intro edge member
    simp only [relabelPackage, List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    exact source.relabelEdgeCanonical_distinct symmetry originalMember
  edgeCarrier := by
    intro edge member
    simp only [relabelPackage, List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    exact source.relabelEdgeCanonical_mem_relabelCarrier symmetry originalMember
  faceCarrier := by
    intro face faceMember atom atomMember
    simp only [relabelPackage, List.mem_map] at faceMember
    obtain ⟨originalFace, originalFaceMember, rfl⟩ := faceMember
    simp only [mapMolecularFullereneFace, List.mem_map] at atomMember
    obtain ⟨originalAtom, originalAtomMember, rfl⟩ := atomMember
    exact source.cageMap_mem_relabelCarrier symmetry
      (source.faceCarrier originalFace originalFaceMember originalAtom originalAtomMember)
  faceNodup := by
    intro face faceMember
    simp only [relabelPackage, List.mem_map] at faceMember
    obtain ⟨originalFace, originalFaceMember, rfl⟩ := faceMember
    exact (source.faceNodup originalFace originalFaceMember).map_on
      (fun first firstMember second secondMember equal =>
        source.cageMap_injective_on_carrier symmetry
          (source.faceCarrier originalFace originalFaceMember first firstMember)
          (source.faceCarrier originalFace originalFaceMember second secondMember) equal)
  addendArity := by
    intro interaction member
    simp only [List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    simpa using source.addendArity original originalMember
  addendNodup := by
    intro interaction member
    simp only [List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    exact (source.addendNodup original originalMember).map (by
      intro left right equal
      exact (source.relabelFinEquiv symmetry).injective equal)
  spatialLength := by
    intro spatial observed
    obtain ⟨original, _, rfl⟩ := Option.map_eq_some_iff.mp observed
    simp [relabelSpatial]

@[simp] theorem relabel_package (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput)) :
    (source.relabel symmetry).package = source.relabelPackage symmetry := rfl

/-- Spatial transport preserves the `none` absence of geometry. -/
theorem relabel_spatial?_eq_none (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (absent : source.spatial? = none) :
    (source.relabel symmetry).spatial? = none := by
  simp [relabel, absent]

/-- Spatial transport sends a present configuration to the transported configuration, with the
index permutation applied to positions. -/
theorem relabel_spatial?_eq_some (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (spatial : SpatialConfiguration)
    (present : source.spatial? = some spatial) :
    (source.relabel symmetry).spatial? =
      some (source.relabelSpatial symmetry spatial) := by
  simp [relabel, present]

/-- Cage adjacency reflects exactly under atom-index relabelling. -/
theorem relabel_cageAdjacent_iff (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (left right : ℕ) (leftCarrier : left ∈ source.package.carrier)
    (rightCarrier : right ∈ source.package.carrier) :
    (source.relabel symmetry).cageMolecule.MolecularFullereneCageAdjacent
        (source.cageMap symmetry left) (source.cageMap symmetry right) ↔
      source.cageMolecule.MolecularFullereneCageAdjacent left right := by
  rw [(source.relabel symmetry).cageAdjacent_iff_edgeTable,
    source.cageAdjacent_iff_edgeTable]
  change ((source.cageMap symmetry left, source.cageMap symmetry right) ∈
          (source.relabelPackage symmetry).edgeTable ∨
        (source.cageMap symmetry right, source.cageMap symmetry left) ∈
          (source.relabelPackage symmetry).edgeTable) ↔
      ((left, right) ∈ source.package.edgeTable ∨
        (right, left) ∈ source.package.edgeTable)
  exact source.mem_relabelledEdgeTable_unordered_iff symmetry leftCarrier rightCarrier

/-- Supplied face-edge orientations are preserved by relabelling. -/
theorem isForwardNamedCycleEdge_relabel (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (face : List ℕ) (faceMember : face ∈ source.package.faces) {left right : ℕ}
    (edge : IsForwardNamedCycleEdge face left right) :
    IsForwardNamedCycleEdge
      (mapMolecularFullereneFace source.configurationInput symmetry face)
      (source.cageMap symmetry left) (source.cageMap symmetry right) :=
  isForwardNamedCycleEdge_mapMolecularFullereneFace source.configurationInput symmetry face
    (source.faceCarrier face faceMember) (source.faceNodup face faceMember) edge

/-- Labels of atoms outside the numbered carrier are unchanged by relabelling. -/
theorem relabel_atomData_of_not_mem (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (index : Fin source.atomCount)
    (notMem : (index : ℕ) ∉ source.package.carrier) :
    (source.relabel symmetry).atomData index = source.atomData index := by
  have fixed : (source.relabelFinEquiv symmetry).symm index = index :=
    source.relabelFinEquiv_symm_apply_not_mem symmetry index notMem
  simp [relabel, fixed]

/-- The image position of an atom carries exactly that atom's original broad label. -/
theorem relabel_atomData_cage (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput))
    (index : Fin source.atomCount)
    (member : (index : ℕ) ∈ source.package.carrier) :
    (source.relabel symmetry).atomData
        (source.carrierFinEquiv
          (symmetry (source.carrierFinEquiv.symm ⟨index, member⟩))).1 =
      source.atomData index := by
  have fixed : (source.relabelFinEquiv symmetry).symm
      (source.carrierFinEquiv
        (symmetry (source.carrierFinEquiv.symm ⟨index, member⟩))).1 = index := by
    rw [← source.relabelFinEquiv_apply_mem symmetry index member]
    exact Equiv.symm_apply_apply _ _
  unfold relabel
  exact congrArg source.atomData fixed

/-- The relabelled encoding is structurally valid whenever the source is. -/
theorem relabel_molecule_structurallyWellFormed (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput)) :
    (source.relabel symmetry).molecule.StructurallyWellFormed :=
  (source.relabel symmetry).molecule_structurallyWellFormed

/-- The relabelled encoding yields a kernel-admitted authoritative input. -/
theorem relabel_toAuthoritativeChemicalInput_structurallyWellFormed
    (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput)) :
    (source.relabel symmetry).toAuthoritativeChemicalInput.StructurallyWellFormed :=
  (source.relabel symmetry).toAuthoritativeChemicalInput_structurallyWellFormed

/-- The relabelled edge decoder still returns exactly the relabelled supplied edge table. -/
theorem relabel_cageEdges? (source : FullereneSourceEncoding)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom source.configurationInput)) :
    SemanticMolecule.cageEdges? (source.relabel symmetry).cageMolecule =
      some (source.package.edgeTable.map (source.relabelEdgeCanonical symmetry)) := by
  rw [cageMolecule_cageEdges?]
  rfl

end FullereneSourceEncoding

/-! ## Exact broad-element seam of `RawMolecule` -/

/-- Atomic number of a `PeriodicElement` reached from a parser `Element` is the parser's atomic
number.  This replicates the parser-refinement fact for the authority boundary. -/
private theorem fullereneParserElement_toPeriodic_atomicNumber (element : Element) (periodic : PeriodicElement)
    (converted : element.toPeriodic? = some periodic) :
    periodic.atomicNumber = element.atomicNumber := by
  cases element <;>
    simp [Element.toPeriodic?, PeriodicElement.ofAtomicNumber?, Element.atomicNumber] at converted
  all_goals
    subst periodic
    rfl

/-- Exact characterization of the broad labels reachable from the parser representation: an atom
is the image of some `AtomSpec` exactly when its electronic state has zero unpaired electrons and
its element has a parser preimage. -/
theorem semanticAtom_hasRawSource_iff (atom : SemanticAtom) :
    (∃ spec : AtomSpec, spec.toSemanticAtom? = some atom) ↔
      atom.unpairedElectrons = 0 ∧
        ∃ element : Element, element.toPeriodic? = some atom.element := by
  constructor
  · rintro ⟨spec, converted⟩
    cases observed : spec.element.toPeriodic? with
    | none => simp [AtomSpec.toSemanticAtom?, observed] at converted
    | some element =>
        have converted' : some
            ({ element := element
               isotopeMassNumber? := spec.isotope?
               formalCharge := spec.charge
               aromaticInput := spec.aromatic } : SemanticAtom) = some atom := by
          simpa [AtomSpec.toSemanticAtom?, observed] using converted
        have structureEq :
            ({ element := element
               isotopeMassNumber? := spec.isotope?
               formalCharge := spec.charge
               aromaticInput := spec.aromatic } : SemanticAtom) = atom :=
          Option.some.inj converted'
        subst atom
        exact ⟨rfl, spec.element, observed⟩
  · rintro ⟨radical, element, observed⟩
    refine ⟨{ element := element
              isotope? := atom.isotopeMassNumber?
              charge := atom.formalCharge
              aromatic := atom.aromaticInput }, ?_⟩
    cases atom with
    | mk atomElement isotope charge unpaired aromatic =>
        simp_all [AtomSpec.toSemanticAtom?]

/-- Any atom with a nonzero unpaired-electron count has no raw parser preimage.  This is the
electronic-state half of the seam. -/
theorem nonzeroUnpaired_not_hasRawSource (atom : SemanticAtom)
    (nonzero : atom.unpairedElectrons ≠ 0) :
    ¬ ∃ spec : AtomSpec, spec.toSemanticAtom? = some atom := by
  rintro ⟨spec, converted⟩
  rcases (semanticAtom_hasRawSource_iff atom).mp ⟨spec, converted⟩ with ⟨zero, _⟩
  exact nonzero zero

/-- Helium, which the parser's `Element` vocabulary does not contain. -/
def heliumPeriodic : PeriodicElement where
  atomicNumber := 2
  positive := by decide
  atMost118 := by decide

/-- The broad semantic helium atom. -/
def heliumSemanticAtom : SemanticAtom :=
  { element := heliumPeriodic }

/-- No parser `Element` reaches helium.  This is the element-vocabulary half of the seam. -/
theorem heliumPeriodic_not_rawElement :
    ¬ ∃ element : Element, element.toPeriodic? = some heliumPeriodic := by
  rintro ⟨element, converted⟩
  have atomic := fullereneParserElement_toPeriodic_atomicNumber element heliumPeriodic converted
  have rawBound : element.atomicNumber ≠ 2 := by
    cases element <;> decide
  exact rawBound (by simpa [heliumPeriodic] using atomic.symm)

/-- Helium has no raw parser preimage as a complete semantic atom. -/
theorem heliumSemanticAtom_not_hasRawSource :
    ¬ ∃ spec : AtomSpec, spec.toSemanticAtom? = some heliumSemanticAtom := by
  rintro ⟨spec, converted⟩
  rcases (semanticAtom_hasRawSource_iff heliumSemanticAtom).mp ⟨spec, converted⟩ with
    ⟨_, element, observed⟩
  exact heliumPeriodic_not_rawElement ⟨element, observed⟩

end

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.molecule_structurallyWellFormed
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.toAuthoritativeChemicalInput_structurallyWellFormed
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.cageAdjacent_iff_edgeTable
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.cageMolecule_cageEdges?
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.cageEdges?_toFinset_eq_certified
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceBundle.recoverPackage?_exact
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.toBundle_recoverPackage?
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.toBundle_recoverConfigurationInput?
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.toBundle_recovery_exact
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.relabel_cageAdjacent_iff
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.relabel_atomData_of_not_mem
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.relabel_molecule_structurallyWellFormed
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.relabel_toAuthoritativeChemicalInput_structurallyWellFormed
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.relabel_spatial?_eq_some
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.relabelSpatial_positions_getElem?
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.mem_relabelledEdgeTable_unordered_iff
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.relabel_cageEdges?
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.relabel_atomData_cage
assert_kernel_only
  TetraStereo.OneCenter.FullereneSourceEncoding.isForwardNamedCycleEdge_relabel
assert_kernel_only
  TetraStereo.OneCenter.semanticAtom_hasRawSource_iff
assert_kernel_only
  TetraStereo.OneCenter.heliumSemanticAtom_not_hasRawSource
assert_kernel_only
  TetraStereo.OneCenter.nonzeroUnpaired_not_hasRawSource
