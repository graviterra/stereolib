import TetraStereo.OneCenter.CIPRule2MassData
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through6Scheduler
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.MassEquivalentRule6SymmetryGuardProofs.MassEquivalentRule6SymmetryGuard

open TetraStereo.OneCenter

/-!
# Source-aware mass representation symmetry with four-ligand parity

This successor preserves the actual source Rule-6 guard's center fixation, complete
Rules-1a--5 partition preservation and transport of the actual root nodes. Only full SemanticAtom
identity in the constitutional automorphism is replaced by known-mass representation equivalence.
Oddness is tested on the induced permutation of Fin4 ligand positions, never on all source atoms.

The generic implication from the existing guard requires all source masses known. The concrete
C/I/[127I]/Br/F source supplies a center-fixed representation automorphism and an odd permutation
of its four physical written ligand nodes. It does not construct the scheduler's actual initial
partition or its returned occurrence-root frame, and therefore does not establish the full new
Rule-6 guard for that source or a production descriptor/refusal.

TECHNICAL_PROOF_REQUIRED: actual source-root frame and initial partition preservation for the
fixture; scheduler integration and a complete promoted-pipeline regression; broader domains.
HUMAN_REVIEW_REQUIRED: scientific adoption of ordinary I/[127I] equivalence under frozen Rule-2
policy and promotion conventions. EXTERNAL_EVIDENCE_REQUIRED: independent source adoption.
No completed source approval or chemical nonstereogenicity follows from this library unit.
-/

/-! ## 1. Conservative representation-aware atom profile -/

/-- A conservative representation-level atom signature.  It records exactly the attributes the guard
preserves: atomic number, the **known** frozen Rule-2 mass datum (an unknown spelling is `none`),
formal charge, unpaired-electron count and the aromatic-input flag. -/
structure AtomRepresentation where
  atomicNumber : Nat
  rule2Mass : Option Nat
  formalCharge : Int
  unpairedElectrons : Nat
  aromatic : Bool
  deriving DecidableEq, Repr

namespace AtomRepresentation

/-- The representation signature of one semantic atom.  The Rule-2 datum is the frozen
`SemanticAtom.rule2MassPico?`, so an absent frozen record is `none`. -/
def ofSemanticAtom (atom : SemanticAtom) : AtomRepresentation where
  atomicNumber := atom.element.atomicNumber
  rule2Mass := atom.rule2MassPico?
  formalCharge := atom.formalCharge
  unpairedElectrons := atom.unpairedElectrons
  aromatic := atom.aromaticInput

/-- Conservative representation-awareness.  Two atoms are interchangeable only when atomic number,
**known** Rule-2 mass, charge, radical state and aromatic flag all agree, and the Rule-2 mass is
present on the left.  Because the known-mass conjunct is a `some` requirement, two atoms whose frozen
Rule-2 datum is absent (`none`) are never equated. -/
def Represents (left right : AtomRepresentation) : Prop :=
  left.atomicNumber = right.atomicNumber ∧
    left.rule2Mass.isSome = true ∧
    left.rule2Mass = right.rule2Mass ∧
    left.formalCharge = right.formalCharge ∧
    left.unpairedElectrons = right.unpairedElectrons ∧
    left.aromatic = right.aromatic

theorem represents_atomicNumber {left right : AtomRepresentation} (h : Represents left right) :
    left.atomicNumber = right.atomicNumber := h.1

theorem represents_rule2Mass_isSome {left right : AtomRepresentation} (h : Represents left right) :
    left.rule2Mass.isSome = true := h.2.1

theorem represents_rule2Mass_eq {left right : AtomRepresentation} (h : Represents left right) :
    left.rule2Mass = right.rule2Mass := h.2.2.1

/-- A representation with an absent frozen Rule-2 datum is never representation-aware equal, least of
all to another absent mass: `none` is not a licence to equate unknowns. -/
theorem represents_rule2Mass_ne_none {left right : AtomRepresentation} (h : Represents left right) :
    left.rule2Mass ≠ none := by
  intro hnone
  have his := h.2.1
  rw [hnone] at his
  exact Bool.false_ne_true his

/-- Reflexivity is available exactly for representations with a known Rule-2 mass. -/
theorem refl_of_isSome {atom : AtomRepresentation} (h : atom.rule2Mass.isSome = true) :
    Represents atom atom :=
  ⟨rfl, h, rfl, rfl, rfl, rfl⟩

theorem symm {left right : AtomRepresentation} (h : Represents left right) :
    Represents right left := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1.symm, by rw [← h3]; exact h2, h3.symm, h4.symm, h5.symm, h6.symm⟩

theorem trans {a b c : AtomRepresentation} (hab : Represents a b) (hbc : Represents b c) :
    Represents a c := by
  rcases hab with ⟨h1, h2, h3, h4, h5, h6⟩
  rcases hbc with ⟨g1, g2, g3, g4, g5, g6⟩
  exact ⟨h1.trans g1, h2, h3.trans g3, h4.trans g4, h5.trans g5, h6.trans g6⟩

/-- An unknown mass on the left is not equated with anything. -/
theorem not_represents_of_left_rule2Mass_none {left right : AtomRepresentation}
    (h : left.rule2Mass = none) : ¬ Represents left right := by
  intro r
  have his := r.2.1
  rw [h] at his
  exact Bool.false_ne_true his

/-- Two unknown masses are not equated by both being `none`. -/
theorem not_represents_of_unknown_masses {left right : AtomRepresentation}
    (hl : left.rule2Mass = none) (_hr : right.rule2Mass = none) : ¬ Represents left right :=
  not_represents_of_left_rule2Mass_none hl

/-- Distinct known Rule-2 masses are not equated. -/
theorem not_represents_of_rule2Mass_ne {left right : AtomRepresentation}
    (h : left.rule2Mass ≠ right.rule2Mass) : ¬ Represents left right := by
  intro r
  exact h r.2.2.1

/-- Distinct atomic numbers are not equated. -/
theorem not_represents_of_atomicNumber_ne {left right : AtomRepresentation}
    (h : left.atomicNumber ≠ right.atomicNumber) : ¬ Represents left right := by
  intro r
  exact h r.1

/-- Distinct formal charges are not equated. -/
theorem not_represents_of_formalCharge_ne {left right : AtomRepresentation}
    (h : left.formalCharge ≠ right.formalCharge) : ¬ Represents left right := by
  intro r
  exact h r.2.2.2.1

/-- An atom with a frozen Rule-2 datum has a `some` representation mass. -/
theorem ofSemanticAtom_rule2Mass_isSome_of_known {atom : SemanticAtom}
    (h : atom.Rule2MassKnown) :
    (ofSemanticAtom atom).rule2Mass.isSome = true := by
  obtain ⟨m, hm⟩ := h
  show atom.rule2MassPico?.isSome = true
  rw [hm]
  rfl

end AtomRepresentation

/-! ## 2. An actual five-atom mass-equivalent iodine source -/

namespace IodineCounterexample

/-- The tetrahedral carbon center. -/
def carbonAtom : SemanticAtom := { element := ⟨6, by decide, by decide⟩ }

/-- Ordinary unlabelled iodine (atomic number 53, no explicit isotope label). -/
def ordinaryIodineAtom : SemanticAtom := { element := ⟨53, by decide, by decide⟩ }

/-- Explicitly labelled iodine-127. -/
def iodine127Atom : SemanticAtom :=
  { element := ⟨53, by decide, by decide⟩, isotopeMassNumber? := some 127 }

/-- Bromine. -/
def bromineAtom : SemanticAtom := { element := ⟨35, by decide, by decide⟩ }

/-- Fluorine. -/
def fluorineAtom : SemanticAtom := { element := ⟨9, by decide, by decide⟩ }



def iodineSourceMolecule : SemanticMolecule where
  atoms := [carbonAtom, ordinaryIodineAtom, iodine127Atom, bromineAtom, fluorineAtom]
  interactions :=
    [ { participants := [0, 1], kind := .covalent 1 },
      { participants := [0, 2], kind := .covalent 1 },
      { participants := [0, 3], kind := .covalent 1 },
      { participants := [0, 4], kind := .covalent 1 } ]

/-- The exact source object: the five-atom constitution plus the literal clockwise atom annotation at
the carbon centre (`atom := 0`).  The source is reconstructed from its own field data; it is not a cast
of another molecule that happens to share a constitution. -/
def iodineSource : AuthoritativeChemicalInput where
  molecule := iodineSourceMolecule
  diagram? := some { atomConfigurations := [{ atom := 0, parity := .clockwise }] }

theorem iodineSource_atoms :
    iodineSource.molecule.atoms = [carbonAtom, ordinaryIodineAtom, iodine127Atom, bromineAtom,
      fluorineAtom] := rfl

theorem iodineSource_interactions :
    iodineSource.molecule.interactions =
      [ { participants := [0, 1], kind := .covalent 1 },
        { participants := [0, 2], kind := .covalent 1 },
        { participants := [0, 3], kind := .covalent 1 },
        { participants := [0, 4], kind := .covalent 1 } ] := rfl

theorem iodineSource_diagram :
    iodineSource.diagram? =
      some { atomConfigurations := [{ atom := 0, parity := .clockwise }] } := rfl

/-! ### Concrete representation signatures -/

def carbonRepresentation : AtomRepresentation where
  atomicNumber := 6
  rule2Mass := CIPRule2MassData.rule2MassPico? 6 none
  formalCharge := 0
  unpairedElectrons := 0
  aromatic := false

def ordinaryIodineRepresentation : AtomRepresentation where
  atomicNumber := 53
  rule2Mass := CIPRule2MassData.rule2MassPico? 53 none
  formalCharge := 0
  unpairedElectrons := 0
  aromatic := false

def iodine127Representation : AtomRepresentation where
  atomicNumber := 53
  rule2Mass := CIPRule2MassData.rule2MassPico? 53 (some 127)
  formalCharge := 0
  unpairedElectrons := 0
  aromatic := false

def bromineRepresentation : AtomRepresentation where
  atomicNumber := 35
  rule2Mass := CIPRule2MassData.rule2MassPico? 35 none
  formalCharge := 0
  unpairedElectrons := 0
  aromatic := false

def fluorineRepresentation : AtomRepresentation where
  atomicNumber := 9
  rule2Mass := CIPRule2MassData.rule2MassPico? 9 none
  formalCharge := 0
  unpairedElectrons := 0
  aromatic := false

theorem carbonRepresentation_eq :
    AtomRepresentation.ofSemanticAtom carbonAtom = carbonRepresentation := rfl

theorem ordinaryIodineRepresentation_eq :
    AtomRepresentation.ofSemanticAtom ordinaryIodineAtom = ordinaryIodineRepresentation := rfl

theorem iodine127Representation_eq :
    AtomRepresentation.ofSemanticAtom iodine127Atom = iodine127Representation := rfl

theorem bromineRepresentation_eq :
    AtomRepresentation.ofSemanticAtom bromineAtom = bromineRepresentation := rfl

theorem fluorineRepresentation_eq :
    AtomRepresentation.ofSemanticAtom fluorineAtom = fluorineRepresentation := rfl

/-- Every ordinary current element has a `some` frozen Rule-2 mass, without re-deciding the frozen
tables: this is exactly `every_current_atomic_number_has_an_ordinary_value`. -/
theorem ordinaryRule2Mass_isSome_of_mem (atomicNumber : Nat)
    (h : atomicNumber ∈ CIPRule2MassData.currentAtomicNumbers) :
    (CIPRule2MassData.rule2MassPico? atomicNumber none).isSome = true := by
  show (CIPRule2MassData.ordinaryAtomicMassPico? atomicNumber).isSome = true
  exact Option.isSome_iff_exists.mpr
    (CIPRule2MassData.every_current_atomic_number_has_an_ordinary_value atomicNumber h)

theorem carbon_rule2Mass_isSome : carbonRepresentation.rule2Mass.isSome = true :=
  ordinaryRule2Mass_isSome_of_mem 6 (by decide)

theorem ordinaryIodine_rule2Mass_isSome :
    ordinaryIodineRepresentation.rule2Mass.isSome = true :=
  ordinaryRule2Mass_isSome_of_mem 53 (by decide)

theorem bromine_rule2Mass_isSome : bromineRepresentation.rule2Mass.isSome = true :=
  ordinaryRule2Mass_isSome_of_mem 35 (by decide)

theorem fluorine_rule2Mass_isSome : fluorineRepresentation.rule2Mass.isSome = true :=
  ordinaryRule2Mass_isSome_of_mem 9 (by decide)

theorem iodine127_rule2Mass_isSome :
    iodine127Representation.rule2Mass.isSome = true := by
  show (CIPRule2MassData.rule2MassPico? 53 (some 127)).isSome = true
  rw [← CIPRule2MassData.ordinary_iodine_eq_iodine127]
  exact ordinaryIodine_rule2Mass_isSome

/-- **The two iodine terminal Rule-2 masses are equal.**  This is the frozen source identity
`CIPRule2MassData.ordinary_iodine_eq_iodine127`, read at the representation layer. -/
theorem iodines_represent :
    AtomRepresentation.Represents ordinaryIodineRepresentation iodine127Representation := by
  refine ⟨rfl, ordinaryIodine_rule2Mass_isSome, ?_, rfl, rfl, rfl⟩
  show CIPRule2MassData.rule2MassPico? 53 none = CIPRule2MassData.rule2MassPico? 53 (some 127)
  exact CIPRule2MassData.ordinary_iodine_eq_iodine127

/-- The profile distinguishes iodine from bromine by their actual atomic numbers. -/
theorem iodine_not_represent_bromine :
    ¬ AtomRepresentation.Represents ordinaryIodineRepresentation bromineRepresentation := by
  apply AtomRepresentation.not_represents_of_atomicNumber_ne
  show (53 : Nat) ≠ 35
  decide

/-- A concrete unknown isotope label of carbon (`C-999`) whose frozen Rule-2 datum is absent. -/
def carbon999Representation : AtomRepresentation where
  atomicNumber := 6
  rule2Mass := CIPRule2MassData.rule2MassPico? 6 (some 999)
  formalCharge := 0
  unpairedElectrons := 0
  aromatic := false

theorem carbon999_rule2Mass_eq_none : carbon999Representation.rule2Mass = none := by
  show CIPRule2MassData.rule2MassPico? 6 (some 999) = none
  exact CIPRule2MassData.carbon999_is_unknown

/-- Two absent frozen Rule-2 data are not equated by both being `none`. -/
theorem unknown_masses_not_equated :
    ¬ AtomRepresentation.Represents carbon999Representation carbon999Representation :=
  AtomRepresentation.not_represents_of_unknown_masses
    carbon999_rule2Mass_eq_none carbon999_rule2Mass_eq_none

/-! ### The concrete ligand frame, its bond order, and the iodine exchange -/

/-- The representation signature of the source positions `0..4`, in written order. -/
def sourceRep (i : Fin 5) : AtomRepresentation :=
  match i.val with
  | 0 => carbonRepresentation
  | 1 => ordinaryIodineRepresentation
  | 2 => iodine127Representation
  | 3 => bromineRepresentation
  | _ => fluorineRepresentation

/-- The actual source bond order, read from the source's own canonical digraph. -/
def sourceBond (i j : Fin 5) : Nat :=
  iodineSource.molecule.aromaticCanonicalBondOrder i.val j.val

/-- The written center position `C0`. -/
def centerIndex : Fin 5 := 0

/-- The unwritten ligand exchange of the two iodines. -/
def ligandSwap : Equiv.Perm (Fin 5) := Equiv.swap (1 : Fin 5) 2

/-- The representation signature at each source position is exactly the representation of the source's
own atom there. -/
theorem sourceRep_eq_ofSemanticAtom (i : Fin 5) :
    sourceRep i =
      AtomRepresentation.ofSemanticAtom
        (match i.val with
          | 0 => carbonAtom
          | 1 => ordinaryIodineAtom
          | 2 => iodine127Atom
          | 3 => bromineAtom
          | _ => fluorineAtom) := by
  fin_cases i <;> rfl

theorem ligandSwap_zero : ligandSwap (0 : Fin 5) = 0 := by
  decide +kernel

theorem ligandSwap_one : ligandSwap (1 : Fin 5) = 2 := by
  decide +kernel

theorem ligandSwap_two : ligandSwap (2 : Fin 5) = 1 := by
  decide +kernel

theorem ligandSwap_three : ligandSwap (3 : Fin 5) = 3 := by
  decide +kernel

theorem ligandSwap_four : ligandSwap (4 : Fin 5) = 4 := by
  decide +kernel

theorem ligandSwap_center : ligandSwap centerIndex = centerIndex := by
  show ligandSwap (0 : Fin 5) = 0
  exact ligandSwap_zero

/-! The exchange preserves the representation at every written position: at the carbon, and at the
untouched bromine and fluorine it is a reflexivity; at the two iodines it is the frozen mass identity. -/

theorem ligandSwap_preserves_rep (i : Fin 5) :
    AtomRepresentation.Represents (sourceRep i) (sourceRep (ligandSwap i)) := by
  fin_cases i
  · change AtomRepresentation.Represents carbonRepresentation carbonRepresentation
    exact AtomRepresentation.refl_of_isSome carbon_rule2Mass_isSome
  · change AtomRepresentation.Represents ordinaryIodineRepresentation iodine127Representation
    exact iodines_represent
  · change AtomRepresentation.Represents iodine127Representation ordinaryIodineRepresentation
    exact AtomRepresentation.symm iodines_represent
  · change AtomRepresentation.Represents bromineRepresentation bromineRepresentation
    exact AtomRepresentation.refl_of_isSome bromine_rule2Mass_isSome
  · change AtomRepresentation.Represents fluorineRepresentation fluorineRepresentation
    exact AtomRepresentation.refl_of_isSome fluorine_rule2Mass_isSome

/-- The exchange preserves every source bond order: all bonds are single bonds from the fixed carbon
and the permutation only touches the four ligand positions. -/
theorem ligandSwap_preserves_bond (i j : Fin 5) :
    sourceBond i j = sourceBond (ligandSwap i) (ligandSwap j) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

end IodineCounterexample

/-! ## 3. The old guard requires full identity: isolating the exact gap -/

open IodineCounterexample

/-- The two iodine `SemanticAtom`s differ in their explicit isotope label, hence are unequal as
`SemanticAtom`s. -/
theorem ordinaryIodine_ne_iodine127 : ordinaryIodineAtom ≠ iodine127Atom := by
  intro h
  have key : (none : Option Nat) = some 127 :=
    congrArg (fun a : SemanticAtom => a.isotopeMassNumber?) h
  cases key

/-- Full SemanticAtom identity cannot exchange these two distinct isotope-label representations.
This isolates a representation distinction without concluding chemical nonstereogenicity. -/
theorem no_constitutionAutomorphism_maps_ordinaryIodine_to_iodine127
    (source : AuthoritativeChemicalInput)
    (perm : Equiv.Perm source.AromaticCanonicalAtom)
    (aut : source.AromaticCanonicalConstitutionAutomorphism perm)
    {i j : source.AromaticCanonicalAtom}
    (hi : source.molecule.atoms.get i = ordinaryIodineAtom)
    (hj : source.molecule.atoms.get j = iodine127Atom)
    (hij : perm i = j) : False := by
  have h := aut.1 i
  rw [hij, hi, hj] at h
  exact ordinaryIodine_ne_iodine127 h.symm

/-- The representation-aware conservative replacement for
`AromaticCanonicalConstitutionAutomorphism`: identity of `SemanticAtom` is replaced by
`AtomRepresentation.Represents` at every atom, while the bond-order and aromatic-pair preservation
conditions are retained verbatim. -/
def AromaticCanonicalConstitutionRepresentationAutomorphism
    (source : AuthoritativeChemicalInput)
    (perm : Equiv.Perm source.AromaticCanonicalAtom) : Prop :=
  (∀ atom : source.AromaticCanonicalAtom, AtomRepresentation.Represents
      (AtomRepresentation.ofSemanticAtom (source.molecule.atoms.get atom))
      (AtomRepresentation.ofSemanticAtom (source.molecule.atoms.get (perm atom)))) ∧
    (∀ left right : source.AromaticCanonicalAtom,
      source.molecule.aromaticCanonicalBondOrder left.val right.val =
        source.molecule.aromaticCanonicalBondOrder (perm left).val (perm right).val) ∧
    (∀ left right : source.AromaticCanonicalAtom, source.molecule.aromaticPairEdges.contains
        (semanticEdgeKey left.val right.val) =
      source.molecule.aromaticPairEdges.contains
        (semanticEdgeKey (perm left).val (perm right).val))

/-- Every full-identity automorphism preserves the known-mass representation profile when all
source Rule-2 masses are known. This is an implication between graph predicates, not a production
admission or chemical equivalence theorem. -/
theorem constitutionAutomorphism_implies_representationAutomorphism
    (source : AuthoritativeChemicalInput)
    (perm : Equiv.Perm source.AromaticCanonicalAtom)
    (known : source.molecule.AllRule2MassesKnown)
    (aut : source.AromaticCanonicalConstitutionAutomorphism perm) :
    AromaticCanonicalConstitutionRepresentationAutomorphism source perm := by
  refine ⟨?_, aut.2.1, aut.2.2⟩
  intro atom
  have hEq := aut.1 atom
  have atomKnown : (source.molecule.atoms.get atom).Rule2MassKnown :=
    known (source.molecule.atoms.get atom) (List.get_mem _ _)
  rw [hEq]
  exact AtomRepresentation.refl_of_isSome
    (AtomRepresentation.ofSemanticAtom_rule2Mass_isSome_of_known atomKnown)

/-- Source Rule-6 exclusion with exactly the original center, partition and root-transport
clauses. The parity belongs to the four ligand positions; atomPermutation has no sign condition. -/
def AromaticCanonicalRule6OddRepresentationAutomorphism
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel) : Prop :=
  ∃ positionPermutation : Equiv.Perm (Fin 4),
    Equiv.Perm.sign positionPermutation = -1 ∧
    (∀ position,
      source.compareAromaticCanonicalRule3Through5RootPositions partition.frame
          position (positionPermutation position) = Ordering.eq) ∧
    ∃ atomPermutation : Equiv.Perm source.AromaticCanonicalAtom,
      AromaticCanonicalConstitutionRepresentationAutomorphism source atomPermutation ∧
      atomPermutation center = center ∧
      ∀ position,
        AuthoritativeChemicalInput.mapAromaticCanonicalOfficialCIPNode atomPermutation
            (source.aromaticCanonicalRule6RootAt roots rootsLength position).occurrence.1.node =
          (source.aromaticCanonicalRule6RootAt roots rootsLength
            (positionPermutation position)).occurrence.1.node

/-- Restricted topology predicate mirroring the original source guard. Its use in production must
retain the independently checked mass-availability domain; absence of a representation witness
alone does not establish chemical validity for unknown-mass inputs. -/
def AromaticCanonicalRule6RepresentationTopologyAdmissible
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel) : Prop :=
  ¬ AromaticCanonicalRule6OddRepresentationAutomorphism source center roots rootsLength partition

/-- On known-mass sources, every actual old odd four-position witness remains a new witness.
No successful partition computation, sort or desired descriptor is supplied or concluded. -/
theorem old_odd_guard_implies_representation_odd_guard
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (known : source.molecule.AllRule2MassesKnown)
    (old : source.AromaticCanonicalRule6OddConstitutionAutomorphism
      center roots rootsLength partition) :
    AromaticCanonicalRule6OddRepresentationAutomorphism source center roots rootsLength partition := by
  obtain ⟨positions, oddSign, preserved, atoms, constitution, fixed, transported⟩ := old
  exact ⟨positions, oddSign, preserved, atoms,
    constitutionAutomorphism_implies_representationAutomorphism source atoms known constitution,
    fixed, transported⟩

theorem representation_topology_implies_original_topology
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (known : source.molecule.AllRule2MassesKnown)
    (admitted : AromaticCanonicalRule6RepresentationTopologyAdmissible
      source center roots rootsLength partition) :
    source.AromaticCanonicalRule6TopologyAdmissible center roots rootsLength partition := by
  intro old
  exact admitted (old_odd_guard_implies_representation_odd_guard
    source center roots rootsLength partition known old)

namespace IodineCounterexample

/-- The actual source center ID, constructed without a source-dependent numeral instance. -/
def sourceCenter : iodineSource.AromaticCanonicalAtom := ⟨0, by decide⟩

/-- The four actual physical ligand IDs in the written C0 frame. -/
def ligandAtom (position : Fin 4) : iodineSource.AromaticCanonicalAtom :=
  ⟨position.val + 1, by have bound := position.isLt; change position.val + 1 < 5; omega⟩

theorem ligandAtom_injective : Function.Injective ligandAtom := by
  intro left right equal
  have values := congrArg (fun atom : iodineSource.AromaticCanonicalAtom => atom.val) equal
  change left.val + 1 = right.val + 1 at values
  exact Fin.ext (Nat.add_right_cancel values)

theorem ligandAtom_physical_bond (position : Fin 4) :
    iodineSource.molecule.aromaticCanonicalBondOrder 0 (ligandAtom position).val = 1 := by
  fin_cases position <;> decide +kernel

/-- The induced iodine exchange on four ligand positions, separate from the atom permutation. -/
def positionSwap : Equiv.Perm (Fin 4) := Equiv.swap (0 : Fin 4) 1

theorem positionSwap_odd : Equiv.Perm.sign positionSwap = -1 := by
  simp [positionSwap]

theorem ligandSwap_transports_ligand_atoms (position : Fin 4) :
    ligandSwap (ligandAtom position) = ligandAtom (positionSwap position) := by
  fin_cases position <;> decide +kernel

/-- These nodes are reconstructed from the same source's actual physical center and endpoints.
They are not asserted to be the scheduler's returned occurrence cursors. -/
def writtenRootNode (position : Fin 4) : OfficialCIPNode iodineSource.AromaticCanonicalAtom :=
  OfficialCIPNode.rootFromEdge sourceCenter (ligandAtom position)

theorem ligandSwap_transports_written_root_nodes (position : Fin 4) :
    AuthoritativeChemicalInput.mapAromaticCanonicalOfficialCIPNode (source := iodineSource) ligandSwap
        (writtenRootNode position) = writtenRootNode (positionSwap position) := by
  fin_cases position <;> decide +kernel

theorem source_representation_at_actual_atom (atom : iodineSource.AromaticCanonicalAtom) :
    AtomRepresentation.ofSemanticAtom (iodineSource.molecule.atoms.get atom) = sourceRep atom := by
  fin_cases atom <;> rfl

theorem ligandSwap_representation_automorphism :
    AromaticCanonicalConstitutionRepresentationAutomorphism iodineSource ligandSwap := by
  refine ⟨?_, ?_, ?_⟩
  · intro atom
    simpa only [source_representation_at_actual_atom] using ligandSwap_preserves_rep atom
  · exact ligandSwap_preserves_bond
  · intro left right
    fin_cases left <;> fin_cases right <;> decide +kernel

/-- An actual graph automorphism and odd physical-ligand exchange, leaving the full partition
obligation explicit: this theorem does not claim the corrected Rule-6 guard has been discharged. -/
theorem iodine_source_graph_and_ligand_symmetry :
    AromaticCanonicalConstitutionRepresentationAutomorphism iodineSource ligandSwap ∧
      ligandSwap sourceCenter = sourceCenter ∧
      Equiv.Perm.sign positionSwap = -1 ∧
      ∀ position,
        AuthoritativeChemicalInput.mapAromaticCanonicalOfficialCIPNode (source := iodineSource) ligandSwap
          (writtenRootNode position) = writtenRootNode (positionSwap position) :=
  ⟨ligandSwap_representation_automorphism, ligandSwap_zero, positionSwap_odd,
    ligandSwap_transports_written_root_nodes⟩

end IodineCounterexample

end TetraStereo.UniversalProof.MassEquivalentRule6SymmetryGuardProofs.MassEquivalentRule6SymmetryGuard
