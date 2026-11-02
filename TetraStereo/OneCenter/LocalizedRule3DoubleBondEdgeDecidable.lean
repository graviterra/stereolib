import TetraStereo.OneCenter.LocalizedRule3Occurrence

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Executable decision procedure for the real Rule-3 double-bond edge

`LocalizedOccurrenceHasRule3DoubleBondEdge` is the structural proposition recognizing the physical
order-two parent/current edge stored by one official occurrence.  So far it was consumed only under
`classical`, inside `localizedDescriptorBearingRule3StructuralNode?`.  This module replaces that
classical decision by an executable `Bool` test and derives a computable `Decidable` instance:

* `localizedRule3DoubleBondEdgeExec` requires the node provenance to be
  `OfficialCIPNodeProvenance.realAtom` **and** the stored `current?`/`parent?` atoms to be joined by
  bond order two in the certified molecule graph;
* `localizedRule3DoubleBondEdgeMatch_eq_true_iff` isolates the stored-atom conjunct from
  provenance, so the option match is proved to be exactly the stored-parent/stored-current
  order-two witness;
* `localizedRule3DoubleBondEdgeExec_eq_true_iff` proves the whole `Bool` test to be exactly the
  original proposition, so no conjunct is dropped and no hypothesis is weakened; and
* `localizedOccurrenceHasRule3DoubleBondEdgeDecidable` is obtained by `decidable_of_iff`, so the
  occurrence-local edge predicate is decided by computation rather than by
  `Classical.propDecidable`.

Provenance is not decorative.  A multiple-bond or ring duplicate leaf may repeat the same
`current?`/`parent?` atoms and the same graph bond order, but it records rerooting bookkeeping, not
real geometry.  The provenance conjunct keeps the test `false` there, which is recorded by
`localizedRule3DoubleBondEdgeExec_eq_false_of_provenance_ne_real`.
-/

namespace CertifiedLocalizedCIPInput

/-- Executable, non-classical test for a real order-two parent/current edge at one official
occurrence.  Both conjuncts are required: `realAtom` provenance, and bond order two between the
stored parent and the stored current atom. -/
def localizedRule3DoubleBondEdgeExec (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) : Bool :=
  (occurrence.1.node.provenance == OfficialCIPNodeProvenance.realAtom) &&
    (match occurrence.1.node.current?, occurrence.1.node.parent? with
     | some current, some parent => input.moleculeGraph.bond parent current == 2
     | _, _ => false)

/-- The stored-atom conjunct, isolated from provenance.  The option match is `true` exactly when
the occurrence stores both a current and a parent atom and the certified molecule graph joins them
by bond order two. -/
theorem localizedRule3DoubleBondEdgeMatch_eq_true_iff
    (input : CertifiedLocalizedCIPInput) (current? parent? : Option input.Atom) :
    ((match current?, parent? with
      | some current, some parent => input.moleculeGraph.bond parent current == 2
      | _, _ => false) = true) ↔
      ∃ current parent,
        current? = some current ∧ parent? = some parent ∧
          input.moleculeGraph.bond parent current = 2 := by
  cases current? <;> cases parent? <;> simp

/-- The executable test denotes exactly the proof-facing structural edge proposition. -/
theorem localizedRule3DoubleBondEdgeExec_eq_true_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    input.localizedRule3DoubleBondEdgeExec occurrence = true ↔
      input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence := by
  unfold localizedRule3DoubleBondEdgeExec LocalizedOccurrenceHasRule3DoubleBondEdge
  constructor
  · intro computed
    simp only [Bool.and_eq_true, beq_iff_eq] at computed
    exact ⟨computed.1,
      (localizedRule3DoubleBondEdgeMatch_eq_true_iff input _ _).mp computed.2⟩
  · rintro ⟨real, current, parent, currentComputed, parentComputed, doubleBond⟩
    have stored :=
      (localizedRule3DoubleBondEdgeMatch_eq_true_iff input _ _).mpr
        ⟨current, parent, currentComputed, parentComputed, doubleBond⟩
    rw [Bool.and_eq_true]
    exact ⟨by simp [real], stored⟩

/-- The negation form of the executable test. -/
theorem localizedRule3DoubleBondEdgeExec_eq_false_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    input.localizedRule3DoubleBondEdgeExec occurrence = false ↔
      ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence := by
  constructor
  · intro computed edge
    have isTrue :=
      (input.localizedRule3DoubleBondEdgeExec_eq_true_iff occurrence).mpr edge
    rw [computed] at isTrue
    exact Bool.false_ne_true isTrue
  · intro noEdge
    cases computed : input.localizedRule3DoubleBondEdgeExec occurrence with
    | false => rfl
    | true =>
        exact absurd
          ((input.localizedRule3DoubleBondEdgeExec_eq_true_iff occurrence).mp computed)
          noEdge

/-- A node whose provenance is not `realAtom` never passes the executable edge test, whatever its
stored atom pair and graph bond order: multiple-bond and ring duplicates are rerooting
bookkeeping, not real geometry. -/
theorem localizedRule3DoubleBondEdgeExec_eq_false_of_provenance_ne_real
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (notReal : occurrence.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom) :
    input.localizedRule3DoubleBondEdgeExec occurrence = false :=
  (input.localizedRule3DoubleBondEdgeExec_eq_false_iff occurrence).mpr
    (fun edge => notReal edge.1)

/-- Computable decision procedure for the occurrence-local real double-bond edge, derived from the
executable test through the proved equivalence.  This is the non-classical replacement for
`Classical.propDecidable` at this predicate. -/
instance localizedOccurrenceHasRule3DoubleBondEdgeDecidable
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    Decidable (input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence) :=
  decidable_of_iff (input.localizedRule3DoubleBondEdgeExec occurrence = true)
    (input.localizedRule3DoubleBondEdgeExec_eq_true_iff occurrence)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
