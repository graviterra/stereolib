import TetraStereo.OneCenter.LocalizedChemicalRingWitnessDescendants
import TetraStereo.OneCenter.LocalizedChemicalRingWitnessExecution
import TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual real descendants remain in the residual component obtained by deleting a
boundary already carried in their source history. This is an operational-to-graph bridge:
canonical child membership, fresh-atom provenance, and intake agreement supply adjacency
and boundary avoidance. It does not assume that an occurrence has a descriptor. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingRawResidualDescendants

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingWitnessFactMatch
open LocalizedMarkedTerminalReferenceScope
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedTerminalGaugeFrame (child_bond)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)

abbrev Node := RawMolecule.CanonicalBranchNode

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)

include agreement admissible supported single in
/-- A real actual descendant is reachable without crossing the deleted history boundary.
Both its certified atom and the residual reachability are constructed from the raw steps. -/
theorem descendant_component (B : List input.Atom) (source target : Node)
    (entry : input.Atom) (entryEq : entry.val = source.atom) (outside : entry ∉ B)
    (carried : ∀ atom ∈ B, atom.val ∈ source.history)
    (descent : Descends mol source target) :
    target.forcedLeaf = false →
      ∃ atom : input.Atom, atom.val = target.atom ∧ InComponent input.moleculeGraph B entry atom := by
  induction descent with
  | refl => exact fun _ => ⟨entry, entryEq, inComponent_self input.moleculeGraph outside⟩
  | @tail parent child descent edge ih =>
      intro real
      have parentReal : parent.forcedLeaf = false := by
        cases leaf : parent.forcedLeaf with
        | false => rfl
        | true => simp [LocalizedGenericMarkedRecalculation.canonicalChildren_forcedLeaf mol parent leaf] at edge
      obtain ⟨parentAtom, parentEq, connected⟩ := ih parentReal
      have bond := child_bond mol admissible.1.1
        (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single) parent child edge
      have valid := (mol.bondOrder_pos_endpoint_lt admissible.1.1 bond).2
      let atom := atomOf mol input agreement child.atom valid
      have atomEq : atom.val = child.atom := rfl
      have childOutside : atom ∉ B := by
        intro member
        have history := history_mono descent (carried atom member)
        rw [atomEq] at history
        exact (LocalizedGenericMarkedRecalculation.mem_canonicalChildren mol parent child edge).2.1 real history
      have graphBond : input.moleculeGraph.Adj parentAtom atom := by
        change 0 < input.moleculeGraph.bond parentAtom atom
        rw [moleculeGraph_bond_eq_rawBondOrder mol input agreement
          admissible.1.1 admissible.1.2 supported, parentEq, atomEq]
        exact bond
      have adjacent : (residualGraph input.moleculeGraph B).Adj parentAtom atom :=
        ⟨inComponent_not_mem input.moleculeGraph connected, childOutside, graphBond⟩
      exact ⟨atom, atomEq, connected.1, connected.2.trans adjacent.reachable⟩

include agreement admissible supported single in
/-- A strict real descendant is a different atom in the same residual component. Thus
the ranked reconstruction's local induction hypothesis covers this actual computation. -/
theorem strict_descendant_rank (B : List input.Atom) (source target : Node)
    (entry : input.Atom) (entryEq : entry.val = source.atom) (outside : entry ∉ B)
    (carried : ∀ atom ∈ B, atom.val ∈ source.history)
    (sourceReached : Reached mol source) (descent : StrictDescendant mol source target)
    (real : target.forcedLeaf = false) (rank : input.Atom → Nat)
    (ordered : ∀ atom, InComponent input.moleculeGraph B entry atom → atom ≠ entry →
      rank entry < rank atom) :
    ∃ atom : input.Atom, atom.val = target.atom ∧ rank entry < rank atom := by
  obtain ⟨child, edge, rest⟩ := descent
  obtain ⟨atom, atomEq, connected⟩ := descendant_component input mol agreement admissible supported
    single B source target entry entryEq outside carried
    ((Relation.ReflTransGen.single edge).trans rest) real
  refine ⟨atom, atomEq, ordered atom connected ?_⟩
  intro same
  apply strictDescendant_atom_ne sourceReached ⟨child, edge, rest⟩ real
  rw [← atomEq, same, entryEq]

/-- The ranked witness supplies the boundary premises used by the operational bridge;
none of these history or freshness premises needs to be assumed at a chosen witness. -/
theorem witness_boundary (root entry : input.Atom) (path : List input.Atom)
    (valid : ResidualObsPath input.moleculeGraph [root] entry path) :
    (pathTerminal path valid.nonempty).val = (rawPathNode root path).atom ∧
    pathTerminal path valid.nonempty ∉ [root] ++ path.dropLast ∧
    (∀ atom ∈ [root] ++ path.dropLast, atom.val ∈ (rawPathNode root path).history) := by
  have split : path.dropLast ++ [pathTerminal path valid.nonempty] = path :=
    List.dropLast_append_getLast valid.nonempty
  have nodup : (path.dropLast ++ [pathTerminal path valid.nonempty]).Nodup := by
    rw [split]
    exact valid.nodup
  refine ⟨?_, ?_, ?_⟩
  · simp only [rawPathNode, pathTerminal, List.getLast?_eq_some_getLast valid.nonempty, Option.getD_some]
  · intro member
    rcases List.mem_append.mp member with boundary | earlier
    · exact valid.outside _ (List.getLast_mem valid.nonempty) boundary
    · exact (List.nodup_append.mp nodup).2.2 _ earlier _ (by simp) rfl
  · intro atom member
    apply List.mem_map.mpr
    refine ⟨atom, List.mem_reverse.mpr ?_, rfl⟩
    rcases List.mem_append.mp member with boundary | earlier
    · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp boundary))
    · exact List.mem_cons_of_mem _ ((List.dropLast_sublist path).mem earlier)

end TetraStereo.OneCenter.LocalizedChemicalRingRawResidualDescendants

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRawResidualDescendants.descendant_component
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRawResidualDescendants.strict_descendant_rank
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRawResidualDescendants.witness_boundary
