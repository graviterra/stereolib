import TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense
import TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader
import TetraStereo.OneCenter.LocalizedRetainedGeneratedCovariance
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Transport of the actual raw auxiliary reader

Raw facts are looked up by occurrence history, not atom number alone. Relabelling every
history and permuting a state with unique keys preserves the descriptor read at the transported
occurrence. This derives molecular-reader transport for the actual retained state adapter;
no agreement of generated labels is assumed.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingStateTransport

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingRelabel LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingPhysicalSense LocalizedMarkedRetainedStateReader

theorem find_key_perm {α K : Type*} [BEq K] [LawfulBEq K]
    (key : α → K) {xs ys : List α} (perm : xs.Perm ys)
    (unique : (ys.map key).Nodup) (k : K) :
    xs.find? (fun x => key x == k) = ys.find? (fun x => key x == k) := by
  cases hx : xs.find? (fun x => key x == k) with
  | none =>
      apply Eq.symm
      apply List.find?_eq_none.mpr
      intro x member
      exact List.find?_eq_none.mp hx x (perm.mem_iff.mpr member)
  | some x =>
      have mx := perm.mem_iff.mp (List.mem_of_find?_eq_some hx)
      have kx : key x = k := by simpa using List.find?_some hx
      cases hy : ys.find? (fun x => key x == k) with
      | none =>
          have := List.find?_eq_none.mp hy x mx
          simp [kx] at this
      | some y =>
          have my := List.mem_of_find?_eq_some hy
          have ky : key y = k := by simpa using List.find?_some hy
          exact congrArg some (List.inj_on_of_nodup_map unique mx my (kx.trans ky.symm))

variable (input : CertifiedLocalizedCIPInput)

theorem rawOccurrenceKey_transport (e : Equiv.Perm input.Atom) (unit : OccurrenceUnit input.Atom) :
    rawOccurrenceKey (transportOccurrenceUnit e unit) =
      mapKey (relabelOf input e) (rawOccurrenceKey unit) := by
  have vals : ∀ xs : List input.Atom,
      (xs.map e).map Fin.val = (xs.map Fin.val).map (relabelOf input e) := by
    intro xs
    simp only [List.map_map]
    apply List.map_congr_left
    intro a _
    exact (relabelOf_val input e a).symm
  unfold rawOccurrenceKey transportOccurrenceUnit mapKey
  congr 1
  change ((e unit.root :: unit.path.map e).reverse.map Fin.val) =
    ((unit.root :: unit.path).reverse.map Fin.val).map (relabelOf input e)
  rw [← List.map_cons, ← List.map_reverse, vals]

theorem rawStateFact_transport {mol : RawMolecule} (e : Equiv.Perm input.Atom)
    (sym : StructuralSymmetry mol (relabelOf input e))
    (state state' : OccurrenceAuxState)
    (perm : state'.Perm (state.map (mapFact (relabelOf input e))))
    (unique : (state.map (·.key)).Nodup) (unit : OccurrenceUnit input.Atom) :
    rawStateFact? state' (transportOccurrenceUnit e unit) =
      (rawStateFact? state unit).map (mapFact (relabelOf input e)) := by
  unfold rawStateFact?
  have mappedUnique : ((state.map (mapFact (relabelOf input e))).map (·.key)).Nodup :=
    (keys_nodup_iff sym (List.Perm.refl _)).mpr unique
  rw [find_key_perm (fun fact : OccurrenceAuxFact => fact.key) perm mappedUnique,
    List.find?_map, rawOccurrenceKey_transport]
  congr 2
  funext fact
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, mapFact_key_eq, beq_iff_eq]
  exact (mapKey_injective sym).eq_iff

theorem factDescriptor_mapFact (σ : Nat → Nat) (fact : OccurrenceAuxFact) :
    factDescriptor (mapFact σ fact) = factDescriptor fact := rfl

theorem rawStateDescriptorMap_transport {mol : RawMolecule} (e : input.moleculeGraph.Aut)
    (sym : StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)))
    (state state' : OccurrenceAuxState)
    (perm : state'.Perm (state.map (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))))
    (unique : (state.map (·.key)).Nodup) :
    rawStateDescriptorMap input state' =
      input.transportDescriptorMap e (rawStateDescriptorMap input state) := by
  funext unit
  let original := input.transportDetectedOccurrence (e⁻¹) unit
  have round : input.transportDetectedOccurrence e original = unit := by
    simpa [original] using input.transportDetectedOccurrence_symm_apply (e⁻¹) unit
  conv_lhs => rw [← round]
  change (rawStateFact? state' (transportOccurrenceUnit (e : Equiv.Perm input.Atom) original.1)).map
      factDescriptor = (rawStateFact? state original.1).map factDescriptor
  rw [rawStateFact_transport input (e : Equiv.Perm input.Atom) sym state state' perm unique]
  rw [Option.map_map]
  rfl

/-- Actual retained readers commute with relabelling at every cursor, including duplicate
leaves and arbitrary context depth. Unique-key states are precisely the states accepted by the
recursive evaluator's append operation. -/
theorem rawStateReader_transport {mol : RawMolecule}
    (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    (sym : StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)))
    (state state' : OccurrenceAuxState)
    (perm : state'.Perm (state.map (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))))
    (unique : (state.map (·.key)).Nodup) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (cursor : input.LocalizedRerootCursor fuel) :
    rawStateReader input state' (input.transportOccurrence single e target)
        (input.transportCursor single e cursor) = rawStateReader input state target cursor := by
  rw [rawStateReader_eq_molecularReader, rawStateReader_eq_molecularReader,
    rawStateDescriptorMap_transport input e sym state state' perm unique]
  exact input.molecularReader_transport single e (rawStateDescriptorMap input state) target cursor

end TetraStereo.OneCenter.LocalizedChemicalRingStateTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStateTransport.find_key_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStateTransport.rawOccurrenceKey_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStateTransport.rawStateFact_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStateTransport.rawStateDescriptorMap_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStateTransport.rawStateReader_transport
