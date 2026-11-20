import TetraStereo.OneCenter.LocalizedChemicalRingStateTransport
import TetraStereo.OneCenter.LocalizedMarkedCarrierLookup
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The executable raw-to-certified occurrence lookup commutes with molecular relabelling.
The proof uses uniqueness of the full occurrence coordinate, including history and provenance. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingLookupTransport

open CertifiedLocalizedCIPInput RawLocalizedChildNodeTransport
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedMarkedCarrierLookup LocalizedMarkedReachableConfigurations
open LocalizedMarkedCertifiedTerminalRefusal

variable (input : CertifiedLocalizedCIPInput)

theorem official_unique {left right : OfficialCIPNode input.Atom}
    {raw : RawMolecule.CanonicalBranchNode}
    (hl : NodeCorresponds Fin.val left raw) (hr : NodeCorresponds Fin.val right raw) : left = right := by
  have history : left.history = right.history :=
    (List.map_injective_iff.mpr Fin.val_injective) (hl.history.trans hr.history.symm)
  have current : left.current? = right.current? := by rw [← hl.head, ← hr.head, history]
  have provenance : left.provenance = right.provenance := by
    have unique : ∀ {a b c}, NodeProvenanceCorresponds a c →
        NodeProvenanceCorresponds b c → a = b := by
      intro a b c l r
      cases l <;> cases r <;> rfl
    exact unique hl.provenance hr.provenance
  cases left
  cases right
  cases history
  cases current
  cases provenance
  rfl

/-- At one carrier budget, the full official node determines its rooted occurrence. -/
theorem occurrence_unique (single : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (left right : input.LocalizedCIPOccurrence fuel) (nodes : left.1.node = right.1.node) : left = right := by
  have l := input.legitimateOccurrence_transport single (1 : input.moleculeGraph.Aut)
    (input.carrierOccurrence_legitimate single left)
  have r := input.legitimateOccurrence_transport single (1 : input.moleculeGraph.Aut)
    (input.carrierOccurrence_legitimate single right)
  have roots : left.1.root = right.1.root := Option.some.inj (l.sourceHead.symm.trans (nodes ▸ r.sourceHead))
  have addresses : left.1.address = right.1.address := by rw [l.sourceAddress, r.sourceAddress, roots, nodes]
  have gl := input.declarativeLocalizedOccurrence_depthGrade
    ((input.mem_localizedOccurrences_iff fuel left.1).mp left.2)
  have gr := input.declarativeLocalizedOccurrence_depthGrade
    ((input.mem_localizedOccurrences_iff fuel right.1).mp right.2)
  apply Subtype.ext
  apply LocalizedCIPOccurrenceFrame.ext input roots addresses nodes
  rw [addresses] at gl
  omega

theorem corresponds_relabel {mol : RawMolecule} (e : Equiv.Perm input.Atom)
    (sym : StructuralSymmetry mol (relabelOf input e))
    {official : OfficialCIPNode input.Atom} {raw : RawMolecule.CanonicalBranchNode}
    (corresponds : NodeCorresponds Fin.val official raw) :
    NodeCorresponds Fin.val (mapOfficialNode e official) (mapNode (relabelOf input e) raw) := by
  have op : ∀ value : Option input.Atom, (value.map e).map Fin.val =
      (value.map Fin.val).map (relabelOf input e) := by
    intro value
    cases value <;> simp [relabelOf_val]
  have lp : ∀ value : List input.Atom, (value.map e).map Fin.val =
      (value.map Fin.val).map (relabelOf input e) := by
    intro value
    simp only [List.map_map]
    apply List.map_congr_left
    intro atom _
    exact (relabelOf_val input e atom).symm
  refine ⟨?_, ?_, ?_, corresponds.provenance, ?_⟩
  · change (official.current?.map e).map Fin.val = some (relabelOf input e raw.atom)
    rw [op, corresponds.current]
    rfl
  · change (official.history.map e).map Fin.val = raw.history.map (relabelOf input e)
    rw [lp, corresponds.history]
  · simp only [mapOfficialNode, List.head?_map, corresponds.head]
  · rw [mapOfficialNode_parent?, op, corresponds.parent]
    change (if raw.parent = raw.atom then none else some raw.parent).map (relabelOf input e) =
      if relabelOf input e raw.parent = relabelOf input e raw.atom then none
      else some (relabelOf input e raw.parent)
    by_cases h : raw.parent = raw.atom <;> simp [h, sym.injective.eq_iff]

/-- Actual searches at reached occurrences return the transported carrier occurrence. -/
theorem lookup_transport (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    (sym : StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)))
    (raw : RawMolecule.CanonicalBranchNode) (reached : Reached mol raw)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (found : lookup? input raw = some target) :
    lookup? input (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) raw) =
      some (input.transportOccurrence single e target) := by
  have reached' := reached_map sym admissible.1.1 admissible.1.2
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single) raw reached
  obtain ⟨root, valid, path⟩ := reached'
  obtain ⟨image, result, _, corresponds⟩ := lookup?_exists_of_reachedFrom mol input agreement
    admissible.1.1 admissible.1.2 supported
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
    root valid _ path
  have transported := corresponds_relabel input (e : Equiv.Perm input.Atom) sym
    (lookup?_sound input raw target found)
  have nodes : image.1.node = (input.transportOccurrence single e target).1.node := by
    rw [input.transportOccurrence_node]
    exact official_unique input corresponds transported
  rw [result, occurrence_unique input single image _ nodes]

end TetraStereo.OneCenter.LocalizedChemicalRingLookupTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingLookupTransport.official_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingLookupTransport.occurrence_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingLookupTransport.lookup_transport
