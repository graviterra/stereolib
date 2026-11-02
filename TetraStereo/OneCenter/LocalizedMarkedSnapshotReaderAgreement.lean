import TetraStereo.OneCenter.LocalizedMarkedDetectedSnapshotSupport
import TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Exact retained reading of an actual generated snapshot

The retained reader's real/detected/strict-dependency filters discard no successful lookup in an
actual generated promotion snapshot. Support is derived from the snapshot computation, not
supplied. Existing cyclic-carrier injectivity identifies the constructed support occurrences with
any given corresponding source and query carriers. Both successful and absent lookups are
preserved. This is reader agreement, not comparison equivalence or correctness of generated labels.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedSnapshotReaderAgreement

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedOperationEvaluator LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors LocalizedMarkedDetectedSnapshotSupport
open LocalizedMarkedRetainedStateReader RawLocalizedChildNodeTransport
open LocalizedGenericMarkedRecalculation (Geometry)

abbrev Node := RawMolecule.CanonicalBranchNode

/-- Within the actual single-bond carrier, even with rings, mapped histories determine the whole
occurrence. This reuses the existing cyclic carrier theorem, not an acyclicity assumption. -/
theorem carrier_eq_of_mapped_history_eq (input : CertifiedLocalizedCIPInput)
    (single : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (left right : input.LocalizedCIPOccurrence fuel)
    (mapped : left.1.node.history.map (fun atom : input.Atom => atom.val) =
      right.1.node.history.map (fun atom : input.Atom => atom.val)) : left = right := by
  have history : left.1.node.history = right.1.node.history :=
    (List.map_injective_iff.mpr Fin.val_injective) mapped
  have leftLast := input.carrierOccurrence_history_getLast_eq_root single left
  have rightLast := input.carrierOccurrence_history_getLast_eq_root single right
  have root : left.1.root = right.1.root :=
    Option.some.inj (leftLast.symm.trans ((congrArg List.getLast? history).trans rightLast))
  apply input.molecularFrameUnit_injective_on_simpleBonded_carrier single left right
  simp only [molecularFrameUnit, history, root]

private theorem correspondence_real_iff
    {official : OfficialCIPNodeProvenance} {raw : RawMolecule.CanonicalNodeProvenance}
    (corresponds : NodeProvenanceCorresponds official raw) :
    official = .realAtom ↔ raw = .realAtom := by
  cases corresponds <;> simp

/-- Exact total reading at arbitrary corresponding actual carrier coordinates. Successful lookup
support, including strict dependency and detection, is derived; absent lookups remain absent.
No chemical interpretation of the fact's label is assumed or concluded. -/
theorem snapshot_reader_eq_factAt_label
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : SingleBonded mol) (root : Nat) (valid : root < mol.atomCount)
    (ops : Operations) (sound : FramePermutationSound ops) (depth : Nat)
    (geom : Geometry) (phantom : geom mol.atomCount = none) (state : OccurrenceAuxState)
    (source : Node) (sourcePath : ReachedFrom mol root source) (mark : Nat)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (sourceCorresponds : NodeCorresponds (fun atom : input.Atom => atom.val) target.1.node source)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (query : Node)
    (queryCorresponds :
      NodeCorresponds (fun atom : input.Atom => atom.val) cursor.occurrence.1.node query) :
    rawStateReader input (underWith mol ops geom state source (facts mol ops depth) mark)
      target cursor =
      ((underWith mol ops geom state source (facts mol ops depth) mark).factAt? query).map
        factLabel := by
  have certifiedSingle := certified_simple_of_raw_single mol input agreement wellFormed unique
    supported single
  cases lookup : (underWith mol ops geom state source (facts mol ops depth) mark).factAt? query with
  | none =>
      by_cases dependency : input.LocalizedDepthDependency cursor.occurrence target
      · by_cases real : cursor.occurrence.1.node.provenance = .realAtom
        · by_cases detected :
              IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit cursor.occurrence.1).atom
          · have rawReal := (correspondence_real_iff queryCorresponds.provenance).mp real
            rw [rawStateReader_eq_factAt?_label input certifiedSingle _ target cursor dependency
              real detected query queryCorresponds.history.symm rawReal, lookup]
          · unfold rawStateReader localizedDependencyLabel rawStateView
            rw [dif_pos dependency, if_pos real, if_neg detected]
            rfl
        · rw [rawStateReader_of_not_real input _ target cursor real]
          rfl
      · rw [rawStateReader_of_not_dependency input _ target cursor dependency]
        rfl
  | some fact =>
      obtain ⟨emitter, sourceOccurrence, factOccurrence, _, _, _, sourceCorr, _, dependency,
        officialReal, detected, _, history⟩ :=
        snapshot_factAt_detected_carriers mol input agreement wellFormed unique supported single
          root valid ops sound depth geom phantom state source sourcePath mark query fact lookup
      have sourceEq : target = sourceOccurrence :=
        carrier_eq_of_mapped_history_eq input certifiedSingle target sourceOccurrence
          (sourceCorresponds.history.trans sourceCorr.history.symm)
      have queryEq : cursor.occurrence = factOccurrence :=
        carrier_eq_of_mapped_history_eq input certifiedSingle cursor.occurrence factOccurrence
          (queryCorresponds.history.trans history)
      have actualDependency : input.LocalizedDepthDependency cursor.occurrence target := by
        simpa only [sourceEq, queryEq] using dependency
      have actualReal : cursor.occurrence.1.node.provenance = .realAtom := by
        simpa only [queryEq] using officialReal
      have actualDetected :
          IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit cursor.occurrence.1).atom := by
        simpa only [queryEq] using detected
      have rawReal := (correspondence_real_iff queryCorresponds.provenance).mp actualReal
      rw [rawStateReader_eq_factAt?_label input certifiedSingle _ target cursor actualDependency
        actualReal actualDetected query queryCorresponds.history.symm rawReal, lookup]

/-- The shipped uncapped operations need no supplied permutation-shape certificate. -/
theorem uncapped_snapshot_reader_eq_factAt_label
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : SingleBonded mol) (root : Nat) (valid : root < mol.atomCount)
    (depth : Nat) (geom : Geometry) (phantom : geom mol.atomCount = none)
    (state : OccurrenceAuxState) (source : Node) (sourcePath : ReachedFrom mol root source)
    (mark : Nat)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (sourceCorresponds : NodeCorresponds (fun atom : input.Atom => atom.val) target.1.node source)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (query : Node)
    (queryCorresponds :
      NodeCorresponds (fun atom : input.Atom => atom.val) cursor.occurrence.1.node query) :
    rawStateReader input
      (underWith mol (LocalizedMarkedUncappedEvaluator.operations mol) geom state source
        (facts mol (LocalizedMarkedUncappedEvaluator.operations mol) depth) mark) target cursor =
      ((underWith mol (LocalizedMarkedUncappedEvaluator.operations mol) geom state source
        (facts mol (LocalizedMarkedUncappedEvaluator.operations mol) depth) mark).factAt? query).map
          factLabel :=
  snapshot_reader_eq_factAt_label mol input agreement wellFormed unique supported single root valid
    (LocalizedMarkedUncappedEvaluator.operations mol) (uncapped_framePermutationSound mol) depth
    geom phantom state source sourcePath mark target sourceCorresponds cursor query queryCorresponds

end TetraStereo.OneCenter.LocalizedMarkedSnapshotReaderAgreement

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedSnapshotReaderAgreement.carrier_eq_of_mapped_history_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedSnapshotReaderAgreement.snapshot_reader_eq_factAt_label
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedSnapshotReaderAgreement.uncapped_snapshot_reader_eq_factAt_label
