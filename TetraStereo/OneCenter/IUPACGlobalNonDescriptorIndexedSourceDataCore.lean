import TetraStereo.OneCenter.IUPACGlobalNonDescriptorSourceMeaningEntryConstructors
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorSourceMeaningReadiness

set_option autoImplicit false

/-!
# Shared indexed source-data construction and glycolipid tables

This small foundation module owns the uniform total-source-function constructor and the nineteen
one-to-one glycolipid table rows.  Larger carbohydrate batches import it without re-elaborating
each other's row inventories.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorIndexedSourceData

open GlobalNonDescriptorSourceMeaningConstructor

private theorem parameterized_mem_globalNonDescriptor
    (provision : IUPACNormativeProvision)
    (parameterized : isParameterizedProvision provision = true) :
    provision ∈ globalNonDescriptorProvisions := by
  apply (mem_globalNonDescriptorProvisions_iff provision).2
  intro bearing
  have classifier :=
    descriptorAssignmentBearing?_eq_false_of_parameterizedShape provision parameterized
  simp [DescriptorAssignmentBearing, classifier] at bearing

/-- Package an already-total declarative source function.  The reported result is constrained by
that function, not by manifest membership, the provision tag, or its source key. -/
def totalMeaningBatch {Row Result : Type}
    (rows : List Row)
    (wrap : Row → IUPACNormativeProvision)
    (meaning : Row → Result)
    (parameterized : ∀ row, isParameterizedProvision (wrap row) = true) :
    GlobalNonDescriptorSourceMeaningBatch (rows.map wrap) where
  entries := rows.map fun row => rowResultEntry (wrap row) row meaning
  provisions_exact := by
    simp [rowResultEntry, relationalEntry]
  scope := by
    intro provision member
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp member
    exact parameterized_mem_globalNonDescriptor (wrap row) (parameterized row)

structure GlycolipidRootMeaning where
  structureCode : String
  symbol : String
  deriving DecidableEq, Repr

def glycolipidRootMeaning (row : Glycolipid1997.RootGlycan) : GlycolipidRootMeaning :=
  ⟨row.structureCode, row.symbol⟩

structure GlycolipidSvennerholmMeaning where
  structureCode : String
  abbreviation : String
  deriving DecidableEq, Repr

def glycolipidSvennerholmMeaning
    (row : Glycolipid1997.SvennerholmEntry) : GlycolipidSvennerholmMeaning :=
  ⟨row.structureCode, row.abbreviation⟩

def glycolipidRows : List Glycolipid1997.Provision :=
  Glycolipid1997.RootGlycan.all.map Glycolipid1997.Provision.rootStructure ++
    Glycolipid1997.SvennerholmEntry.all.map Glycolipid1997.Provision.svennerholmStructure

def glycolipidProvisions : List IUPACNormativeProvision :=
  glycolipidRows.map IUPACNormativeProvision.glycolipid1997

private def glycolipidRootBatch :=
  totalMeaningBatch Glycolipid1997.RootGlycan.all
    (fun row => IUPACNormativeProvision.glycolipid1997 (.rootStructure row))
    glycolipidRootMeaning (by intro _row; rfl)

private def glycolipidSvennerholmBatch :=
  totalMeaningBatch Glycolipid1997.SvennerholmEntry.all
    (fun row => IUPACNormativeProvision.glycolipid1997 (.svennerholmStructure row))
    glycolipidSvennerholmMeaning (by intro _row; rfl)

def glycolipidBatch : GlobalNonDescriptorSourceMeaningBatch glycolipidProvisions := by
  simpa [glycolipidProvisions, glycolipidRows, List.map_append, List.map_map] using
    glycolipidRootBatch.append glycolipidSvennerholmBatch

@[simp] theorem glycolipidProvisionCount : glycolipidProvisions.length = 19 := by
  simp [glycolipidProvisions, glycolipidRows]

private theorem glycolipidRows_nodup : glycolipidRows.Nodup := by
  have allNodup := Glycolipid1997.Provision.all_nodup
  have baseAppend : (Glycolipid1997.Provision.base ++ glycolipidRows).Nodup := by
    simpa [Glycolipid1997.Provision.all, glycolipidRows, List.append_assoc] using allNodup
  exact baseAppend.of_append_right

theorem glycolipidProvisions_nodup : glycolipidProvisions.Nodup := by
  exact glycolipidRows_nodup.map (by intro left right equal; cases equal; rfl)

end GlobalNonDescriptorIndexedSourceData
end IUPACNormativeProvision
end TetraStereo.OneCenter
