import TetraStereo.OneCenter.CertificateExport
import TetraStereo.OneCenter.OfficialCIPEngine
import TetraStereo.OneCenter.CIPRules
import TetraStereo.OneCenter.RS

set_option autoImplicit false

namespace TetraStereo
namespace Engine

open OneCenter

noncomputable section

/-!
  Public engine API.

  This module is a deliberate facade over the research proof kernel.  The kernel contains raw,
  deterministic orders and permutations because those are useful for proofs and executable
  normalization.  The public engine surface below does **not** expose those raw choices as
  stereochemical classifications.  Public results are tied to safe optional APIs and therefore
  certify that a successful descriptor came from resolved priorities rather than from an index
  tie-breaker.
-/

/-- Public descriptor-priority result for one-center descriptor-CIP.

Both fields are safe optional outputs.  There is intentionally no raw deterministic `order` or
`permutation` field here. -/
structure DescriptorPriorityResult {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V) where
  order? : Option (List (Fin 4))
  permutation? : Option (Equiv.Perm (Fin 4))
  safeOrder : order? = m.cipOrderDescriptor?
  safePermutation : permutation? = m.cipPermutationDescriptor?

/-- Public official-priority result for one-center official CIP. -/
structure OfficialPriorityResult {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) where
  order? : Option (List (Fin 4))
  permutation? : Option (Equiv.Perm (Fin 4))
  safeOrder : order? = m.cipOfficialOrder? context
  safePermutation : permutation? = m.cipOfficialPermutation? context

/-- Certified descriptor-CIP `R/S` assignment.

The proof field is the firewall: a successful public assignment is definitionally a theorem that
the safe descriptor-facing API returned `some descriptor`. -/
structure CertifiedRSAssignment {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) where
  descriptor : RS
  certificate : m.rsCIP? g = some descriptor

/-- Certified official-CIP `R/S` assignment. -/
structure CertifiedOfficialRSAssignment {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (g : TetrahedralGeometry.Realization) where
  descriptor : RS
  certificate : m.rsOfficial? context g = some descriptor

/-- Public descriptor-CIP `R/S` result.

The only descriptor payload is optional and linked by proof to `rsCIP?`; unresolved ties therefore
remain `none` at the public boundary. -/
structure RSResult {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) where
  descriptor? : Option RS
  safeAssignment : descriptor? = m.rsCIP? g

/-- Public official-CIP `R/S` result. -/
structure OfficialRSResult {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (g : TetrahedralGeometry.Realization) where
  descriptor? : Option RS
  safeAssignment : descriptor? = m.rsOfficial? context g

namespace DescriptorPriorityResult

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : OneCenterMolecule V}

/-- If the public descriptor permutation succeeds, descriptor priorities were resolved. -/
theorem resolved_of_permutation_some (result : DescriptorPriorityResult m)
    {permutation : Equiv.Perm (Fin 4)}
    (h : result.permutation? = some permutation) :
    m.ResolvedCIPDescriptor := by
  have hsomeResult : result.permutation?.isSome = true := by
    simp [h]
  have hsomeSafe : m.cipPermutationDescriptor?.isSome = true := by
    rw [← result.safePermutation]
    exact hsomeResult
  exact
    (m.cipPermutationCycleCut?_isSome_iff_resolvedCIPCycleCut).1
      (by simpa [OneCenterMolecule.cipPermutationDescriptor?] using hsomeSafe)

end DescriptorPriorityResult

namespace OfficialPriorityResult

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : OneCenterMolecule V}
variable {context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext}

/-- If the public official permutation succeeds, official priorities were resolved. -/
theorem resolved_of_permutation_some (result : OfficialPriorityResult m context)
    {permutation : Equiv.Perm (Fin 4)}
    (h : result.permutation? = some permutation) :
    m.ResolvedOfficialCIP context := by
  have hsomeResult : result.permutation?.isSome = true := by
    simp [h]
  have hsomeSafe : (m.cipOfficialPermutation? context).isSome = true := by
    rw [← result.safePermutation]
    exact hsomeResult
  exact (m.cipOfficialPermutation?_isSome_iff_resolved context).1 hsomeSafe

end OfficialPriorityResult

namespace CertifiedRSAssignment

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : OneCenterMolecule V}
variable {g : TetrahedralGeometry.Realization}

/-- A certified public descriptor assignment implies resolved descriptor priorities. -/
theorem resolved (assignment : CertifiedRSAssignment m g) :
    m.ResolvedCIPDescriptor := by
  classical
  by_cases h : m.ResolvedCIPDescriptor
  · exact h
  · have hnone : m.rsCIP? g = none := by
      simp [OneCenterMolecule.rsCIP?, OneCenterMolecule.rsCycleCut?, h]
    rw [assignment.certificate] at hnone
    contradiction

/-- Convert a public assignment into the existing theorem-artifact export format. -/
def toCertificateArtifact (assignment : CertifiedRSAssignment m g)
    (theoremName computedExpr expectedExpr proofTerm : String) : LeanCertificateArtifact :=
  compileRSAssignmentCertificate theoremName computedExpr expectedExpr proofTerm
    (m.rsCIP? g) assignment.descriptor assignment.certificate

end CertifiedRSAssignment

namespace CertifiedOfficialRSAssignment

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : OneCenterMolecule V}
variable {context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext}
variable {g : TetrahedralGeometry.Realization}

/-- A certified public official assignment implies resolved official priorities. -/
theorem resolved (assignment : CertifiedOfficialRSAssignment m context g) :
    m.ResolvedOfficialCIP context := by
  classical
  by_cases h : m.ResolvedOfficialCIP context
  · exact h
  · have hnone : m.rsOfficial? context g = none := by
      simp [OneCenterMolecule.rsOfficial?, h]
    rw [assignment.certificate] at hnone
    contradiction

/-- Convert a public official assignment into the existing theorem-artifact export format. -/
def toCertificateArtifact (assignment : CertifiedOfficialRSAssignment m context g)
    (theoremName computedExpr expectedExpr proofTerm : String) : LeanCertificateArtifact :=
  compileRSAssignmentCertificate theoremName computedExpr expectedExpr proofTerm
    (m.rsOfficial? context g) assignment.descriptor assignment.certificate

end CertifiedOfficialRSAssignment

namespace RSResult

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : OneCenterMolecule V}
variable {g : TetrahedralGeometry.Realization}

/-- Extract a certificate when the public descriptor result succeeded. -/
def certified? (result : RSResult m g) : Option (CertifiedRSAssignment m g) :=
  match h : result.descriptor? with
  | some descriptor =>
      some
        { descriptor := descriptor
          certificate := by
            rw [← result.safeAssignment]
            exact h }
  | none => none

/-- A `some` public descriptor is exactly a safe descriptor-CIP success. -/
theorem safe_some (result : RSResult m g) {descriptor : RS}
    (h : result.descriptor? = some descriptor) :
    m.rsCIP? g = some descriptor := by
  rw [← result.safeAssignment]
  exact h

/-- If the public descriptor result succeeds, descriptor priorities were resolved. -/
theorem resolved_of_some (result : RSResult m g) {descriptor : RS}
    (h : result.descriptor? = some descriptor) :
    m.ResolvedCIPDescriptor :=
  (CertifiedRSAssignment.resolved
    { descriptor := descriptor
      certificate := result.safe_some h })

end RSResult

namespace OfficialRSResult

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : OneCenterMolecule V}
variable {context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext}
variable {g : TetrahedralGeometry.Realization}

/-- Extract a certificate when the public official result succeeded. -/
def certified? (result : OfficialRSResult m context g) :
    Option (CertifiedOfficialRSAssignment m context g) :=
  match h : result.descriptor? with
  | some descriptor =>
      some
        { descriptor := descriptor
          certificate := by
            rw [← result.safeAssignment]
            exact h }
  | none => none

/-- A `some` public official descriptor is exactly a safe official-CIP success. -/
theorem safe_some (result : OfficialRSResult m context g) {descriptor : RS}
    (h : result.descriptor? = some descriptor) :
    m.rsOfficial? context g = some descriptor := by
  rw [← result.safeAssignment]
  exact h

/-- If the public official descriptor result succeeds, official priorities were resolved. -/
theorem resolved_of_some (result : OfficialRSResult m context g) {descriptor : RS}
    (h : result.descriptor? = some descriptor) :
    m.ResolvedOfficialCIP context :=
  (CertifiedOfficialRSAssignment.resolved
    { descriptor := descriptor
      certificate := result.safe_some h })

end OfficialRSResult

/-- Public descriptor-CIP priority engine. -/
def descriptorPriority {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V) : DescriptorPriorityResult m where
  order? := m.cipOrderDescriptor?
  permutation? := m.cipPermutationDescriptor?
  safeOrder := rfl
  safePermutation := rfl

/-- Public official-CIP priority engine. -/
def officialPriority {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    OfficialPriorityResult m context where
  order? := m.cipOfficialOrder? context
  permutation? := m.cipOfficialPermutation? context
  safeOrder := rfl
  safePermutation := rfl

/-- Public descriptor-CIP `R/S` engine. -/
def descriptorRS {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) : RSResult m g where
  descriptor? := m.rsCIP? g
  safeAssignment := rfl

/-- Public official-CIP `R/S` engine. -/
def officialRS {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (g : TetrahedralGeometry.Realization) :
    OfficialRSResult m context g where
  descriptor? := m.rsOfficial? context g
  safeAssignment := rfl

/-- Public descriptor-CIP `R/S` certificate extraction. -/
def descriptorRSCertificate? {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) :
    Option (CertifiedRSAssignment m g) :=
  (descriptorRS m g).certified?

/-- Public official-CIP `R/S` certificate extraction. -/
def officialRSCertificate? {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (g : TetrahedralGeometry.Realization) :
    Option (CertifiedOfficialRSAssignment m context g) :=
  (officialRS m context g).certified?

end
end Engine
end TetraStereo
