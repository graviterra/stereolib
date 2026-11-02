import TetraStereo.OneCenter.StereochemicalElements

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace CIPOfficialRules

open OneCenter

noncomputable section

/-- A deliberately tied graph key, used to force the official descriptor-rich rules to fire. -/
def tiedKey : List MoleculeGraph.AtomLabel :=
  []

/-- Rule 3 is now in the executable proof trace: `Z/seqcis` outranks `E/seqtrans`
after ordinary graph keys tie. -/
theorem rule3_Z_over_E_after_key_tie :
    (CIPRuleEngine.compareKeyThenOfficialCertificate tiedKey tiedKey
      AlkeneEZ.Z.toOfficialLigandRuleContext
      AlkeneEZ.E.toOfficialLigandRuleContext).outcome = Ordering.gt := by
  simp [tiedKey, CIPRuleEngine.compareKeyThenOfficialCertificate,
    CIPRuleEngine.compareKeyThenOfficialTrace]

/-- Rule 4a is now in the executable proof trace: chiral units outrank pseudoasymmetric units
after ordinary graph keys tie. -/
theorem rule4a_chiral_over_pseudoasymmetric_after_key_tie :
    (CIPRuleEngine.compareKeyThenOfficialCertificate tiedKey tiedKey
      (CIPRuleEngine.OfficialLigandRuleContext.ofRule4aKind
        OfficialStereogenicUnitKind.chiral)
      (CIPRuleEngine.OfficialLigandRuleContext.ofRule4aKind
        OfficialStereogenicUnitKind.pseudoasymmetric)).outcome = Ordering.gt := by
  simp [tiedKey, CIPRuleEngine.compareKeyThenOfficialCertificate,
    CIPRuleEngine.compareKeyThenOfficialTrace]

/-- Rule 4b is now in the executable proof trace: like descriptor pairs outrank unlike pairs
after ordinary graph keys tie. -/
theorem rule4b_like_over_unlike_after_key_tie :
    (CIPRuleEngine.compareKeyThenOfficialCertificate tiedKey tiedKey
      (CIPRuleEngine.OfficialLigandRuleContext.ofRule4bPair OfficialDescriptorPairKind.like)
      (CIPRuleEngine.OfficialLigandRuleContext.ofRule4bPair OfficialDescriptorPairKind.unlike)).outcome =
      Ordering.gt := by
  simp [tiedKey, CIPRuleEngine.compareKeyThenOfficialCertificate,
    CIPRuleEngine.compareKeyThenOfficialTrace]

/-- Rule 4c is now in the executable proof trace: lowercase `r` outranks lowercase `s`
after ordinary graph keys tie. -/
theorem rule4c_r_over_s_after_key_tie :
    (CIPRuleEngine.compareKeyThenOfficialCertificate tiedKey tiedKey
      (CIPRuleEngine.OfficialLigandRuleContext.ofRule4cDescriptor
        OfficialPseudoasymmetricDescriptor.r)
      (CIPRuleEngine.OfficialLigandRuleContext.ofRule4cDescriptor
        OfficialPseudoasymmetricDescriptor.s)).outcome = Ordering.gt := by
  simp [tiedKey, CIPRuleEngine.compareKeyThenOfficialCertificate,
    CIPRuleEngine.compareKeyThenOfficialTrace]

/-- The Rule-5 helical bridge is also connected: `M` outranks `P` after ordinary graph keys tie. -/
theorem rule5_helical_M_over_P_after_key_tie :
    (CIPRuleEngine.compareKeyThenOfficialCertificate tiedKey tiedKey
      HelicalDescriptor.M.toOfficialLigandRuleContext
      HelicalDescriptor.P.toOfficialLigandRuleContext).outcome = Ordering.gt := by
  simp [tiedKey, CIPRuleEngine.compareKeyThenOfficialCertificate,
    CIPRuleEngine.compareKeyThenOfficialTrace]

end
end CIPOfficialRules
end Examples
end TetraStereo
