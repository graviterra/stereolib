import TetraStereo.OneCenter.LocalizedSpiroLigandPatternCompleteness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through6PromotedKey

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open BlueBookP93.Cyclic

/-!
# Spiro pattern classification by the actual authoritative Rules-1a--6 comparator

This module removes the abstract key-equivalence parameter from the spiro classifier.  A pair of
successfully built strengthened source-canonical keys is equivalent exactly when the production
Rules-1a--6 comparator returns `Ordering.eq`.  The remaining input is only the branch-to-key
builder itself.
-/

abbrev AuthoritativeSpiroBranchKey (input : CertifiedLocalizedCIPInput) : Type :=
  input.certified.input.AromaticCanonicalRule3Through6PromotedKey

def AuthoritativeSpiroBranchKeyEquivalent
    (input : CertifiedLocalizedCIPInput)
    (left right : input.AuthoritativeSpiroBranchKey) : Prop :=
  input.certified.input.compareAromaticCanonicalRule3Through6PromotedKeys
    left right = Ordering.eq

theorem authoritativeSpiroBranchKeyEquivalent_symmetric
    (input : CertifiedLocalizedCIPInput)
    {left right : input.AuthoritativeSpiroBranchKey} :
    input.AuthoritativeSpiroBranchKeyEquivalent left right →
      input.AuthoritativeSpiroBranchKeyEquivalent right left := by
  letI : Std.TransCmp
      input.certified.input.compareAromaticCanonicalRule3Through6PromotedKeys :=
    input.certified.input.compareAromaticCanonicalRule3Through6PromotedKeys_transCmp
  exact Std.OrientedCmp.eq_comm.mp

/-- Simple-spiro ligand-pattern classifier with the authoritative strengthened comparator fixed. -/
noncomputable def localizedSpiroLigandPatternFromAuthoritativeKeys?
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (key? : input.Atom → Option input.AuthoritativeSpiroBranchKey) :
    Option SpiroLigandPattern :=
  input.localizedSpiroLigandPatternFromKeys? center carrier key?
    input.AuthoritativeSpiroBranchKeyEquivalent

theorem localizedSpiroLigandPatternFromAuthoritativeKeys?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedSpiroCenter center carrier)
    (key? : input.Atom → Option input.AuthoritativeSpiroBranchKey)
    (pattern : SpiroLigandPattern) :
    input.localizedSpiroLigandPatternFromAuthoritativeKeys? center carrier key? = some pattern ↔
      input.LocalizedSpiroBranchKeysResolved center carrier key? ∧
        input.DeclarativeLocalizedSpiroLigandPattern center carrier
          (SpiroOccurrencePattern.SameResolvedKey key?
            input.AuthoritativeSpiroBranchKeyEquivalent) pattern := by
  exact input.localizedSpiroLigandPatternFromKeys?_eq_some_iff center carrier topology key?
    input.AuthoritativeSpiroBranchKeyEquivalent
    input.authoritativeSpiroBranchKeyEquivalent_symmetric pattern

theorem localizedSpiroLigandPatternFromAuthoritativeKeys?_eq_none_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedSpiroCenter center carrier)
    (key? : input.Atom → Option input.AuthoritativeSpiroBranchKey) :
    input.localizedSpiroLigandPatternFromAuthoritativeKeys? center carrier key? = none ↔
      ¬input.LocalizedSpiroBranchKeysResolved center carrier key? ∨
        ∀ pattern, ¬input.DeclarativeLocalizedSpiroLigandPattern center carrier
          (SpiroOccurrencePattern.SameResolvedKey key?
            input.AuthoritativeSpiroBranchKeyEquivalent) pattern := by
  exact input.localizedSpiroLigandPatternFromKeys?_eq_none_iff center carrier topology key?
    input.AuthoritativeSpiroBranchKeyEquivalent
    input.authoritativeSpiroBranchKeyEquivalent_symmetric

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
