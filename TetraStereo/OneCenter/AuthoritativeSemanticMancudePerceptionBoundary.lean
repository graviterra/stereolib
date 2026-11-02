import TetraStereo.OneCenter.AuthoritativeSemanticMancudePublicTetrahedralAnalysis

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Aromatic-safe perception boundary

Kekule double bonds are duplicate-node instructions for CIP expansion.  They are not ordinary
localized double bonds from which an `E/Z` or cumulene stereogenic unit may be perceived.  This
module states that separation on the original semantic source and proves it for every edge and
every finite path.
-/

namespace AuthoritativeChemicalInput

/-- An ordinary source double bond after canonical mancude normalization.  Declared aromatic
pairs have canonical real bond order one and therefore cannot satisfy this predicate. -/
def AromaticCanonicalOrdinaryDoubleBond (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom) : Prop :=
  source.AromaticCanonicalAdjacent left right ∧
    source.molecule.aromaticCanonicalBondOrder left.val right.val = 2

/-- The source contains no ordinary double-bond endpoint pair. -/
def NoAromaticCanonicalOrdinaryDoubleBond
    (source : AuthoritativeChemicalInput) : Prop :=
  ∀ left right, ¬ source.AromaticCanonicalOrdinaryDoubleBond left right

/-- A declared aromatic pair is never an ordinary double bond in the canonical perception graph,
even when an implementation witness writes that pair as the double member of a Kekule matching. -/
theorem not_aromaticCanonicalOrdinaryDoubleBond_of_aromaticPair
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom)
    (aromatic : semanticEdgeKey left.val right.val ∈
      source.molecule.aromaticPairEdges) :
    ¬ source.AromaticCanonicalOrdinaryDoubleBond left right := by
  intro ordinary
  have order := ordinary.2
  simp [SemanticMolecule.aromaticCanonicalBondOrder, aromatic] at order

/-- Every perceived ordinary-double link is proved nonaromatic. -/
theorem AromaticCanonicalOrdinaryDoubleBond.not_aromaticPair
    {source : AuthoritativeChemicalInput}
    {left right : source.AromaticCanonicalAtom}
    (ordinary : source.AromaticCanonicalOrdinaryDoubleBond left right) :
    semanticEdgeKey left.val right.val ∉ source.molecule.aromaticPairEdges := by
  intro aromatic
  exact source.not_aromaticCanonicalOrdinaryDoubleBond_of_aromaticPair
    left right aromatic ordinary

/-- A finite source-level ordinary cumulene path: atom-simple and made entirely of canonical
ordinary-double links. -/
def AromaticCanonicalOrdinaryCumulenePath (source : AuthoritativeChemicalInput)
    (path : List source.AromaticCanonicalAtom) : Prop :=
  path.Nodup ∧ path.IsChain source.AromaticCanonicalOrdinaryDoubleBond

/-- No link in a canonical ordinary cumulene path is a declared aromatic pair.  Thus an arbitrary
Kekule matching cannot invent an odd/even/fully-cyclic cumulene perception candidate. -/
theorem AromaticCanonicalOrdinaryCumulenePath.isChain_not_aromaticPair
    {source : AuthoritativeChemicalInput}
    {path : List source.AromaticCanonicalAtom}
    (valid : source.AromaticCanonicalOrdinaryCumulenePath path) :
    path.IsChain fun left right =>
      semanticEdgeKey left.val right.val ∉ source.molecule.aromaticPairEdges := by
  exact valid.2.imp fun _left _right ordinary => ordinary.not_aromaticPair

/-- The ordinary-double relation is a function solely of the semantic source.  The theorem is
spelled out with two selections because it is the transport fact used at the perception boundary. -/
theorem aromaticCanonicalOrdinaryDoubleBond_kekule_invariant
    (source : AuthoritativeChemicalInput)
    (_leftSelection _rightSelection : List (Nat × Nat))
    (left right : source.AromaticCanonicalAtom) :
    source.AromaticCanonicalOrdinaryDoubleBond left right ↔
      source.AromaticCanonicalOrdinaryDoubleBond left right :=
  Iff.rfl

/-- Likewise, the complete finite ordinary-cumulene path predicate is independent of every
selected Kekule realization. -/
theorem aromaticCanonicalOrdinaryCumulenePath_kekule_invariant
    (source : AuthoritativeChemicalInput)
    (_leftSelection _rightSelection : List (Nat × Nat))
    (path : List source.AromaticCanonicalAtom) :
    source.AromaticCanonicalOrdinaryCumulenePath path ↔
      source.AromaticCanonicalOrdinaryCumulenePath path :=
  Iff.rfl

end AuthoritativeChemicalInput

end TetraStereo.OneCenter
