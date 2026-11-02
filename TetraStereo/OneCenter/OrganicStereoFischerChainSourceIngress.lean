import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoFragmentSourceData
import TetraStereo.OneCenter.OrganicStereoResidueLinkAnnotations
import TetraStereo.OneCenter.OrganicStereoSourceDataResidueAssembly
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter

/-!
# Exact ingress of the 1996 Fischer-chain projection record

The five 2-Carb-2 image meanings in
`IUPACGlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings` carry the actual
`Carbohydrate1996ImageAudit.FischerProjection` record.  That record is a whole chain: a carbon
count, an optional carbonyl locant, an ordered (and possibly duplicated) list of
`FischerSubstituent` entries (printed locant, oxygen group, horizontal side), and a
`hydroxymethylTermini` flag.  The single-centre `FragmentSourceDatum.aminoFischer` and
`lipidFischer` constructors do not retain that whole record.

The low-level `OrganicStereoFragmentSourceData` module therefore carries an independent closed
structural copy, `CarbohydrateFischerChainData`, and one new constructor
`carbohydrateFischerChain (carbons : List V) (projection : CarbohydrateFischerChainData)`.  This
leaf imports the **actual** source module and closes the typed record ingress:

* fieldwise total maps in both directions between the closed carrier and the actual
  `FischerProjection` / `FischerSubstituent` / `FischerOxygenSubstituent` /
  `FischerHorizontalSide` records, with round trips, injectivity, bijectivity and an `Equiv`;
* exact recovery of every field, including `carbonylLocant? = none` and `= some locant`, the
  ordered substituent list (order and duplicates retained), the carbon count, all three oxygen
  groups, both sides, and both flag values.  There is no string or sum erasure;
* an actual physical binding against a real `ResidueIncidenceLedger Nat input`: the ordered carbon
  anchors have length `projection.carbonCount` and the `i`-th carbon resolves source locant
  `i + 1` in the actual residue.  Anchor support membership is *derived* from that resolution;
* substituent and carbonyl index bounds derived from the actual source
  `FischerProjection.wellFormed = true` premise, not assumed as output;
* `withSourceData` / `encodeWithSourceData` annotation builders and exact source readback from
  the suffix actually emitted into a residue's `sourceData`, together with preservation of the old
  source-data prefix, support, bindings, links and naming hierarchy.

No descriptor, geometry or chemistry is inferred from a name.  The module transports the supplied
record and maps its carbon anchors through actual ledger incidence only.
-/

namespace CarbohydrateFischerChainIngress

/-- The actual source horizontal-side record. -/
abbrev SourceHorizontalSide := Carbohydrate1996ImageAudit.FischerHorizontalSide

/-- The actual source oxygen-substituent record. -/
abbrev SourceOxygenSubstituent := Carbohydrate1996ImageAudit.FischerOxygenSubstituent

/-- The actual source substituent record. -/
abbrev SourceSubstituent := Carbohydrate1996ImageAudit.FischerSubstituent

/-- The actual source complete Fischer-chain projection. -/
abbrev SourceProjection := Carbohydrate1996ImageAudit.FischerProjection

/-! ## Fieldwise total maps and exact round trips -/

/-- The closed carrier side maps to the actual source side. -/
def sideToSource : CarbohydrateFischerHorizontalSide → SourceHorizontalSide
  | .left => .left
  | .right => .right

/-- The actual source side maps back to the closed carrier side. -/
def sideFromSource : SourceHorizontalSide → CarbohydrateFischerHorizontalSide
  | .left => .left
  | .right => .right

@[simp] theorem sideToSource_left : sideToSource .left = .left := rfl
@[simp] theorem sideToSource_right : sideToSource .right = .right := rfl
@[simp] theorem sideFromSource_left : sideFromSource .left = .left := rfl
@[simp] theorem sideFromSource_right : sideFromSource .right = .right := rfl

/-- Both side values round-trip exactly. -/
@[simp] theorem sideFromSource_toSource (side : CarbohydrateFischerHorizontalSide) :
    sideFromSource (sideToSource side) = side := by
  cases side <;> rfl

/-- Both source side values round-trip exactly. -/
@[simp] theorem sideToSource_fromSource (side : SourceHorizontalSide) :
    sideToSource (sideFromSource side) = side := by
  cases side <;> rfl

/-- The closed carrier oxygen group maps to the actual source oxygen group. -/
def oxygenToSource :
    CarbohydrateFischerOxygenSubstituent → SourceOxygenSubstituent
  | .hydroxy => .hydroxy
  | .methoxy => .methoxy
  | .acetoxy => .acetoxy

/-- The actual source oxygen group maps back to the closed carrier oxygen group. -/
def oxygenFromSource :
    SourceOxygenSubstituent → CarbohydrateFischerOxygenSubstituent
  | .hydroxy => .hydroxy
  | .methoxy => .methoxy
  | .acetoxy => .acetoxy

@[simp] theorem oxygenToSource_hydroxy : oxygenToSource .hydroxy = .hydroxy := rfl
@[simp] theorem oxygenToSource_methoxy : oxygenToSource .methoxy = .methoxy := rfl
@[simp] theorem oxygenToSource_acetoxy : oxygenToSource .acetoxy = .acetoxy := rfl
@[simp] theorem oxygenFromSource_hydroxy : oxygenFromSource .hydroxy = .hydroxy := rfl
@[simp] theorem oxygenFromSource_methoxy : oxygenFromSource .methoxy = .methoxy := rfl
@[simp] theorem oxygenFromSource_acetoxy : oxygenFromSource .acetoxy = .acetoxy := rfl

/-- All three oxygen groups round-trip exactly: `hydroxy`, `methoxy` and `acetoxy` are not
identified or erased. -/
@[simp] theorem oxygenFromSource_toSource
    (oxygenGroup : CarbohydrateFischerOxygenSubstituent) :
    oxygenFromSource (oxygenToSource oxygenGroup) = oxygenGroup := by
  cases oxygenGroup <;> rfl

/-- All three actual source oxygen groups round-trip exactly. -/
@[simp] theorem oxygenToSource_fromSource
    (oxygenGroup : SourceOxygenSubstituent) :
    oxygenToSource (oxygenFromSource oxygenGroup) = oxygenGroup := by
  cases oxygenGroup <;> rfl

/-- The closed carrier substituent maps fieldwise to the actual source substituent. -/
def substituentToSource
    (substituent : CarbohydrateFischerSubstituent) : SourceSubstituent where
  locant := substituent.locant
  oxygenGroup := oxygenToSource substituent.oxygenGroup
  horizontalSide := sideToSource substituent.horizontalSide

/-- The actual source substituent maps fieldwise to the closed carrier substituent. -/
def substituentFromSource
    (substituent : SourceSubstituent) : CarbohydrateFischerSubstituent where
  locant := substituent.locant
  oxygenGroup := oxygenFromSource substituent.oxygenGroup
  horizontalSide := sideFromSource substituent.horizontalSide

@[simp] theorem substituentToSource_locant
    (substituent : CarbohydrateFischerSubstituent) :
    (substituentToSource substituent).locant = substituent.locant := rfl

@[simp] theorem substituentToSource_oxygenGroup
    (substituent : CarbohydrateFischerSubstituent) :
    (substituentToSource substituent).oxygenGroup =
      oxygenToSource substituent.oxygenGroup := rfl

@[simp] theorem substituentToSource_horizontalSide
    (substituent : CarbohydrateFischerSubstituent) :
    (substituentToSource substituent).horizontalSide =
      sideToSource substituent.horizontalSide := rfl

@[simp] theorem substituentFromSource_locant
    (substituent : SourceSubstituent) :
    (substituentFromSource substituent).locant = substituent.locant := rfl

@[simp] theorem substituentFromSource_oxygenGroup
    (substituent : SourceSubstituent) :
    (substituentFromSource substituent).oxygenGroup =
      oxygenFromSource substituent.oxygenGroup := rfl

@[simp] theorem substituentFromSource_horizontalSide
    (substituent : SourceSubstituent) :
    (substituentFromSource substituent).horizontalSide =
      sideFromSource substituent.horizontalSide := rfl

/-- Substituent round trip: locant, oxygen group and side are all recovered. -/
@[simp] theorem substituentFromSource_toSource
    (substituent : CarbohydrateFischerSubstituent) :
    substituentFromSource (substituentToSource substituent) = substituent := by
  cases substituent with
  | mk locant oxygenGroup horizontalSide =>
      simp [substituentFromSource, substituentToSource]

/-- Source-substituent round trip: locant, oxygen group and side are all recovered. -/
@[simp] theorem substituentToSource_fromSource
    (substituent : SourceSubstituent) :
    substituentToSource (substituentFromSource substituent) = substituent := by
  cases substituent with
  | mk locant oxygenGroup horizontalSide =>
      simp [substituentToSource, substituentFromSource]

/-- The closed carrier complete chain record maps fieldwise to the actual source projection.
The substituent list is mapped positionally, so order, multiplicity and duplicates are retained. -/
def projectionToSource
    (projection : CarbohydrateFischerChainData) : SourceProjection where
  carbonCount := projection.carbonCount
  carbonylLocant? := projection.carbonylLocant?
  substituents := projection.substituents.map substituentToSource
  hydroxymethylTermini := projection.hydroxymethylTermini

/-- The actual source projection maps fieldwise back to the closed carrier record. -/
def projectionFromSource
    (projection : SourceProjection) : CarbohydrateFischerChainData where
  carbonCount := projection.carbonCount
  carbonylLocant? := projection.carbonylLocant?
  substituents := projection.substituents.map substituentFromSource
  hydroxymethylTermini := projection.hydroxymethylTermini

@[simp] theorem projectionToSource_carbonCount
    (projection : CarbohydrateFischerChainData) :
    (projectionToSource projection).carbonCount = projection.carbonCount := rfl

@[simp] theorem projectionToSource_carbonylLocant?
    (projection : CarbohydrateFischerChainData) :
    (projectionToSource projection).carbonylLocant? = projection.carbonylLocant? := rfl

@[simp] theorem projectionToSource_substituents
    (projection : CarbohydrateFischerChainData) :
    (projectionToSource projection).substituents =
      projection.substituents.map substituentToSource := rfl

@[simp] theorem projectionToSource_hydroxymethylTermini
    (projection : CarbohydrateFischerChainData) :
    (projectionToSource projection).hydroxymethylTermini =
      projection.hydroxymethylTermini := rfl

@[simp] theorem projectionFromSource_carbonCount
    (projection : SourceProjection) :
    (projectionFromSource projection).carbonCount = projection.carbonCount := rfl

@[simp] theorem projectionFromSource_carbonylLocant?
    (projection : SourceProjection) :
    (projectionFromSource projection).carbonylLocant? = projection.carbonylLocant? := rfl

@[simp] theorem projectionFromSource_substituents
    (projection : SourceProjection) :
    (projectionFromSource projection).substituents =
      projection.substituents.map substituentFromSource := rfl

@[simp] theorem projectionFromSource_hydroxymethylTermini
    (projection : SourceProjection) :
    (projectionFromSource projection).hydroxymethylTermini =
      projection.hydroxymethylTermini := rfl

/-- Projection round trip: an actual source projection is recovered field for field, including
the optional carbonyl locant and the ordered substituent list. -/
@[simp] theorem projectionToSource_fromSource (projection : SourceProjection) :
    projectionToSource (projectionFromSource projection) = projection := by
  cases projection with
  | mk carbonCount carbonylLocant? substituents hydroxymethylTermini =>
      simp [projectionToSource, projectionFromSource, List.map_map, Function.comp_def,
        substituentToSource_fromSource]

/-- Projection round trip in the other direction. -/
@[simp] theorem projectionFromSource_toSource
    (projection : CarbohydrateFischerChainData) :
    projectionFromSource (projectionToSource projection) = projection := by
  cases projection with
  | mk carbonCount carbonylLocant? substituents hydroxymethylTermini =>
      simp [projectionToSource, projectionFromSource, List.map_map, Function.comp_def,
        substituentFromSource_toSource]

/-! ### Optional absence and presence -/

/-- An absent carbonyl locant stays absent. -/
@[simp] theorem projectionToSource_carbonyl_none
    (projection : CarbohydrateFischerChainData)
    (absent : projection.carbonylLocant? = none) :
    (projectionToSource projection).carbonylLocant? = none := by
  rw [projectionToSource_carbonylLocant?, absent]

/-- A present carbonyl locant stays the same present locant. -/
@[simp] theorem projectionToSource_carbonyl_some
    (projection : CarbohydrateFischerChainData) {locant : Nat}
    (present : projection.carbonylLocant? = some locant) :
    (projectionToSource projection).carbonylLocant? = some locant := by
  rw [projectionToSource_carbonylLocant?, present]

/-- Absence is recovered from the actual source projection as absence. -/
@[simp] theorem projectionFromSource_carbonyl_none
    (projection : SourceProjection)
    (absent : projection.carbonylLocant? = none) :
    (projectionFromSource projection).carbonylLocant? = none := by
  rw [projectionFromSource_carbonylLocant?, absent]

/-- Presence is recovered from the actual source projection as the same present locant. -/
@[simp] theorem projectionFromSource_carbonyl_some
    (projection : SourceProjection) {locant : Nat}
    (present : projection.carbonylLocant? = some locant) :
    (projectionFromSource projection).carbonylLocant? = some locant := by
  rw [projectionFromSource_carbonylLocant?, present]

/-! ### Ordered substituent list is retained exactly -/

/-- Mapping the recovered source substituents back gives the original source list.  The `map` is
positional, so order, length and duplicate entries are retained exactly. -/
theorem projectionFromSource_substituents_map (projection : SourceProjection) :
    (projectionFromSource projection).substituents.map substituentToSource =
      projection.substituents := by
  simpa [projectionToSource] using
    congrArg Carbohydrate1996ImageAudit.FischerProjection.substituents
      (projectionToSource_fromSource projection)

/-- Mapping the recovered carrier substituents back gives the original carrier list. -/
theorem projectionToSource_substituents_map (projection : CarbohydrateFischerChainData) :
    (projectionToSource projection).substituents.map substituentFromSource =
      projection.substituents := by
  simpa [projectionFromSource] using
    congrArg CarbohydrateFischerChainData.substituents
      (projectionFromSource_toSource projection)

@[simp] theorem projectionFromSource_substituents_length (projection : SourceProjection) :
    (projectionFromSource projection).substituents.length =
      projection.substituents.length := by
  rw [projectionFromSource_substituents, List.length_map]

@[simp] theorem projectionToSource_substituents_length
    (projection : CarbohydrateFischerChainData) :
    (projectionToSource projection).substituents.length =
      projection.substituents.length := by
  rw [projectionToSource_substituents, List.length_map]

/-- Positional exactness of the recovered ordered list, including duplicate positions. -/
theorem projectionFromSource_substituents_getElem? (projection : SourceProjection)
    (index : Nat) :
    (projectionFromSource projection).substituents[index]?.map substituentToSource =
      projection.substituents[index]? := by
  rw [projectionFromSource_substituents, List.getElem?_map]
  cases get : projection.substituents[index]? with
  | none => simp [get]
  | some substituent => simp [get]

/-- Positional exactness in the other direction. -/
theorem projectionToSource_substituents_getElem? (projection : CarbohydrateFischerChainData)
    (index : Nat) :
    (projectionToSource projection).substituents[index]?.map substituentFromSource =
      projection.substituents[index]? := by
  rw [projectionToSource_substituents, List.getElem?_map]
  cases get : projection.substituents[index]? with
  | none => simp [get]
  | some substituent => simp [get]

/-! ### Flag exactness -/

/-- The hydroxymethyl-termini flag is `true` exactly when the supplied flag is `true`. -/
theorem projectionFromSource_termini_true (projection : SourceProjection)
    (flag : projection.hydroxymethylTermini = true) :
    (projectionFromSource projection).hydroxymethylTermini = true := by
  rw [projectionFromSource_hydroxymethylTermini, flag]

/-- The hydroxymethyl-termini flag is `false` exactly when the supplied flag is `false`. -/
theorem projectionFromSource_termini_false (projection : SourceProjection)
    (flag : projection.hydroxymethylTermini = false) :
    (projectionFromSource projection).hydroxymethylTermini = false := by
  rw [projectionFromSource_hydroxymethylTermini, flag]

/-- The carrier flag is retained exactly in the actual source projection. -/
theorem projectionToSource_termini_true (projection : CarbohydrateFischerChainData)
    (flag : projection.hydroxymethylTermini = true) :
    (projectionToSource projection).hydroxymethylTermini = true := by
  rw [projectionToSource_hydroxymethylTermini, flag]

/-- The carrier flag is retained exactly in the actual source projection. -/
theorem projectionToSource_termini_false (projection : CarbohydrateFischerChainData)
    (flag : projection.hydroxymethylTermini = false) :
    (projectionToSource projection).hydroxymethylTermini = false := by
  rw [projectionToSource_hydroxymethylTermini, flag]

/-! ### Injectivity, bijectivity and the equivalence -/

/-- The closed carrier projection maps injectively to the actual source projection. -/
theorem projectionToSource_injective : Function.Injective projectionToSource :=
  Function.LeftInverse.injective (g := projectionFromSource) projectionFromSource_toSource

/-- The actual source projection maps injectively to the closed carrier. -/
theorem projectionFromSource_injective : Function.Injective projectionFromSource :=
  Function.LeftInverse.injective (g := projectionToSource) projectionToSource_fromSource

/-- The fieldwise map is bijective. -/
theorem projectionToSource_bijective : Function.Bijective projectionToSource :=
  ⟨projectionToSource_injective,
    fun projection => ⟨projectionFromSource projection, projectionToSource_fromSource projection⟩⟩

/-- The closed carrier is equivalent, field for field, to the actual source projection. -/
def projectionEquiv : CarbohydrateFischerChainData ≃ SourceProjection where
  toFun := projectionToSource
  invFun := projectionFromSource
  left_inv := projectionFromSource_toSource
  right_inv := projectionToSource_fromSource

@[simp] theorem projectionEquiv_apply (projection : CarbohydrateFischerChainData) :
    projectionEquiv projection = projectionToSource projection := rfl

@[simp] theorem projectionEquiv_symm_apply (projection : SourceProjection) :
    projectionEquiv.symm projection = projectionFromSource projection := rfl

/-! ### The mirrored well-formedness predicate -/

theorem map_substituents_all_wellFormedFor (carbonCount : Nat)
    (substituents : List CarbohydrateFischerSubstituent) :
    (substituents.map substituentToSource).all
        (fun substituent =>
          Carbohydrate1996ImageAudit.FischerSubstituent.wellFormedFor substituent carbonCount) =
      substituents.all
        (fun substituent =>
          CarbohydrateFischerSubstituent.wellFormedFor substituent carbonCount) := by
  induction substituents with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [substituentToSource, Function.comp_def,
        Carbohydrate1996ImageAudit.FischerSubstituent.wellFormedFor,
        CarbohydrateFischerSubstituent.wellFormedFor, inductionHypothesis]

theorem map_substituents_fromSource_all_wellFormedFor (carbonCount : Nat)
    (substituents : List SourceSubstituent) :
    (substituents.map substituentFromSource).all
        (fun substituent =>
          CarbohydrateFischerSubstituent.wellFormedFor substituent carbonCount) =
      substituents.all
        (fun substituent =>
          Carbohydrate1996ImageAudit.FischerSubstituent.wellFormedFor substituent
            carbonCount) := by
  induction substituents with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [substituentFromSource, Function.comp_def,
        Carbohydrate1996ImageAudit.FischerSubstituent.wellFormedFor,
        CarbohydrateFischerSubstituent.wellFormedFor, inductionHypothesis]

theorem map_substituents_locants (substituents : List CarbohydrateFischerSubstituent) :
    (substituents.map substituentToSource).map
        Carbohydrate1996ImageAudit.FischerSubstituent.locant =
      substituents.map CarbohydrateFischerSubstituent.locant := by
  induction substituents with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [substituentToSource, inductionHypothesis]

theorem map_substituents_fromSource_locants (substituents : List SourceSubstituent) :
    (substituents.map substituentFromSource).map
        CarbohydrateFischerSubstituent.locant =
      substituents.map Carbohydrate1996ImageAudit.FischerSubstituent.locant := by
  induction substituents with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [substituentFromSource, inductionHypothesis]

/-- The carrier's mirrored well-formedness predicate is exactly the actual source predicate. -/
@[simp] theorem wellFormed_projectionToSource (projection : CarbohydrateFischerChainData) :
    (projectionToSource projection).wellFormed = projection.wellFormed := by
  cases projection with
  | mk carbonCount carbonylLocant? substituents hydroxymethylTermini =>
      unfold Carbohydrate1996ImageAudit.FischerProjection.wellFormed
        CarbohydrateFischerChainData.wellFormed
      simp only [projectionToSource, map_substituents_all_wellFormedFor,
        map_substituents_locants]
      rfl

/-- The mirrored predicate is also exactly the actual source predicate in the other direction. -/
@[simp] theorem wellFormed_projectionFromSource (projection : SourceProjection) :
    (projectionFromSource projection).wellFormed = projection.wellFormed := by
  cases projection with
  | mk carbonCount carbonylLocant? substituents hydroxymethylTermini =>
      unfold Carbohydrate1996ImageAudit.FischerProjection.wellFormed
        CarbohydrateFischerChainData.wellFormed
      simp only [projectionFromSource, map_substituents_fromSource_all_wellFormedFor,
        map_substituents_fromSource_locants]
      rfl

/-! ## Consequences of actual source well-formedness

These bounds are derived from `Carbohydrate1996ImageAudit.FischerProjection.wellFormed = true`.
They are not outputs assumed by the codec below. -/

/-- A well-formed actual projection has at least two carbons. -/
theorem wellFormed_carbonCount (projection : SourceProjection)
    (wellFormed : projection.wellFormed = true) :
    2 ≤ projection.carbonCount := by
  unfold Carbohydrate1996ImageAudit.FischerProjection.wellFormed at wellFormed
  cases carbonyl : projection.carbonylLocant? with
  | none =>
      simp only [carbonyl, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        Carbohydrate1996ImageAudit.FischerSubstituent.wellFormedFor,
        Bool.and_true] at wellFormed
      exact wellFormed.1.1
  | some locant =>
      simp only [carbonyl, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        Carbohydrate1996ImageAudit.FischerSubstituent.wellFormedFor] at wellFormed
      exact wellFormed.1.1.1

/-- Every listed source substituent locant of a well-formed projection lies strictly between the
chain ends.  This is the actual source predicate, not an assumed index bound. -/
theorem wellFormed_substituent_bounds (projection : SourceProjection)
    (wellFormed : projection.wellFormed = true)
    {substituent : SourceSubstituent}
    (member : substituent ∈ projection.substituents) :
    1 < substituent.locant ∧ substituent.locant < projection.carbonCount := by
  unfold Carbohydrate1996ImageAudit.FischerProjection.wellFormed at wellFormed
  cases carbonyl : projection.carbonylLocant? with
  | none =>
      simp only [carbonyl, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        Carbohydrate1996ImageAudit.FischerSubstituent.wellFormedFor,
        Bool.and_true] at wellFormed
      exact wellFormed.1.2 substituent member
  | some locant =>
      simp only [carbonyl, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        Carbohydrate1996ImageAudit.FischerSubstituent.wellFormedFor] at wellFormed
      exact wellFormed.1.1.2 substituent member

/-- A present carbonyl locant of a well-formed projection is inside the carbon range. -/
theorem wellFormed_carbonyl_bounds (projection : SourceProjection)
    (wellFormed : projection.wellFormed = true) {locant : Nat}
    (present : projection.carbonylLocant? = some locant) :
    0 < locant ∧ locant ≤ projection.carbonCount := by
  unfold Carbohydrate1996ImageAudit.FischerProjection.wellFormed at wellFormed
  cases carbonyl : projection.carbonylLocant? with
  | none =>
      rw [carbonyl] at present
      simp at present
  | some actual =>
      have actualEq : actual = locant :=
        Option.some.inj (carbonyl.symm.trans present)
      subst locant
      simp only [carbonyl, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        Carbohydrate1996ImageAudit.FischerSubstituent.wellFormedFor] at wellFormed
      exact ⟨wellFormed.2.1.1, wellFormed.2.1.2⟩

/-- The carbonyl locant of a well-formed projection is not also a listed substituent locant. -/
theorem wellFormed_carbonyl_not_substituent (projection : SourceProjection)
    (wellFormed : projection.wellFormed = true) {locant : Nat}
    (present : projection.carbonylLocant? = some locant) :
    locant ∉ projection.substituents.map
      Carbohydrate1996ImageAudit.FischerSubstituent.locant := by
  unfold Carbohydrate1996ImageAudit.FischerProjection.wellFormed at wellFormed
  cases carbonyl : projection.carbonylLocant? with
  | none =>
      rw [carbonyl] at present
      simp at present
  | some actual =>
      have actualEq : actual = locant :=
        Option.some.inj (carbonyl.symm.trans present)
      subst locant
      simp only [carbonyl, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        Carbohydrate1996ImageAudit.FischerSubstituent.wellFormedFor] at wellFormed
      exact wellFormed.2.2

/-! ## Actual ledger carbon binding -/

/-- A physical binding of one actual 1996 Fischer-chain projection to one residue of a real
`ResidueIncidenceLedger Nat input`.

`carbons` is the ordered list of source atom indices.  Its length is exactly the supplied
`carbonCount`, and for every position `i` the source locant `i + 1` resolves in the actual residue
incidence to the `i`-th carbon.  Nothing here says that the projection is chemically correct; it
records the supplied record and the actual source anchors. -/
structure LedgerFischerChainBinding {input : CertifiedAuthoritativeChemicalInput}
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (projection : SourceProjection) where
  /-- The ordered source atoms of the chain carbons. -/
  carbons : List (Fin input.input.molecule.atomCount)
  /-- The number of carbon anchors is exactly the supplied carbon count. -/
  length_eq : carbons.length = projection.carbonCount
  /-- The `i`-th carbon is the actual residue resolution of source locant `i + 1`. -/
  resolves : ∀ i : Fin carbons.length,
    ledger.resolve? residueIndex (i.val + 1) = some (carbons.get i)

namespace LedgerFischerChainBinding

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}
variable {residueIndex : Fin ledger.residueCount}
variable {projection : SourceProjection}

/-- The carbon count and the ordered anchor length agree. -/
theorem carbonCount_eq (binding : LedgerFischerChainBinding ledger residueIndex projection) :
    projection.carbonCount = binding.carbons.length :=
  binding.length_eq.symm

/-- Every carbon anchor is an actual support atom of the bound residue.  This is derived from the
actual resolution field, never assumed. -/
theorem get_mem_support (binding : LedgerFischerChainBinding ledger residueIndex projection)
    (i : Fin binding.carbons.length) :
    binding.carbons.get i ∈ (ledger.residue residueIndex).support :=
  ledger.resolve?_mem_support (binding.resolves i)

/-- The actual resolution statement for position `i`, restated. -/
theorem get_resolves (binding : LedgerFischerChainBinding ledger residueIndex projection)
    (i : Fin binding.carbons.length) :
    ledger.resolve? residueIndex (i.val + 1) = some (binding.carbons.get i) :=
  binding.resolves i

/-- Under the atom enumeration, the `i`-th carbon anchor belongs to the encoded residue support. -/
theorem get_mem_encoded_support {V : Type*}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (binding : LedgerFischerChainBinding ledger residueIndex projection)
    (i : Fin binding.carbons.length) :
    e.symm (binding.carbons.get i) ∈
      (ledger.residue residueIndex).support.map e.symm.toEmbedding :=
  Finset.mem_map.mpr ⟨binding.carbons.get i, binding.get_mem_support i, rfl⟩

/-- A source position strictly inside the chain is an actual carbon position. -/
theorem exists_carbon_index (binding : LedgerFischerChainBinding ledger residueIndex projection)
    {locant : Nat} (lower : 1 ≤ locant) (upper : locant ≤ projection.carbonCount) :
    ∃ i : Fin binding.carbons.length, i.val + 1 = locant := by
  have lengthEq : binding.carbons.length = projection.carbonCount := binding.length_eq
  refine ⟨⟨locant - 1, by omega⟩, ?_⟩
  show locant - 1 + 1 = locant
  omega

/-- A listed source substituent locant has an actual carbon index in the bound chain. -/
theorem substituent_exists_carbon_index
    (binding : LedgerFischerChainBinding ledger residueIndex projection)
    (wellFormed : projection.wellFormed = true)
    {substituent : SourceSubstituent} (member : substituent ∈ projection.substituents) :
    ∃ i : Fin binding.carbons.length, i.val + 1 = substituent.locant := by
  obtain ⟨lower, upper⟩ := wellFormed_substituent_bounds projection wellFormed member
  exact binding.exists_carbon_index (by omega) (by omega)

/-- The substituent locant resolves in the actual residue to the corresponding ordered carbon.
The index bound is derived from actual source well-formedness. -/
theorem substituent_resolves
    (binding : LedgerFischerChainBinding ledger residueIndex projection)
    (wellFormed : projection.wellFormed = true)
    {substituent : SourceSubstituent} (member : substituent ∈ projection.substituents) :
    ∃ i : Fin binding.carbons.length,
      ledger.resolve? residueIndex substituent.locant = some (binding.carbons.get i) ∧
        i.val + 1 = substituent.locant := by
  obtain ⟨i, indexEq⟩ := binding.substituent_exists_carbon_index wellFormed member
  refine ⟨i, ?_, indexEq⟩
  rw [← indexEq]
  exact binding.resolves i

/-- A present carbonyl locant has an actual carbon index in the bound chain. -/
theorem carbonyl_exists_carbon_index
    (binding : LedgerFischerChainBinding ledger residueIndex projection)
    (wellFormed : projection.wellFormed = true) {locant : Nat}
    (present : projection.carbonylLocant? = some locant) :
    ∃ i : Fin binding.carbons.length, i.val + 1 = locant := by
  obtain ⟨lower, upper⟩ := wellFormed_carbonyl_bounds projection wellFormed present
  exact binding.exists_carbon_index (by omega) (by omega)

/-- The carbonyl locant resolves in the actual residue to the corresponding ordered carbon. -/
theorem carbonyl_resolves
    (binding : LedgerFischerChainBinding ledger residueIndex projection)
    (wellFormed : projection.wellFormed = true) {locant : Nat}
    (present : projection.carbonylLocant? = some locant) :
    ∃ i : Fin binding.carbons.length,
      ledger.resolve? residueIndex locant = some (binding.carbons.get i) ∧
        i.val + 1 = locant := by
  obtain ⟨i, indexEq⟩ := binding.carbonyl_exists_carbon_index wellFormed present
  refine ⟨i, ?_, indexEq⟩
  rw [← indexEq]
  exact binding.resolves i

/-- The carbonyl locant is not a listed substituent locant, derived from actual source
well-formedness rather than assumed. -/
theorem carbonyl_not_substituent_locant
    (wellFormed : projection.wellFormed = true) {locant : Nat}
    (present : projection.carbonylLocant? = some locant)
    {substituent : SourceSubstituent} (member : substituent ∈ projection.substituents) :
    locant ≠ substituent.locant := by
  intro equal
  have notMember := wellFormed_carbonyl_not_substituent projection wellFormed present
  apply notMember
  rw [equal]
  exact List.mem_map_of_mem member

end LedgerFischerChainBinding

/-! ## Output-only datum extractors -/

/-- The exact actual source projection carried by a Fischer-chain datum, if it is one. -/
def datumFischerChainProjection? {V : Type*} :
    FragmentSourceDatum V → Option SourceProjection
  | .carbohydrateFischerChain _ projection => some (projectionToSource projection)
  | _ => none

/-- The ordered carbon-anchor list carried by a Fischer-chain datum, if it is one. -/
def datumFischerChainAnchors? {V : Type*} :
    FragmentSourceDatum V → Option (List V)
  | .carbohydrateFischerChain carbons _ => some carbons
  | _ => none

@[simp] theorem datumFischerChainProjection?_chain {V : Type*}
    (carbons : List V) (projection : CarbohydrateFischerChainData) :
    datumFischerChainProjection? (V := V)
        (.carbohydrateFischerChain carbons projection) =
      some (projectionToSource projection) := rfl

@[simp] theorem datumFischerChainAnchors?_chain {V : Type*}
    (carbons : List V) (projection : CarbohydrateFischerChainData) :
    datumFischerChainAnchors? (V := V)
        (.carbohydrateFischerChain carbons projection) = some carbons := rfl

/-! ## The emitted datum and its support -/

/-- Emit one actual source projection as a shared closed datum with the ordered carbon anchors,
mapped through the external atom enumeration.  The payload is the fieldwise carrier copy. -/
def datumOfBinding {V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} {residueIndex : Fin ledger.residueCount}
    {projection : SourceProjection}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (binding : LedgerFischerChainBinding ledger residueIndex projection) :
    FragmentSourceDatum V :=
  .carbohydrateFischerChain (binding.carbons.map e.symm) (projectionFromSource projection)

@[simp] theorem datumOfBinding_atomReferences {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} {residueIndex : Fin ledger.residueCount}
    {projection : SourceProjection}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (binding : LedgerFischerChainBinding ledger residueIndex projection) :
    (datumOfBinding e binding).atomReferences = binding.carbons.map e.symm := rfl

/-- The emitted datum carries exactly the supplied actual source projection. -/
@[simp] theorem datumOfBinding_projection {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} {residueIndex : Fin ledger.residueCount}
    {projection : SourceProjection}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (binding : LedgerFischerChainBinding ledger residueIndex projection) :
    datumFischerChainProjection? (datumOfBinding e binding) = some projection := by
  simp [datumOfBinding]

/-- The emitted datum carries exactly the ordered carbon anchors. -/
@[simp] theorem datumOfBinding_anchors {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} {residueIndex : Fin ledger.residueCount}
    {projection : SourceProjection}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (binding : LedgerFischerChainBinding ledger residueIndex projection) :
    datumFischerChainAnchors? (datumOfBinding e binding) = some (binding.carbons.map e.symm) :=
  rfl

/-- Every anchor of the emitted datum belongs to the encoded actual residue support.  The proof
uses the actual ledger resolutions recorded in the binding. -/
theorem datumOfBinding_supported {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} {residueIndex : Fin ledger.residueCount}
    {projection : SourceProjection}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (binding : LedgerFischerChainBinding ledger residueIndex projection) :
    ∀ atom ∈ (datumOfBinding e binding).atomReferences,
      atom ∈ (ledger.residue residueIndex).support.map e.symm.toEmbedding := by
  intro atom member
  rw [datumOfBinding_atomReferences] at member
  obtain ⟨carbon, carbonMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, getEq⟩ := List.mem_iff_get.mp carbonMember
  rw [← getEq]
  exact binding.get_mem_encoded_support e i

/-- The actual ledger resolution of the `i + 1` locant is the `i`-th emitted anchor. -/
theorem datumOfBinding_resolveAnchor? {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} {residueIndex : Fin ledger.residueCount}
    {projection : SourceProjection}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (binding : LedgerFischerChainBinding ledger residueIndex projection)
    (i : Fin binding.carbons.length) :
    resolveAnchor? e ledger residueIndex (i.val + 1) =
      some (e.symm (binding.carbons.get i)) := by
  have resolved := congrArg (Option.map e.symm) (binding.resolves i)
  simpa [resolveAnchor?, ResidueFragment.locate?_eq_incidence,
    ResidueIncidenceLedger.resolve?_eq] using resolved

/-! ## Direct `withSourceData` annotation -/

/-- Build the shared fragment annotation from one actual residue, attaching exactly one emitted
Fischer-chain datum with `FragmentAnnotation.withSourceData`.  The support certificate is derived
from actual ledger incidence. -/
def annotationWithFischerChain {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (cover : List Nat) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger residueIndex projection) :
    FragmentAnnotation V :=
  (encodeFragment LocantCodec.nat e (ledger.residue residueIndex) cover).withSourceData
    [datumOfBinding e binding]
    (by
      intro datum member atom atomMem
      rw [List.mem_singleton] at member
      subst datum
      simpa [encodeFragment_support] using datumOfBinding_supported e binding atom atomMem)

/-- The direct annotation's source-data channel is exactly the one emitted datum. -/
@[simp] theorem annotationWithFischerChain_sourceData {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (cover : List Nat) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger residueIndex projection) :
    (annotationWithFischerChain e ledger residueIndex cover projection binding).sourceData =
      [datumOfBinding e binding] := by
  simp [annotationWithFischerChain]

/-- Attaching the Fischer-chain datum does not change the encoded physical support. -/
@[simp] theorem annotationWithFischerChain_support {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (cover : List Nat) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger residueIndex projection) :
    (annotationWithFischerChain e ledger residueIndex cover projection binding).support =
      (ledger.residue residueIndex).support.map e.symm.toEmbedding := by
  simp [annotationWithFischerChain, encodeFragment_support]

/-- Exact source readback from the direct `withSourceData` annotation: the emitted source-data
channel maps to exactly the supplied projection. -/
theorem annotationWithFischerChain_readback {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (cover : List Nat) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger residueIndex projection) :
    ((annotationWithFischerChain e ledger residueIndex cover projection binding).sourceData).filterMap
        datumFischerChainProjection? = [projection] := by
  rw [annotationWithFischerChain_sourceData]
  simp [datumOfBinding_projection]

/-- Exact ordered-carbon readback from the direct `withSourceData` annotation. -/
theorem annotationWithFischerChain_anchors {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (cover : List Nat) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger residueIndex projection) :
    ((annotationWithFischerChain e ledger residueIndex cover projection binding).sourceData).filterMap
        datumFischerChainAnchors? = [binding.carbons.map e.symm] := by
  rw [annotationWithFischerChain_sourceData]
  simp

/-- Append one emitted Fischer-chain datum beside an existing annotation's source data.  Old data
stay in front; the new datum is the exact suffix. -/
def appendFischerChainDatum {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (annotation : FragmentAnnotation V)
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger residueIndex projection)
    (anchorsSupported : ∀ atom ∈ (datumOfBinding e binding).atomReferences,
      atom ∈ annotation.support) :
    FragmentAnnotation V :=
  annotation.withSourceData [datumOfBinding e binding]
    (by
      intro datum member atom atomMem
      rw [List.mem_singleton] at member
      subst datum
      exact anchorsSupported atom atomMem)

/-- Appending retains the whole old source-data list as the exact prefix. -/
@[simp] theorem appendFischerChainDatum_sourceData {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (annotation : FragmentAnnotation V)
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger residueIndex projection)
    (anchorsSupported : ∀ atom ∈ (datumOfBinding e binding).atomReferences,
      atom ∈ annotation.support) :
    (appendFischerChainDatum annotation e ledger residueIndex projection binding
        anchorsSupported).sourceData =
      annotation.sourceData ++ [datumOfBinding e binding] := by
  simp [appendFischerChainDatum]

/-- The old annotation's source-data list is recovered as the exact prefix. -/
theorem appendFischerChainDatum_old_prefix {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (annotation : FragmentAnnotation V)
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger residueIndex projection)
    (anchorsSupported : ∀ atom ∈ (datumOfBinding e binding).atomReferences,
      atom ∈ annotation.support) :
    (appendFischerChainDatum annotation e ledger residueIndex projection binding
        anchorsSupported).sourceData.take annotation.sourceData.length =
      annotation.sourceData := by
  rw [appendFischerChainDatum_sourceData, List.take_left]

/-- The new datum is the exact suffix, selected by the old source-data length. -/
theorem appendFischerChainDatum_new_suffix {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (annotation : FragmentAnnotation V)
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger residueIndex projection)
    (anchorsSupported : ∀ atom ∈ (datumOfBinding e binding).atomReferences,
      atom ∈ annotation.support) :
    (appendFischerChainDatum annotation e ledger residueIndex projection binding
        anchorsSupported).sourceData.drop annotation.sourceData.length =
      [datumOfBinding e binding] := by
  rw [appendFischerChainDatum_sourceData, List.drop_left]

/-- Exact source readback from the actual appended suffix of the direct annotation. -/
theorem appendFischerChainDatum_suffix_projection {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (annotation : FragmentAnnotation V)
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger residueIndex projection)
    (anchorsSupported : ∀ atom ∈ (datumOfBinding e binding).atomReferences,
      atom ∈ annotation.support) :
    (((appendFischerChainDatum annotation e ledger residueIndex projection binding
        anchorsSupported).sourceData.drop annotation.sourceData.length)).filterMap
        datumFischerChainProjection? = [projection] := by
  rw [appendFischerChainDatum_new_suffix]
  simp [datumOfBinding_projection]

/-- Appending does not change the actual support. -/
@[simp] theorem appendFischerChainDatum_support {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (annotation : FragmentAnnotation V)
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger residueIndex projection)
    (anchorsSupported : ∀ atom ∈ (datumOfBinding e binding).atomReferences,
      atom ∈ annotation.support) :
    (appendFischerChainDatum annotation e ledger residueIndex projection binding
        anchorsSupported).support = annotation.support := by
  simp [appendFischerChainDatum]

/-- Appending does not change the ordered scoped bindings. -/
@[simp] theorem appendFischerChainDatum_bindings {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (annotation : FragmentAnnotation V)
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger residueIndex projection)
    (anchorsSupported : ∀ atom ∈ (datumOfBinding e binding).atomReferences,
      atom ∈ annotation.support) :
    (appendFischerChainDatum annotation e ledger residueIndex projection binding
        anchorsSupported).bindings = annotation.bindings := by
  simp [appendFischerChainDatum]

/-! ## `encodeWithSourceData` at one actual residue -/

/-- The isolated per-residue source-data family: the ordered list is attached at `index` and every
other actual residue occurrence is empty. -/
def residueSourceDataAt {V : Type*} {residueCount : Nat} (index : Fin residueCount)
    (data : List (FragmentSourceDatum V)) :
    Fin residueCount → List (FragmentSourceDatum V) :=
  fun other => if other = index then data else []

@[simp] theorem residueSourceDataAt_self {V : Type*} {residueCount : Nat}
    (index : Fin residueCount) (data : List (FragmentSourceDatum V)) :
    residueSourceDataAt index data index = data := by
  simp [residueSourceDataAt]

@[simp] theorem residueSourceDataAt_of_ne {V : Type*} {residueCount : Nat}
    {index other : Fin residueCount} (data : List (FragmentSourceDatum V))
    (different : other ≠ index) :
    residueSourceDataAt index data other = [] := by
  simp [residueSourceDataAt, different]

/-- The isolated family satisfies the support invariant whenever every anchor is in the actual
support of the selected residue. -/
theorem residueSourceDataAt_supported {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (index : Fin ledger.residueCount) (data : List (FragmentSourceDatum V))
    (supported : ∀ datum ∈ data, ∀ atom ∈ datum.atomReferences,
      atom ∈ (ledger.residue index).support.map e.symm.toEmbedding) :
    ∀ other, ∀ datum ∈ residueSourceDataAt index data other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding := by
  intro other datum member atom atomMem
  by_cases h : other = index
  · subst other
    rw [residueSourceDataAt_self] at member
    exact supported datum member atom atomMem
  · rw [residueSourceDataAt_of_ne data h] at member
    simp at member

/-- Encode one actual source projection at one actual ledger residue through the shared
`encodeWithSourceData` codec. -/
def encodeFischerChainAt {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection) :
    ResidueLedgerAnnotation V ledger.residueCount input.input.molecule.interactions.length :=
  encodeWithSourceData codec e ledger cover
    (residueSourceDataAt index [datumOfBinding e binding])
    (residueSourceDataAt_supported e ledger index [datumOfBinding e binding] (by
      intro datum member atom atomMem
      rw [List.mem_singleton] at member
      subst datum
      exact datumOfBinding_supported e binding atom atomMem))

/-- The encoded residue occurrence carries exactly the one emitted Fischer-chain datum. -/
@[simp] theorem encodeFischerChainAt_residue_sourceData {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection) :
    ((encodeFischerChainAt codec e ledger cover index projection binding).residue
        index).sourceData = [datumOfBinding e binding] := by
  unfold encodeFischerChainAt
  rw [encodeWithSourceData_residue_sourceData]
  simp

/-- The encoded support is exactly the actual ledger residue support transported by the
enumeration; source data ride alongside it. -/
@[simp] theorem encodeFischerChainAt_residue_support {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection) :
    ((encodeFischerChainAt codec e ledger cover index projection binding).residue
        index).support =
      (ledger.residue index).support.map e.symm.toEmbedding := by
  simp [encodeFischerChainAt, encodeWithSourceData_residue, FragmentAnnotation.withSourceData_support,
    encodeFragment_support]

/-- Output-only readback from the actual encoded annotation: the exact source projection. -/
def fischerChainReadback {V : Type*} {residueCount interactionCount : Nat}
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) : Option SourceProjection :=
  ((annotation.residue index).sourceData.filterMap datumFischerChainProjection?).head?

/-- The output-only accessor recovers exactly the supplied projection. -/
@[simp] theorem fischerChainReadback_encodeFischerChainAt {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection) :
    fischerChainReadback
        (encodeFischerChainAt codec e ledger cover index projection binding) index =
      some projection := by
  unfold fischerChainReadback
  rw [encodeFischerChainAt_residue_sourceData]
  simp [datumOfBinding_projection]

/-! ## Appending to old source data at the actual residue -/

/-- The old ordered source-data family with one new ordered list appended at `index`. -/
def appendSourceDataAt {V : Type*} {residueCount : Nat} (index : Fin residueCount)
    (data : List (FragmentSourceDatum V))
    (oldData : Fin residueCount → List (FragmentSourceDatum V)) :
    Fin residueCount → List (FragmentSourceDatum V) :=
  fun other => if other = index then oldData other ++ data else oldData other

@[simp] theorem appendSourceDataAt_self {V : Type*} {residueCount : Nat}
    (index : Fin residueCount) (data : List (FragmentSourceDatum V))
    (oldData : Fin residueCount → List (FragmentSourceDatum V)) :
    appendSourceDataAt index data oldData index = oldData index ++ data := by
  simp [appendSourceDataAt]

@[simp] theorem appendSourceDataAt_of_ne {V : Type*} {residueCount : Nat}
    {index other : Fin residueCount} (data : List (FragmentSourceDatum V))
    (oldData : Fin residueCount → List (FragmentSourceDatum V))
    (different : other ≠ index) :
    appendSourceDataAt index data oldData other = oldData other := by
  simp [appendSourceDataAt, different]

/-- Appending preserves the support invariant: old data remain supported at every occurrence and
the new data are supported at the selected occurrence. -/
theorem appendSourceDataAt_supported {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (index : Fin ledger.residueCount) (data : List (FragmentSourceDatum V))
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : ∀ other, ∀ datum ∈ oldData other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding)
    (newSupported : ∀ datum ∈ data, ∀ atom ∈ datum.atomReferences,
      atom ∈ (ledger.residue index).support.map e.symm.toEmbedding) :
    ∀ other, ∀ datum ∈ appendSourceDataAt index data oldData other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding := by
  intro other datum member atom atomMem
  by_cases h : other = index
  · subst other
    rw [appendSourceDataAt_self] at member
    rcases List.mem_append.mp member with oldMember | newMember
    · exact oldSupported index datum oldMember atom atomMem
    · exact newSupported datum newMember atom atomMem
  · rw [appendSourceDataAt_of_ne data oldData h] at member
    exact oldSupported other datum member atom atomMem

/-- Encode one actual source projection at one actual ledger residue, appending it *after* the
caller's existing ordered source data at that residue.  Every other residue keeps its old data
exactly. -/
def encodeFischerChainAppendedAt {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : ∀ other, ∀ datum ∈ oldData other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding) :
    ResidueLedgerAnnotation V ledger.residueCount input.input.molecule.interactions.length :=
  encodeWithSourceData codec e ledger cover
    (appendSourceDataAt index [datumOfBinding e binding] oldData)
    (appendSourceDataAt_supported e ledger index [datumOfBinding e binding] oldData
      oldSupported (by
        intro datum member atom atomMem
        rw [List.mem_singleton] at member
        subst datum
        exact datumOfBinding_supported e binding atom atomMem))

/-- At the selected residue, the emitted ordered source data are exactly the old list followed by
the one new datum. -/
@[simp] theorem encodeFischerChainAppendedAt_residue_sourceData {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : ∀ other, ∀ datum ∈ oldData other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding) :
    ((encodeFischerChainAppendedAt codec e ledger cover index projection binding oldData
        oldSupported).residue index).sourceData =
      oldData index ++ [datumOfBinding e binding] := by
  unfold encodeFischerChainAppendedAt
  rw [encodeWithSourceData_residue_sourceData]
  simp

/-- At every other residue, the old annotation is preserved literally. -/
theorem encodeFischerChainAppendedAt_residue_sourceData_of_ne {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : ∀ other, ∀ datum ∈ oldData other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding)
    (other : Fin ledger.residueCount) (different : other ≠ index) :
    ((encodeFischerChainAppendedAt codec e ledger cover index projection binding oldData
        oldSupported).residue other).sourceData = oldData other := by
  unfold encodeFischerChainAppendedAt
  rw [encodeWithSourceData_residue_sourceData]
  simp [appendSourceDataAt, different]

/-- The old ordered list is retained as the exact prefix at the selected residue. -/
theorem encodeFischerChainAppendedAt_old_prefix {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : ∀ other, ∀ datum ∈ oldData other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding) :
    ((encodeFischerChainAppendedAt codec e ledger cover index projection binding oldData
        oldSupported).residue index).sourceData.take (oldData index).length =
      oldData index := by
  rw [encodeFischerChainAppendedAt_residue_sourceData, List.take_left]

/-- The new datum is the exact suffix selected by the old prefix length. -/
theorem encodeFischerChainAppendedAt_new_suffix {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : ∀ other, ∀ datum ∈ oldData other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding) :
    ((encodeFischerChainAppendedAt codec e ledger cover index projection binding oldData
        oldSupported).residue index).sourceData.drop (oldData index).length =
      [datumOfBinding e binding] := by
  rw [encodeFischerChainAppendedAt_residue_sourceData, List.drop_left]

/-- **Exact source readback from the emitted suffix.**  Dropping the old prefix length from the
actual emitted source-data list and reading only the Fischer-chain projection yields exactly the
supplied actual source projection. -/
theorem encodeFischerChainAppendedAt_suffix_projection {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : ∀ other, ∀ datum ∈ oldData other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding) :
    ((((encodeFischerChainAppendedAt codec e ledger cover index projection binding oldData
        oldSupported).residue index).sourceData.drop (oldData index).length).filterMap
          datumFischerChainProjection?) = [projection] := by
  rw [encodeFischerChainAppendedAt_new_suffix]
  simp [datumOfBinding_projection]

/-- **Exact ordered-anchor readback from the emitted suffix.** -/
theorem encodeFischerChainAppendedAt_suffix_anchors {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : ∀ other, ∀ datum ∈ oldData other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding) :
    ((((encodeFischerChainAppendedAt codec e ledger cover index projection binding oldData
        oldSupported).residue index).sourceData.drop (oldData index).length).filterMap
          datumFischerChainAnchors?) = [binding.carbons.map e.symm] := by
  rw [encodeFischerChainAppendedAt_new_suffix]
  simp

/-- Output-only suffix accessor: read the exact source projection at a given offset of a residue's
actual emitted source-data list. -/
def emittedFischerChainSuffix? {V : Type*} {residueCount interactionCount : Nat}
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) (offset : Nat) : Option SourceProjection :=
  (((annotation.residue index).sourceData.drop offset).filterMap
    datumFischerChainProjection?).head?

/-- The output-only suffix accessor recovers exactly the supplied actual projection. -/
@[simp] theorem emittedFischerChainSuffix?_encodeFischerChainAppendedAt {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : ∀ other, ∀ datum ∈ oldData other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding) :
    emittedFischerChainSuffix?
        (encodeFischerChainAppendedAt codec e ledger cover index projection binding oldData
          oldSupported) index (oldData index).length = some projection := by
  unfold emittedFischerChainSuffix?
  rw [encodeFischerChainAppendedAt_suffix_projection]
  rfl

/-! ### Physical preservation of the appended encoding -/

/-- Appending source data does not change the encoded residue support. -/
@[simp] theorem encodeFischerChainAppendedAt_residue_support {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : ∀ other, ∀ datum ∈ oldData other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding) :
    ((encodeFischerChainAppendedAt codec e ledger cover index projection binding oldData
        oldSupported).residue index).support =
      (ledger.residue index).support.map e.symm.toEmbedding := by
  simp [encodeFischerChainAppendedAt, encodeWithSourceData_residue, FragmentAnnotation.withSourceData_support,
    encodeFragment_support]

/-- Appending source data does not change the ordered scoped bindings. -/
@[simp] theorem encodeFischerChainAppendedAt_residue_bindings {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : ∀ other, ∀ datum ∈ oldData other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding) :
    ((encodeFischerChainAppendedAt codec e ledger cover index projection binding oldData
        oldSupported).residue index).bindings =
      (cover index).map (fun locant => (codec.code locant,
        ((ledger.residue index).incidence locant).map e.symm)) := by
  simp [encodeFischerChainAppendedAt, encodeWithSourceData_residue, FragmentAnnotation.withSourceData_bindings,
    encodeFragment_bindings]

/-- Appending source data does not change the ordered link list.  It is exactly the encoding of the
actual ledger link list. -/
@[simp] theorem encodeFischerChainAppendedAt_links {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : ∀ other, ∀ datum ∈ oldData other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding) :
    (encodeFischerChainAppendedAt codec e ledger cover index projection binding oldData
        oldSupported).links = ledger.links.map (encodeLink codec) := by
  simp [encodeFischerChainAppendedAt]

/-- Appending source data does not change the optional naming hierarchy. -/
@[simp] theorem encodeFischerChainAppendedAt_hierarchy? {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : ∀ other, ∀ datum ∈ oldData other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding) :
    (encodeFischerChainAppendedAt codec e ledger cover index projection binding oldData
        oldSupported).hierarchy? = ledger.hierarchy? := by
  simp [encodeFischerChainAppendedAt]

/-! ## Bundled exactness and kernel receipts -/

/-- Bundled result: the actual projection, the ordered anchors and the old prefix are all
recovered exactly from the emitted annotation. -/
theorem encodeFischerChainAppendedAt_recovery {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Nat) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (index : Fin ledger.residueCount) (projection : SourceProjection)
    (binding : LedgerFischerChainBinding ledger index projection)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : ∀ other, ∀ datum ∈ oldData other,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue other).support.map e.symm.toEmbedding) :
    emittedFischerChainSuffix?
        (encodeFischerChainAppendedAt codec e ledger cover index projection binding oldData
          oldSupported) index (oldData index).length = some projection ∧
      ((((encodeFischerChainAppendedAt codec e ledger cover index projection binding oldData
          oldSupported).residue index).sourceData.take (oldData index).length) =
        oldData index) ∧
      ((((encodeFischerChainAppendedAt codec e ledger cover index projection binding oldData
          oldSupported).residue index).sourceData.drop (oldData index).length).filterMap
            datumFischerChainAnchors? = [binding.carbons.map e.symm]) ∧
      ((encodeFischerChainAppendedAt codec e ledger cover index projection binding oldData
          oldSupported).residue index).support =
        (ledger.residue index).support.map e.symm.toEmbedding ∧
      (encodeFischerChainAppendedAt codec e ledger cover index projection binding oldData
          oldSupported).links = ledger.links.map (encodeLink codec) :=
  ⟨emittedFischerChainSuffix?_encodeFischerChainAppendedAt codec e ledger cover index projection
      binding oldData oldSupported,
    encodeFischerChainAppendedAt_old_prefix codec e ledger cover index projection binding oldData
      oldSupported,
    encodeFischerChainAppendedAt_suffix_anchors codec e ledger cover index projection binding
      oldData oldSupported,
    encodeFischerChainAppendedAt_residue_support codec e ledger cover index projection binding
      oldData oldSupported,
    encodeFischerChainAppendedAt_links codec e ledger cover index projection binding oldData
      oldSupported⟩

/-! ## Canonical-output endpoint

The approved `OrganicStereoSourceDataResidueAssembly` module already turns a request, an actual
same-ledger source-data family and its real-anchor guard into the actual
`CanonicalOrganicMolecularRepresentation`, and its decoder `decodedSourceDataAt?` reads only that
actual output.  This section is a thin instantiation of that interface: the source-data family is
the isolated `residueSourceDataAt` list holding exactly one `datumOfBinding`, and the projection
decoder is composed with `datumFischerChainProjection?`.  No second codec or assembly is
introduced. -/

open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoMolecularCanonicalTransport
open OrganicStereoIndependentElectronicEncoding

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The actual per-residue source-data family for the canonical assembly: exactly one emitted
Fischer-chain datum at `index`, and the empty list at every other residue. -/
def canonicalSourceDataAt {request : OrganicMolecularEvidence V}
    (enumeration : V ≃ Fin (Fintype.card V))
    {ledger : ResidueIncidenceLedger Nat (request.graph.certifiedEncoding enumeration)}
    {index : Fin ledger.residueCount} {projection : SourceProjection}
    (binding : LedgerFischerChainBinding ledger index projection) :
    Fin ledger.residueCount → List (FragmentSourceDatum V) :=
  residueSourceDataAt index
    [datumOfBinding (encodedAtomEquiv request.graph enumeration) binding]

@[simp] theorem canonicalSourceDataAt_self {request : OrganicMolecularEvidence V}
    (enumeration : V ≃ Fin (Fintype.card V))
    {ledger : ResidueIncidenceLedger Nat (request.graph.certifiedEncoding enumeration)}
    {index : Fin ledger.residueCount} {projection : SourceProjection}
    (binding : LedgerFischerChainBinding ledger index projection) :
    canonicalSourceDataAt enumeration binding index =
      [datumOfBinding (encodedAtomEquiv request.graph enumeration) binding] := by
  simp [canonicalSourceDataAt]

@[simp] theorem canonicalSourceDataAt_of_ne {request : OrganicMolecularEvidence V}
    (enumeration : V ≃ Fin (Fintype.card V))
    {ledger : ResidueIncidenceLedger Nat (request.graph.certifiedEncoding enumeration)}
    {index : Fin ledger.residueCount} {projection : SourceProjection}
    (binding : LedgerFischerChainBinding ledger index projection)
    {other : Fin ledger.residueCount} (different : other ≠ index) :
    canonicalSourceDataAt enumeration binding other = [] := by
  simp [canonicalSourceDataAt, residueSourceDataAt_of_ne _ different]

/-- The canonical source-data family satisfies the approved real-anchor guard.  It is derived from
the actual ledger resolutions through `datumOfBinding_supported`, not assumed. -/
theorem canonicalSourceDataAt_supported {request : OrganicMolecularEvidence V}
    (enumeration : V ≃ Fin (Fintype.card V))
    {ledger : ResidueIncidenceLedger Nat (request.graph.certifiedEncoding enumeration)}
    {index : Fin ledger.residueCount} {projection : SourceProjection}
    (binding : LedgerFischerChainBinding ledger index projection) :
    SourceDataSupported (Locant := Nat) request.graph enumeration ledger
      (canonicalSourceDataAt enumeration binding) := by
  unfold canonicalSourceDataAt
  exact residueSourceDataAt_supported (encodedAtomEquiv request.graph enumeration) ledger index
    [datumOfBinding (encodedAtomEquiv request.graph enumeration) binding] (by
      intro datum member atom atomMem
      rw [List.mem_singleton] at member
      subst datum
      exact datumOfBinding_supported (encodedAtomEquiv request.graph enumeration) binding atom
        atomMem)

/-- The actual canonical output of the approved assembly for the isolated Fischer-chain family. -/
def canonicalOutputWithFischerChain {request : OrganicMolecularEvidence V}
    (enumeration : V ≃ Fin (Fintype.card V))
    {ledger : ResidueIncidenceLedger Nat (request.graph.certifiedEncoding enumeration)}
    {index : Fin ledger.residueCount} {projection : SourceProjection}
    (binding : LedgerFischerChainBinding ledger index projection)
    (cover : LocantCover ledger) : CanonicalOrganicMolecularRepresentation V :=
  sourceDataCanonicalOutput LocantCodec.nat enumeration request ledger cover
    (canonicalSourceDataAt enumeration binding) (canonicalSourceDataAt_supported enumeration binding)

/-- Output-only projection decoder: read the ordered source-data list at a residue position from
the actual canonical output, then read the unique Fischer-chain projection carried by that list. -/
def canonicalFischerChainProjectionAt?
    (canonical : CanonicalOrganicMolecularRepresentation V) (index : Nat) :
    Option SourceProjection :=
  (decodedSourceDataAt? canonical index).bind fun data =>
    (data.filterMap datumFischerChainProjection?).head?

/-- Output-only ordered-anchor decoder at a residue position of the actual canonical output. -/
def canonicalFischerChainAnchorsAt?
    (canonical : CanonicalOrganicMolecularRepresentation V) (index : Nat) :
    Option (List V) :=
  (decodedSourceDataAt? canonical index).bind fun data =>
    (data.filterMap datumFischerChainAnchors?).head?

/-- **Actual canonical source readback.**  The projection decoder composed with
`decodedSourceDataAt?` recovers exactly the supplied actual `FischerProjection` from the actual
canonical output. -/
@[simp] theorem canonicalFischerChainProjectionAt?_canonicalOutputWithFischerChain
    {request : OrganicMolecularEvidence V}
    (enumeration : V ≃ Fin (Fintype.card V))
    {ledger : ResidueIncidenceLedger Nat (request.graph.certifiedEncoding enumeration)}
    {index : Fin ledger.residueCount} {projection : SourceProjection}
    (binding : LedgerFischerChainBinding ledger index projection)
    (cover : LocantCover ledger) :
    canonicalFischerChainProjectionAt?
        (canonicalOutputWithFischerChain enumeration binding cover) index.val =
      some projection := by
  unfold canonicalFischerChainProjectionAt? canonicalOutputWithFischerChain
  rw [decodedSourceDataAt?_sourceDataCanonicalOutput]
  simp [canonicalSourceDataAt, datumOfBinding_projection]

/-- **Actual canonical ordered-anchor readback.**  The ordered carbon anchors are recovered
exactly, in order, from the same actual canonical output. -/
@[simp] theorem canonicalFischerChainAnchorsAt?_canonicalOutputWithFischerChain
    {request : OrganicMolecularEvidence V}
    (enumeration : V ≃ Fin (Fintype.card V))
    {ledger : ResidueIncidenceLedger Nat (request.graph.certifiedEncoding enumeration)}
    {index : Fin ledger.residueCount} {projection : SourceProjection}
    (binding : LedgerFischerChainBinding ledger index projection)
    (cover : LocantCover ledger) :
    canonicalFischerChainAnchorsAt?
        (canonicalOutputWithFischerChain enumeration binding cover) index.val =
      some (binding.carbons.map (encodedAtomEquiv request.graph enumeration).symm) := by
  unfold canonicalFischerChainAnchorsAt? canonicalOutputWithFischerChain
  rw [decodedSourceDataAt?_sourceDataCanonicalOutput]
  simp [canonicalSourceDataAt, datumOfBinding_anchors]
  all_goals first | rfl | (intro atom _; rfl)

/-- The canonical output carries the whole derived channel, including the exact ordered
source-data family attached at the selected residue. -/
theorem canonicalOutputWithFischerChain_channel
    {request : OrganicMolecularEvidence V}
    (enumeration : V ≃ Fin (Fintype.card V))
    {ledger : ResidueIncidenceLedger Nat (request.graph.certifiedEncoding enumeration)}
    {index : Fin ledger.residueCount} {projection : SourceProjection}
    (binding : LedgerFischerChainBinding ledger index projection)
    (cover : LocantCover ledger) :
    sourceDataResidueChannel? (canonicalOutputWithFischerChain enumeration binding cover) =
      some (sourceDataBoundChannel LocantCodec.nat enumeration request.graph ledger cover
        (canonicalSourceDataAt enumeration binding)
        (canonicalSourceDataAt_supported enumeration binding)) := by
  unfold canonicalOutputWithFischerChain
  exact sourceDataResidueChannel?_sourceDataCanonicalOutput LocantCodec.nat enumeration request
    ledger cover (canonicalSourceDataAt enumeration binding)
    (canonicalSourceDataAt_supported enumeration binding)

/-! ### Same-ledger append endpoint -/

/-- Output-only suffix projection decoder: read a residue list from the actual canonical output,
drop the old prefix length, then read the Fischer-chain projection. -/
def canonicalFischerChainSuffixAt?
    (canonical : CanonicalOrganicMolecularRepresentation V) (index offset : Nat) :
    Option SourceProjection :=
  (decodedSourceDataAt? canonical index).bind fun data =>
    ((data.drop offset).filterMap datumFischerChainProjection?).head?

/-- The actual canonical output of the approved append assembly on the **same** actual ledger and
cover: the caller's old ordered data first, then exactly one Fischer-chain datum at `index`. -/
def canonicalAppendedOutputWithFischerChain {request : OrganicMolecularEvidence V}
    (enumeration : V ≃ Fin (Fintype.card V))
    {ledger : ResidueIncidenceLedger Nat (request.graph.certifiedEncoding enumeration)}
    {index : Fin ledger.residueCount} {projection : SourceProjection}
    (binding : LedgerFischerChainBinding ledger index projection)
    (cover : LocantCover ledger)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Nat) request.graph enumeration ledger oldData) :
    CanonicalOrganicMolecularRepresentation V :=
  sourceDataAppendedCanonicalOutput LocantCodec.nat enumeration request ledger cover oldData
    (canonicalSourceDataAt enumeration binding) oldSupported
    (canonicalSourceDataAt_supported enumeration binding)

/-- **Actual canonical appended-suffix readback.**  Dropping the caller's old prefix length from
the list decoded at the selected residue of the actual canonical output yields exactly the
supplied actual `FischerProjection`. -/
@[simp] theorem canonicalFischerChainSuffixAt?_canonicalAppendedOutputWithFischerChain
    {request : OrganicMolecularEvidence V}
    (enumeration : V ≃ Fin (Fintype.card V))
    {ledger : ResidueIncidenceLedger Nat (request.graph.certifiedEncoding enumeration)}
    {index : Fin ledger.residueCount} {projection : SourceProjection}
    (binding : LedgerFischerChainBinding ledger index projection)
    (cover : LocantCover ledger)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Nat) request.graph enumeration ledger oldData) :
    canonicalFischerChainSuffixAt?
        (canonicalAppendedOutputWithFischerChain enumeration binding cover oldData oldSupported)
        index.val (oldData index).length = some projection := by
  unfold canonicalFischerChainSuffixAt? decodedSourceDataAt?
    canonicalAppendedOutputWithFischerChain
  rw [sourceDataAppendedCanonicalOutput_lists]
  simp only [Option.bind_some, List.getElem?_ofFn, dif_pos index.isLt]
  simp [canonicalSourceDataAt, List.drop_left, datumOfBinding_projection]

/-- The appended canonical output retains the old ordered list as the exact prefix at the selected
residue. -/
theorem canonicalAppendedOutputWithFischerChain_old_prefix
    {request : OrganicMolecularEvidence V}
    (enumeration : V ≃ Fin (Fintype.card V))
    {ledger : ResidueIncidenceLedger Nat (request.graph.certifiedEncoding enumeration)}
    {index : Fin ledger.residueCount} {projection : SourceProjection}
    (binding : LedgerFischerChainBinding ledger index projection)
    (cover : LocantCover ledger)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Nat) request.graph enumeration ledger oldData) :
    (decodedSourceDataAt?
        (canonicalAppendedOutputWithFischerChain enumeration binding cover oldData oldSupported)
        index.val).map (fun data => data.take (oldData index).length) = some (oldData index) := by
  unfold decodedSourceDataAt? canonicalAppendedOutputWithFischerChain
  rw [sourceDataAppendedCanonicalOutput_lists, Option.bind_some, List.getElem?_ofFn,
    dif_pos index.isLt, Option.map_some]
  simp [canonicalSourceDataAt]

/-- Bundled actual canonical endpoint: exact projection readback, exact ordered-anchor readback,
the complete derived channel, and (for the same-ledger append form) exact old-prefix and new-suffix
reads.  All components are the individual theorems above; this theorem only conjoins them. -/
theorem canonicalOutputWithFischerChain_recovery
    {request : OrganicMolecularEvidence V}
    (enumeration : V ≃ Fin (Fintype.card V))
    {ledger : ResidueIncidenceLedger Nat (request.graph.certifiedEncoding enumeration)}
    {index : Fin ledger.residueCount} {projection : SourceProjection}
    (binding : LedgerFischerChainBinding ledger index projection)
    (cover : LocantCover ledger) :
    canonicalFischerChainProjectionAt?
        (canonicalOutputWithFischerChain enumeration binding cover) index.val = some projection ∧
      canonicalFischerChainAnchorsAt?
          (canonicalOutputWithFischerChain enumeration binding cover) index.val =
        some (binding.carbons.map (encodedAtomEquiv request.graph enumeration).symm) ∧
      sourceDataResidueChannel?
          (canonicalOutputWithFischerChain enumeration binding cover) =
        some (sourceDataBoundChannel LocantCodec.nat enumeration request.graph ledger cover
          (canonicalSourceDataAt enumeration binding)
          (canonicalSourceDataAt_supported enumeration binding)) :=
  ⟨canonicalFischerChainProjectionAt?_canonicalOutputWithFischerChain enumeration binding cover,
    canonicalFischerChainAnchorsAt?_canonicalOutputWithFischerChain enumeration binding cover,
    canonicalOutputWithFischerChain_channel enumeration binding cover⟩

end

end CarbohydrateFischerChainIngress

end TetraStereo.OneCenter

/-! ## Kernel receipts -/

assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.projectionToSource_fromSource
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.projectionFromSource_toSource
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.projectionToSource_injective
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.projectionToSource_bijective
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.wellFormed_substituent_bounds
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.wellFormed_carbonyl_bounds
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.LedgerFischerChainBinding.get_mem_support
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.LedgerFischerChainBinding.substituent_resolves
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.LedgerFischerChainBinding.carbonyl_resolves
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.datumOfBinding_supported
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.annotationWithFischerChain_readback
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.appendFischerChainDatum_suffix_projection
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.fischerChainReadback_encodeFischerChainAt
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.encodeFischerChainAppendedAt_suffix_projection
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.emittedFischerChainSuffix?_encodeFischerChainAppendedAt
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.encodeFischerChainAppendedAt_recovery
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.canonicalSourceDataAt_supported
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.canonicalFischerChainProjectionAt?_canonicalOutputWithFischerChain
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.canonicalFischerChainAnchorsAt?_canonicalOutputWithFischerChain
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.canonicalOutputWithFischerChain_channel
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.canonicalFischerChainSuffixAt?_canonicalAppendedOutputWithFischerChain
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.canonicalAppendedOutputWithFischerChain_old_prefix
assert_kernel_only
  TetraStereo.OneCenter.CarbohydrateFischerChainIngress.canonicalOutputWithFischerChain_recovery
