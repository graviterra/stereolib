import TetraStereo.OneCenter.OrganicStereoFiniteEncoding
import TetraStereo.OneCenter.GraphicalRepresentationST1Special
import TetraStereo.OneCenter.GraphicalRepresentationST3to6
import TetraStereo.OneCenter.CarbohydrateFoundationStereochemistrySemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-! ## Local instances for the supplied crossing record

The IUPAC 2006 ST-3 source record `BondCrossing` is declared without `DecidableEq`/`Repr`
instances, and the source module is not modified.  The corresponding structural instances are
derived locally here so that crossing cues can be compared and printed like every other retained
convention payload.  These instances add no interpretation: all three source fields stay literal.
-/
deriving instance DecidableEq, Repr for IUPACDrawing2006.ST3.BondCrossing
































































































/-! ## Generic list/option round-trip helpers -/

/-- Mapping a list by `f` and then by a left inverse `g` recovers the list. -/
theorem list_map_map_of_leftInverse {α β : Type*} (f : α → β) (g : β → α)
    (leftInverse : ∀ value, g (f value) = value) (values : List α) :
    (values.map f).map g = values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [leftInverse head, inductionHypothesis]

/-- Mapping an optional value by `f` and then by a left inverse `g` recovers the value, including
the absent case. -/
theorem option_map_map_of_leftInverse {α β : Type*} (f : α → β) (g : β → α)
    (leftInverse : ∀ value, g (f value) = value) (value : Option α) :
    (value.map f).map g = value := by
  cases value with
  | none => rfl
  | some actual =>
      simp only [Option.map_some]
      rw [leftInverse actual]

/-! ## Convention vocabulary -/

/-- The explicitly declared two-dimensional projection convention.  `unspecified` records that a
source drawing exists without a declared convention; it is not an inference of any convention. -/
inductive ProjectionConvention where
  | fischer
  | haworth
  | mills
  | unspecified
  deriving DecidableEq, Repr

/-- The role of one atom in an ordered reference frame.  Roles are atom-independent tokens. -/
inductive ReferenceRole where
  | centre
  | ringOxygen
  | front
  | back
  | upper
  | lower
  | left
  | right
  | referenceAtom
  deriving DecidableEq, Repr

/-- One ordered reference-frame entry.  Only `atom` is moved by a relabelling; `role` is copied. -/
structure ReferenceEntry (V : Type*) where
  atom : V
  role : ReferenceRole
  deriving DecidableEq, Repr

namespace ReferenceEntry

variable {V W U : Type*}

/-- Move the atom reference; the role is unchanged. -/
def mapAtom (e : V ≃ W) (entry : ReferenceEntry V) : ReferenceEntry W where
  atom := e entry.atom
  role := entry.role

@[simp] theorem mapAtom_atom (e : V ≃ W) (entry : ReferenceEntry V) :
    (entry.mapAtom e).atom = e entry.atom := rfl

@[simp] theorem mapAtom_role (e : V ≃ W) (entry : ReferenceEntry V) :
    (entry.mapAtom e).role = entry.role := rfl

@[simp] theorem mapAtom_symm_mapAtom (e : V ≃ W) (entry : ReferenceEntry V) :
    (entry.mapAtom e).mapAtom e.symm = entry := by
  cases entry with
  | mk atom role => simp [mapAtom, Equiv.symm_apply_apply]

@[simp] theorem mapAtom_mapAtom_symm (e : V ≃ W) (entry : ReferenceEntry W) :
    (entry.mapAtom e.symm).mapAtom e = entry := by
  cases entry with
  | mk atom role => simp [mapAtom, Equiv.apply_symm_apply]

/-- Relabelling by the identity equivalence is the identity. -/
@[simp] theorem mapAtom_refl (entry : ReferenceEntry V) :
    entry.mapAtom (Equiv.refl V) = entry := by
  cases entry with
  | mk atom role => rfl

end ReferenceEntry

/-! ## Supplied bond glyphs

The structure below retains the *literal* supplied glyph payload.  In particular the written
endpoint order is `source` then `target`; the orientation record is copied whole, so its explicit
`narrowEnd` is not normalized into the source order; and the optional ST-0 `HashConvention`,
`WavyGeometry` and `BondPurpose` records are absent or present exactly as supplied.  No semantic
judgment, recommendation, suitability check or reverse-hash interpretation is stored. -/

/-- One supplied bond glyph over atom labels `V`.  `interactionIndex` is an occurrence position
carried as a plain numeral: this retention record does not claim that it is in bounds for any
particular graph, and it does not mention an interaction kind or arity.  The field order of
`source` and `target` is the supplied written order. -/
structure BondGlyph (V : Type*) where
  /-- The supplied source interaction occurrence position, retained as a numeral. -/
  interactionIndex : Nat
  /-- First endpoint in the supplied written order. -/
  source : V
  /-- Second endpoint in the supplied written order. -/
  target : V
  /-- The complete supplied orientation record: style and explicit narrow end. -/
  oriented : IUPACDrawing2006.ST0.OrientedBond
  /-- The supplied hash-convention token, absent or present exactly as supplied. -/
  hashConvention? : Option IUPACDrawing2006.ST0.HashConvention := none
  /-- The supplied wavy-geometry record, absent or present exactly as supplied. -/
  wavyGeometry? : Option IUPACDrawing2006.ST0.WavyGeometry := none
  /-- The supplied bond-purpose token, absent or present exactly as supplied. -/
  purpose? : Option IUPACDrawing2006.ST0.BondPurpose := none
  deriving DecidableEq, Repr

namespace BondGlyph

variable {V W : Type*}

/-- Move both endpoints through one external equivalence.  The occurrence index, the complete
orientation record (style and narrow end) and every optional source token are copied verbatim. -/
def mapAtom (e : V ≃ W) (glyph : BondGlyph V) : BondGlyph W where
  interactionIndex := glyph.interactionIndex
  source := e glyph.source
  target := e glyph.target
  oriented := glyph.oriented
  hashConvention? := glyph.hashConvention?
  wavyGeometry? := glyph.wavyGeometry?
  purpose? := glyph.purpose?

@[simp] theorem mapAtom_interactionIndex (e : V ≃ W) (glyph : BondGlyph V) :
    (glyph.mapAtom e).interactionIndex = glyph.interactionIndex := rfl

@[simp] theorem mapAtom_source (e : V ≃ W) (glyph : BondGlyph V) :
    (glyph.mapAtom e).source = e glyph.source := rfl

@[simp] theorem mapAtom_target (e : V ≃ W) (glyph : BondGlyph V) :
    (glyph.mapAtom e).target = e glyph.target := rfl

@[simp] theorem mapAtom_oriented (e : V ≃ W) (glyph : BondGlyph V) :
    (glyph.mapAtom e).oriented = glyph.oriented := rfl

@[simp] theorem mapAtom_hashConvention? (e : V ≃ W) (glyph : BondGlyph V) :
    (glyph.mapAtom e).hashConvention? = glyph.hashConvention? := rfl

@[simp] theorem mapAtom_wavyGeometry? (e : V ≃ W) (glyph : BondGlyph V) :
    (glyph.mapAtom e).wavyGeometry? = glyph.wavyGeometry? := rfl

@[simp] theorem mapAtom_purpose? (e : V ≃ W) (glyph : BondGlyph V) :
    (glyph.mapAtom e).purpose? = glyph.purpose? := rfl

/-- Presence of the optional hash-convention token is preserved exactly. -/
@[simp] theorem mapAtom_hashConvention?_isSome (e : V ≃ W) (glyph : BondGlyph V) :
    (glyph.mapAtom e).hashConvention?.isSome = glyph.hashConvention?.isSome := rfl

/-- Presence of the optional wavy-geometry record is preserved exactly. -/
@[simp] theorem mapAtom_wavyGeometry?_isSome (e : V ≃ W) (glyph : BondGlyph V) :
    (glyph.mapAtom e).wavyGeometry?.isSome = glyph.wavyGeometry?.isSome := rfl

/-- Presence of the optional bond-purpose token is preserved exactly. -/
@[simp] theorem mapAtom_purpose?_isSome (e : V ≃ W) (glyph : BondGlyph V) :
    (glyph.mapAtom e).purpose?.isSome = glyph.purpose?.isSome := rfl

/-- The two atom references in the supplied written order: `source` first, then `target`. -/
def atomReferences (glyph : BondGlyph V) : List V := [glyph.source, glyph.target]

@[simp] theorem atomReferences_length (glyph : BondGlyph V) :
    glyph.atomReferences.length = 2 := rfl

/-- The source endpoint is a reference of the glyph. -/
@[simp] theorem source_mem_atomReferences (glyph : BondGlyph V) :
    glyph.source ∈ glyph.atomReferences := by
  simp [atomReferences]

/-- The target endpoint is a reference of the glyph. -/
@[simp] theorem target_mem_atomReferences (glyph : BondGlyph V) :
    glyph.target ∈ glyph.atomReferences := by
  simp [atomReferences]

/-- Relabelling acts elementwise on the ordered reference list.  Order and multiplicity are
retained. -/
@[simp] theorem atomReferences_mapAtom (e : V ≃ W) (glyph : BondGlyph V) :
    (glyph.mapAtom e).atomReferences = glyph.atomReferences.map e := by
  simp [atomReferences, mapAtom]

@[simp] theorem mapAtom_symm_mapAtom (e : V ≃ W) (glyph : BondGlyph V) :
    (glyph.mapAtom e).mapAtom e.symm = glyph := by
  cases glyph with
  | mk interactionIndex source target oriented hashConvention wavyGeometry purpose =>
      simp [mapAtom, Equiv.symm_apply_apply]

@[simp] theorem mapAtom_mapAtom_symm (e : V ≃ W) (glyph : BondGlyph W) :
    (glyph.mapAtom e.symm).mapAtom e = glyph := by
  cases glyph with
  | mk interactionIndex source target oriented hashConvention wavyGeometry purpose =>
      simp [mapAtom, Equiv.apply_symm_apply]

/-- Relabelling by the identity equivalence is the identity. -/
@[simp] theorem mapAtom_refl (glyph : BondGlyph V) :
    glyph.mapAtom (Equiv.refl V) = glyph := by
  cases glyph with
  | mk interactionIndex source target oriented hashConvention wavyGeometry purpose => rfl

end BondGlyph

/-! ## Supplied bond-crossing payloads

An ST-3 crossing is an ordered pair of supplied bond-glyph occurrences.  `firstCueIndex` and
`secondCueIndex` are positions in the *containing ordered convention cue list*, never atom labels
and never interaction-occurrence indexes.  The two `BondGlyph` payloads and the complete source
`IUPACDrawing2006.ST3.BondCrossing` record are retained literally.  In particular the source
`Bool` discontinuity flag, the exact rational `discontinuityWidthRatio` and the ordering-conflict
flag are copied verbatim; no recommendation, no `UnambiguousCrossing` condition, no derived depth
authority and no chemical applicability judgment is required or stored. -/

/-- One supplied crossing between two ordered retained bond glyphs. -/
structure BondCrossingGlyph (V : Type*) where
  /-- Position of the first crossing glyph in the containing ordered cue list. -/
  firstCueIndex : Nat
  /-- Position of the second crossing glyph in the containing ordered cue list. -/
  secondCueIndex : Nat
  /-- First supplied bond glyph of the ordered crossing pair. -/
  first : BondGlyph V
  /-- Second supplied bond glyph of the ordered crossing pair. -/
  second : BondGlyph V
  /-- The complete source ST-3 crossing record, retained literally. -/
  crossing : IUPACDrawing2006.ST3.BondCrossing
  deriving DecidableEq, Repr

namespace BondCrossingGlyph

variable {V W : Type*}

/-- Move both supplied glyphs of the pair through one external equivalence.  Both cue indices and
the complete source crossing record are copied verbatim, so order, multiplicity and every source
field survive. -/
def mapAtom (e : V ≃ W) (pair : BondCrossingGlyph V) : BondCrossingGlyph W where
  firstCueIndex := pair.firstCueIndex
  secondCueIndex := pair.secondCueIndex
  first := pair.first.mapAtom e
  second := pair.second.mapAtom e
  crossing := pair.crossing

@[simp] theorem mapAtom_firstCueIndex (e : V ≃ W) (pair : BondCrossingGlyph V) :
    (pair.mapAtom e).firstCueIndex = pair.firstCueIndex := rfl

@[simp] theorem mapAtom_secondCueIndex (e : V ≃ W) (pair : BondCrossingGlyph V) :
    (pair.mapAtom e).secondCueIndex = pair.secondCueIndex := rfl

@[simp] theorem mapAtom_first (e : V ≃ W) (pair : BondCrossingGlyph V) :
    (pair.mapAtom e).first = pair.first.mapAtom e := rfl

@[simp] theorem mapAtom_second (e : V ≃ W) (pair : BondCrossingGlyph V) :
    (pair.mapAtom e).second = pair.second.mapAtom e := rfl

@[simp] theorem mapAtom_crossing (e : V ≃ W) (pair : BondCrossingGlyph V) :
    (pair.mapAtom e).crossing = pair.crossing := rfl

@[simp] theorem mapAtom_symm_mapAtom (e : V ≃ W) (pair : BondCrossingGlyph V) :
    (pair.mapAtom e).mapAtom e.symm = pair := by
  cases pair with
  | mk firstCueIndex secondCueIndex first second crossing =>
      simp [mapAtom]

@[simp] theorem mapAtom_mapAtom_symm (e : V ≃ W) (pair : BondCrossingGlyph W) :
    (pair.mapAtom e.symm).mapAtom e = pair := by
  cases pair with
  | mk firstCueIndex secondCueIndex first second crossing =>
      simp [mapAtom]

/-- Relabelling by the identity equivalence is the identity. -/
@[simp] theorem mapAtom_refl (pair : BondCrossingGlyph V) :
    pair.mapAtom (Equiv.refl V) = pair := by
  cases pair with
  | mk firstCueIndex secondCueIndex first second crossing => rfl

end BondCrossingGlyph

/-- One typed convention cue.  Atom positions are `V`-labelled; every other payload is exactly an
existing source enum or carrier.  A cue never stores a recommendation, a configuration effect, a
descriptor or any derived geometry. -/
inductive ConventionCue (V : Type*) where
  /-- Fischer centre: the labelled atom, its explicit source locant, the paper-depth geometry,
  the horizontal hydroxy side, and the existing Fischer applicability domain. -/
  | fischerCenter (atom : V) (locant : Nat)
      (geometry : Carbohydrate1996Foundation.FischerCenterGeometry)
      (hydroxySide : Carbohydrate1996Foundation.HorizontalSide)
      (domain : IUPACDrawing2006.ST1Special.FischerDomain)
  /-- The quarter-turn datum of a Fischer drawing.  It is retained as a token; the source
  `fischerRotationEffect` is not applied. -/
  | fischerRotation (turn : IUPACDrawing2006.ST1Special.QuarterTurn)
  /-- Haworth ring: reference atom, source orientation, numbering sense computed by the source
  function, ring-closure locants, and the existing depiction record. -/
  | haworthRing (reference : V)
      (orientation : Carbohydrate1996Foundation.HaworthOrientation)
      (numbering : Carbohydrate1996Foundation.NumberingSense)
      (closure : Carbohydrate1996Foundation.RingClosureLocants)
      (depiction : IUPACDrawing2006.ST1Special.HaworthDepiction)
  /-- One Haworth substituent side marker. -/
  | haworthSubstituent (atom : V) (side : Carbohydrate1996Foundation.HaworthSide)
  /-- One Mills bond marker.  `MillsBond` is the only atom-level Mills data carrier in the source. -/
  | millsBond (atom : V) (bond : Carbohydrate1996Foundation.MillsBond)
  /-- An explicit non-tetrahedral reference cue.  Only the existing geometry enum is retained;
  no formal-meaning interpretation is derived. -/
  | nonTetrahedralReference (atom : V)
      (geometry : IUPACDrawing2006.ST1.NonTetrahedralGeometry)
  /-- One supplied bond glyph: literal written endpoint order, complete `OrientedBond` record
  (including its explicit narrow end), and the optional source hash/wavy/purpose records. -/
  | bondGlyph (glyph : BondGlyph V)
  /-- One supplied crossing between two ordered retained bond glyphs.  The two cue indexes are
  positions in the containing ordered convention cue list; the two glyphs and the complete ST-3
  crossing record are retained literally. -/
  | bondCrossing (crossing : BondCrossingGlyph V)
  deriving DecidableEq, Repr

namespace ConventionCue

variable {V W U : Type*}

/-- The optional *single-atom focus* of a cue.  `none` means that the cue does not name exactly one
atom; it does not mean that the cue carries no atom references.  In particular a `bondGlyph` cue
has two ordered references and a `bondCrossing` cue has the concatenated ordered references of
both glyphs (see `atomReferences`), so neither has a single-atom focus. -/
def atom? : ConventionCue V → Option V
  | .fischerCenter atom _ _ _ _ => some atom
  | .fischerRotation _ => none
  | .haworthRing reference _ _ _ _ => some reference
  | .haworthSubstituent atom _ => some atom
  | .millsBond atom _ => some atom
  | .nonTetrahedralReference atom _ => some atom
  | .bondGlyph _ => none
  | .bondCrossing _ => none

/-- Every atom reference carried by a cue, in the cue's own order.  A unary cue returns a
singleton, `fischerRotation` returns the empty list, and `bondGlyph` returns `[source, target]` in
exactly the supplied written order.  A `bondCrossing` returns the concatenation of the two glyphs'
reference lists, first then second.  This is deliberately separate from `atom?`: `atom? = none`
records the absence of a unique single-atom focus, not the absence of references. -/
def atomReferences : ConventionCue V → List V
  | .fischerCenter atom _ _ _ _ => [atom]
  | .fischerRotation _ => []
  | .haworthRing reference _ _ _ _ => [reference]
  | .haworthSubstituent atom _ => [atom]
  | .millsBond atom _ => [atom]
  | .nonTetrahedralReference atom _ => [atom]
  | .bondGlyph glyph => [glyph.source, glyph.target]
  | .bondCrossing crossing =>
      crossing.first.atomReferences ++ crossing.second.atomReferences

/-- The explicit non-atom indexes carried by a cue.  These are `Nat` locants, not atom labels and
not interaction-occurrence indexes.  A `bondGlyph` has no locant field; its source occurrence index
is retained separately inside the `BondGlyph`. -/
def locants : ConventionCue V → List Nat
  | .fischerCenter _ locant _ _ _ => [locant]
  | .haworthRing _ _ _ closure _ =>
      [closure.carbonylLocant, closure.hydroxyLocant]
  | _ => []

/-- The Haworth numbering sense stored by a ring cue, if any. -/
def haworthNumbering? :
    ConventionCue V → Option Carbohydrate1996Foundation.NumberingSense
  | .haworthRing _ _ numbering _ _ => some numbering
  | _ => none

/-- Relabel exactly the atom references.  Locants, roles, enums and every carrier payload are
copied verbatim.  For a bond glyph both endpoints move through the same equivalence and the
written order, occurrence index, orientation record and optional tokens are unchanged.  For a
bond crossing both glyphs move through that same equivalence, while both cue indexes and the
whole source crossing record are unchanged. -/
def mapAtom (e : V ≃ W) : ConventionCue V → ConventionCue W
  | .fischerCenter atom locant geometry hydroxySide domain =>
      .fischerCenter (e atom) locant geometry hydroxySide domain
  | .fischerRotation turn => .fischerRotation turn
  | .haworthRing reference orientation numbering closure depiction =>
      .haworthRing (e reference) orientation numbering closure depiction
  | .haworthSubstituent atom side => .haworthSubstituent (e atom) side
  | .millsBond atom bond => .millsBond (e atom) bond
  | .nonTetrahedralReference atom geometry =>
      .nonTetrahedralReference (e atom) geometry
  | .bondGlyph glyph => .bondGlyph (glyph.mapAtom e)
  | .bondCrossing crossing => .bondCrossing (crossing.mapAtom e)

@[simp] theorem atom?_mapAtom (e : V ≃ W) (cue : ConventionCue V) :
    (cue.mapAtom e).atom? = cue.atom?.map e := by
  cases cue <;> simp [atom?, mapAtom]

@[simp] theorem atomReferences_mapAtom (e : V ≃ W) (cue : ConventionCue V) :
    (cue.mapAtom e).atomReferences = cue.atomReferences.map e := by
  cases cue <;> simp [atomReferences, mapAtom]

@[simp] theorem locants_mapAtom (e : V ≃ W) (cue : ConventionCue V) :
    (cue.mapAtom e).locants = cue.locants := by
  cases cue <;> simp [locants, mapAtom]

@[simp] theorem haworthNumbering?_mapAtom (e : V ≃ W) (cue : ConventionCue V) :
    (cue.mapAtom e).haworthNumbering? = cue.haworthNumbering? := by
  cases cue <;> simp [haworthNumbering?, mapAtom]

@[simp] theorem atom?_bondGlyph (glyph : BondGlyph V) :
    (bondGlyph glyph).atom? = none := rfl

@[simp] theorem atomReferences_bondGlyph (glyph : BondGlyph V) :
    (bondGlyph glyph).atomReferences = [glyph.source, glyph.target] := rfl

/-- Relabelling a bond-glyph cue moves both endpoints through the same equivalence and leaves the
occurrence index, orientation record and optional tokens unchanged. -/
@[simp] theorem mapAtom_bondGlyph (e : V ≃ W) (glyph : BondGlyph V) :
    mapAtom e (bondGlyph glyph) = bondGlyph (glyph.mapAtom e) := rfl

@[simp] theorem locants_bondGlyph (glyph : BondGlyph V) :
    (bondGlyph glyph).locants = [] := rfl

@[simp] theorem haworthNumbering?_bondGlyph (glyph : BondGlyph V) :
    (bondGlyph glyph).haworthNumbering? = none := rfl

@[simp] theorem atom?_bondCrossing (crossing : BondCrossingGlyph V) :
    (bondCrossing crossing).atom? = none := rfl

/-- A crossing cue references both glyphs' ordered endpoint lists, first then second. -/
@[simp] theorem atomReferences_bondCrossing (crossing : BondCrossingGlyph V) :
    (bondCrossing crossing).atomReferences =
      crossing.first.atomReferences ++ crossing.second.atomReferences := rfl

/-- Relabelling a crossing cue reindexes both glyphs through the same equivalence and leaves both
cue indexes and the complete source crossing record unchanged. -/
@[simp] theorem mapAtom_bondCrossing (e : V ≃ W) (crossing : BondCrossingGlyph V) :
    mapAtom e (bondCrossing crossing) = bondCrossing (crossing.mapAtom e) := rfl

@[simp] theorem locants_bondCrossing (crossing : BondCrossingGlyph V) :
    (bondCrossing crossing).locants = [] := rfl

@[simp] theorem haworthNumbering?_bondCrossing (crossing : BondCrossingGlyph V) :
    (bondCrossing crossing).haworthNumbering? = none := rfl

/-- A `bondCrossing` has no single-atom focus but does carry the two glyphs' ordered references. -/
theorem bondCrossing_atom?_none_and_references_ne_nil (crossing : BondCrossingGlyph V) :
    (bondCrossing crossing).atom? = none ∧ (bondCrossing crossing).atomReferences ≠ [] := by
  simp [atomReferences, BondGlyph.atomReferences]

/-- The `bondCrossing` constructor is injective, so distinct crossing payloads remain distinct
cues even when all their glyph fields and scalar indexes coincide. -/
theorem bondCrossing_injective :
    Function.Injective
      (ConventionCue.bondCrossing : BondCrossingGlyph V → ConventionCue V) := by
  intro first second equal
  cases equal
  rfl

/-- A `bondGlyph` has no single-atom focus but does carry two ordered references.  Thus
`atom? = none` must not be read as "no references". -/
theorem atom?_none_and_references_ne_nil (glyph : BondGlyph V) :
    (bondGlyph glyph).atom? = none ∧ (bondGlyph glyph).atomReferences ≠ [] := by
  simp

/-- A cue with a single-atom focus has exactly that atom as its ordered reference list. -/
theorem atomReferences_eq_singleton_of_atom? (cue : ConventionCue V) {atom : V}
    (observed : cue.atom? = some atom) :
    cue.atomReferences = [atom] := by
  cases cue <;> simp_all [atom?, atomReferences]

/-- The `bondGlyph` constructor is injective, so distinct supplied glyph payloads remain distinct
cues even when their legacy projection fields coincide. -/
theorem bondGlyph_injective :
    Function.Injective (ConventionCue.bondGlyph : BondGlyph V → ConventionCue V) := by
  intro first second equal
  cases equal
  rfl

@[simp] theorem mapAtom_symm_mapAtom (e : V ≃ W) (cue : ConventionCue V) :
    (cue.mapAtom e).mapAtom e.symm = cue := by
  cases cue <;> simp [mapAtom, Equiv.symm_apply_apply]

@[simp] theorem mapAtom_mapAtom_symm (e : V ≃ W) (cue : ConventionCue W) :
    (cue.mapAtom e.symm).mapAtom e = cue := by
  cases cue <;> simp [mapAtom, Equiv.apply_symm_apply]

end ConventionCue

/-! ## The V-labelled source record -/

/-- Independently supplied drawing-convention evidence over atom labels `V`.  Every optional
channel distinguishes absence from present-but-empty.  `scope?` carries the existing configuration
scope enum, so `relative n` and `racemic n` group identifiers survive unchanged. -/
structure OrganicConventionSource (V : Type*) where
  /-- Explicitly declared projection convention, if any. -/
  convention? : Option ProjectionConvention := none
  /-- Configuration scope, including any relative/racemic group number. -/
  scope? : Option DiagramConfigurationScope := none
  /-- Ordered reference frame.  `none` is absence; `some []` is a present empty frame. -/
  referenceFrame? : Option (List (ReferenceEntry V)) := none
  /-- Ordered convention cues.  `none` is absence; `some []` is a present empty cue list. -/
  cues? : Option (List (ConventionCue V)) := none
  deriving DecidableEq, Repr

namespace OrganicConventionSource

variable {V W U : Type*}

/-- Move every atom reference through one external equivalence.  All atom-independent fields are
copied: convention, scope/group, order, multiplicity, locants, and carrier payloads. -/
def mapAtom (e : V ≃ W) (source : OrganicConventionSource V) : OrganicConventionSource W where
  convention? := source.convention?
  scope? := source.scope?
  referenceFrame? := source.referenceFrame?.map (List.map (ReferenceEntry.mapAtom e))
  cues? := source.cues?.map (List.map (ConventionCue.mapAtom e))

@[simp] theorem mapAtom_convention? (e : V ≃ W) (source : OrganicConventionSource V) :
    (source.mapAtom e).convention? = source.convention? := rfl

@[simp] theorem mapAtom_scope? (e : V ≃ W) (source : OrganicConventionSource V) :
    (source.mapAtom e).scope? = source.scope? := rfl

@[simp] theorem mapAtom_referenceFrame? (e : V ≃ W) (source : OrganicConventionSource V) :
    (source.mapAtom e).referenceFrame? =
      source.referenceFrame?.map (List.map (ReferenceEntry.mapAtom e)) := rfl

@[simp] theorem mapAtom_cues? (e : V ≃ W) (source : OrganicConventionSource V) :
    (source.mapAtom e).cues? =
      source.cues?.map (List.map (ConventionCue.mapAtom e)) := rfl

@[simp] theorem mapAtom_symm_mapAtom (e : V ≃ W) (source : OrganicConventionSource V) :
    (source.mapAtom e).mapAtom e.symm = source := by
  obtain ⟨convention?, scope?, referenceFrame?, cues?⟩ := source
  simp only [mapAtom]
  have referenceFrameRoundtrip :
      Option.map (List.map (ReferenceEntry.mapAtom e.symm))
          (Option.map (List.map (ReferenceEntry.mapAtom e)) referenceFrame?) =
        referenceFrame? :=
    option_map_map_of_leftInverse (f := List.map (ReferenceEntry.mapAtom e))
      (g := List.map (ReferenceEntry.mapAtom e.symm))
      (leftInverse := fun entries =>
        list_map_map_of_leftInverse (f := ReferenceEntry.mapAtom e)
          (g := ReferenceEntry.mapAtom e.symm)
          (leftInverse := fun entry => ReferenceEntry.mapAtom_symm_mapAtom e entry)
          entries)
      referenceFrame?
  have cuesRoundtrip :
      Option.map (List.map (ConventionCue.mapAtom e.symm))
          (Option.map (List.map (ConventionCue.mapAtom e)) cues?) =
        cues? :=
    option_map_map_of_leftInverse (f := List.map (ConventionCue.mapAtom e))
      (g := List.map (ConventionCue.mapAtom e.symm))
      (leftInverse := fun entries =>
        list_map_map_of_leftInverse (f := ConventionCue.mapAtom e)
          (g := ConventionCue.mapAtom e.symm)
          (leftInverse := fun cue => ConventionCue.mapAtom_symm_mapAtom e cue)
          entries)
      cues?
  rw [referenceFrameRoundtrip, cuesRoundtrip]

@[simp] theorem mapAtom_mapAtom_symm (e : V ≃ W) (source : OrganicConventionSource W) :
    (source.mapAtom e.symm).mapAtom e = source := by
  obtain ⟨convention?, scope?, referenceFrame?, cues?⟩ := source
  simp only [mapAtom]
  have referenceFrameRoundtrip :
      Option.map (List.map (ReferenceEntry.mapAtom e))
          (Option.map (List.map (ReferenceEntry.mapAtom e.symm)) referenceFrame?) =
        referenceFrame? :=
    option_map_map_of_leftInverse (f := List.map (ReferenceEntry.mapAtom e.symm))
      (g := List.map (ReferenceEntry.mapAtom e))
      (leftInverse := fun entries =>
        list_map_map_of_leftInverse (f := ReferenceEntry.mapAtom e.symm)
          (g := ReferenceEntry.mapAtom e)
          (leftInverse := fun entry => ReferenceEntry.mapAtom_mapAtom_symm e entry)
          entries)
      referenceFrame?
  have cuesRoundtrip :
      Option.map (List.map (ConventionCue.mapAtom e))
          (Option.map (List.map (ConventionCue.mapAtom e.symm)) cues?) =
        cues? :=
    option_map_map_of_leftInverse (f := List.map (ConventionCue.mapAtom e.symm))
      (g := List.map (ConventionCue.mapAtom e))
      (leftInverse := fun entries =>
        list_map_map_of_leftInverse (f := ConventionCue.mapAtom e.symm)
          (g := ConventionCue.mapAtom e)
          (leftInverse := fun cue => ConventionCue.mapAtom_mapAtom_symm e cue)
          entries)
      cues?
  rw [referenceFrameRoundtrip, cuesRoundtrip]

/-- Encode the source under an external atom equivalence `e : V ≃ W`. -/
def encode (e : V ≃ W) (source : OrganicConventionSource V) : OrganicConventionSource W :=
  source.mapAtom e

/-- Decode an encoded record using the same external equivalence. -/
def decode (e : V ≃ W) (encoded : OrganicConventionSource W) : OrganicConventionSource V :=
  encoded.mapAtom e.symm

/-- Decoder recovery: decoding an encoded source recovers every field exactly. -/
@[simp] theorem decode_encode (e : V ≃ W) (source : OrganicConventionSource V) :
    decode e (encode e source) = source :=
  mapAtom_symm_mapAtom e source

/-- Encoding is a right inverse of decoding. -/
@[simp] theorem encode_decode (e : V ≃ W) (source : OrganicConventionSource W) :
    encode e (decode e source) = source :=
  mapAtom_mapAtom_symm e source

/-- The encoding is an equivalence of source records.  Only atom references move. -/
def encodeEquiv (e : V ≃ W) : OrganicConventionSource V ≃ OrganicConventionSource W where
  toFun := encode e
  invFun := decode e
  left_inv := decode_encode e
  right_inv := encode_decode e

@[simp] theorem encodeEquiv_apply (e : V ≃ W) (source : OrganicConventionSource V) :
    encodeEquiv e source = encode e source := rfl

/-- The encoding function is injective. -/
theorem encode_injective (e : V ≃ W) : Function.Injective (encode e) := by
  intro first second equal
  have applied := congrArg (decode e) equal
  simpa [decode_encode e first, decode_encode e second] using applied

/-! ### Field and absence retention -/

@[simp] theorem encode_convention? (e : V ≃ W) (source : OrganicConventionSource V) :
    (encode e source).convention? = source.convention? := rfl

@[simp] theorem encode_scope? (e : V ≃ W) (source : OrganicConventionSource V) :
    (encode e source).scope? = source.scope? := rfl

@[simp] theorem encode_referenceFrame? (e : V ≃ W) (source : OrganicConventionSource V) :
    (encode e source).referenceFrame? =
      source.referenceFrame?.map (List.map (ReferenceEntry.mapAtom e)) := rfl

@[simp] theorem encode_cues? (e : V ≃ W) (source : OrganicConventionSource V) :
    (encode e source).cues? =
      source.cues?.map (List.map (ConventionCue.mapAtom e)) := rfl

/-- A supplied bond-glyph cue survives encoding with both endpoints moved by the same equivalence
and every other payload copied exactly. -/
@[simp] theorem encode_cue_bondGlyph (e : V ≃ W) (glyph : BondGlyph V) :
    ConventionCue.mapAtom e (ConventionCue.bondGlyph glyph) =
      ConventionCue.bondGlyph (glyph.mapAtom e) := rfl

/-- The convention channel is present after encoding exactly when it was present before. -/
@[simp] theorem encode_convention?_isSome (e : V ≃ W) (source : OrganicConventionSource V) :
    (encode e source).convention?.isSome = source.convention?.isSome := rfl

/-- The scope/group channel is present after encoding exactly when it was present before. -/
@[simp] theorem encode_scope?_isSome (e : V ≃ W) (source : OrganicConventionSource V) :
    (encode e source).scope?.isSome = source.scope?.isSome := rfl

/-- The reference-frame channel is present after encoding exactly when it was present before. -/
@[simp] theorem encode_referenceFrame?_isSome (e : V ≃ W)
    (source : OrganicConventionSource V) :
    (encode e source).referenceFrame?.isSome = source.referenceFrame?.isSome := by
  simp [encode, mapAtom]

/-- The cue channel is present after encoding exactly when it was present before. -/
@[simp] theorem encode_cues?_isSome (e : V ≃ W) (source : OrganicConventionSource V) :
    (encode e source).cues?.isSome = source.cues?.isSome := by
  simp [encode, mapAtom]

/-- Absence of the reference frame is preserved exactly. -/
@[simp] theorem encode_referenceFrame?_eq_none_iff (e : V ≃ W)
    (source : OrganicConventionSource V) :
    (encode e source).referenceFrame? = none ↔ source.referenceFrame? = none := by
  simp [encode, mapAtom]

/-- Absence of the cue channel is preserved exactly. -/
@[simp] theorem encode_cues?_eq_none_iff (e : V ≃ W) (source : OrganicConventionSource V) :
    (encode e source).cues? = none ↔ source.cues? = none := by
  simp [encode, mapAtom]

/-- A Fischer or Haworth group identifier carried by a relative scope is retained verbatim. -/
theorem encode_scope?_relative (e : V ≃ W) (source : OrganicConventionSource V)
    (group : Nat) (observed : source.scope? = some (.relative group)) :
    (encode e source).scope? = some (.relative group) := by
  change (source.mapAtom e).scope? = some (.relative group)
  simp [mapAtom_scope?, observed]

/-- A racemic group identifier carried by a racemic scope is retained verbatim. -/
theorem encode_scope?_racemic (e : V ≃ W) (source : OrganicConventionSource V)
    (group : Nat) (observed : source.scope? = some (.racemic group)) :
    (encode e source).scope? = some (.racemic group) := by
  change (source.mapAtom e).scope? = some (.racemic group)
  simp [mapAtom_scope?, observed]

end OrganicConventionSource

/-! ## Adapters from existing Fischer, Haworth and Mills carrier data -/

/-- A Fischer carrier: a labelled centre, the actual `ChiralCenter` (locant plus horizontal
hydroxy side), the actual paper-depth geometry, and the actual Fischer applicability domain. -/
structure FischerCarrier (V : Type*) where
  atom : V
  chiralCenter : Carbohydrate1996Foundation.ChiralCenter
  geometry : Carbohydrate1996Foundation.FischerCenterGeometry
  domain : IUPACDrawing2006.ST1Special.FischerDomain
  deriving DecidableEq, Repr

namespace FischerCarrier

variable {V W : Type*}

/-- Adapt actual Fischer carrier data into one typed cue.  The locant and hydroxy side are copied
from `ChiralCenter`; no locant is interpreted as an atom label. -/
def toCue (carrier : FischerCarrier V) : ConventionCue V :=
  .fischerCenter carrier.atom carrier.chiralCenter.locant carrier.geometry
    carrier.chiralCenter.hydroxySide carrier.domain

/-- Recover a Fischer carrier from a cue, if the cue is a Fischer-centre cue. -/
def ofCue? : ConventionCue V → Option (FischerCarrier V)
  | .fischerCenter atom locant geometry hydroxySide domain =>
      some { atom := atom
             chiralCenter := { locant := locant, hydroxySide := hydroxySide }
             geometry := geometry
             domain := domain }
  | _ => none

/-- Move the labelled centre; every source carrier field is unchanged. -/
def mapAtom (e : V ≃ W) (carrier : FischerCarrier V) : FischerCarrier W :=
  { carrier with atom := e carrier.atom }

/-- The adapter and its recovery are mutually inverse on carrier data. -/
@[simp] theorem ofCue?_toCue (carrier : FischerCarrier V) :
    ofCue? (toCue carrier) = some carrier := by
  obtain ⟨atom, ⟨locant, hydroxySide⟩, geometry, domain⟩ := carrier
  rfl

/-- Adapter recovery after relabelling the centre. -/
@[simp] theorem ofCue?_mapAtom_toCue (e : V ≃ W) (carrier : FischerCarrier V) :
    ofCue? (ConventionCue.mapAtom e (toCue carrier)) = some (carrier.mapAtom e) := by
  obtain ⟨atom, ⟨locant, hydroxySide⟩, geometry, domain⟩ := carrier
  rfl

/-- The cue names exactly the carrier's labelled centre. -/
@[simp] theorem toCue_atom? (carrier : FischerCarrier V) :
    (toCue carrier).atom? = some carrier.atom := rfl

/-- The cue's only atom reference is the labelled centre. -/
@[simp] theorem toCue_atomReferences (carrier : FischerCarrier V) :
    (toCue carrier).atomReferences = [carrier.atom] := rfl

/-- The cue's only non-atom index is the source locant. -/
@[simp] theorem toCue_locants (carrier : FischerCarrier V) :
    (toCue carrier).locants = [carrier.chiralCenter.locant] := rfl

end FischerCarrier

/-- A Haworth carrier built from actual source data. -/
structure HaworthCarrier (V : Type*) where
  reference : V
  orientation : Carbohydrate1996Foundation.HaworthOrientation
  closure : Carbohydrate1996Foundation.RingClosureLocants
  depiction : IUPACDrawing2006.ST1Special.HaworthDepiction
  deriving DecidableEq, Repr

namespace HaworthCarrier

variable {V W : Type*}

/-- Adapt actual Haworth data.  The numbering sense is the source function
`haworthNumberingSense` applied to the stored orientation. -/
def toCue (carrier : HaworthCarrier V) : ConventionCue V :=
  .haworthRing carrier.reference carrier.orientation
    (Carbohydrate1996Foundation.haworthNumberingSense carrier.orientation)
    carrier.closure carrier.depiction

/-- Recover a Haworth carrier.  The numbering sense is recomputed from the recovered orientation,
so no independent numbering field is invented. -/
def ofCue? : ConventionCue V → Option (HaworthCarrier V)
  | .haworthRing reference orientation _ closure depiction =>
      some { reference := reference
             orientation := orientation
             closure := closure
             depiction := depiction }
  | _ => none

/-- Move only the labelled reference atom. -/
def mapAtom (e : V ≃ W) (carrier : HaworthCarrier V) : HaworthCarrier W :=
  { carrier with reference := e carrier.reference }

/-- Adapter and recovery are mutually inverse on Haworth carrier data. -/
@[simp] theorem ofCue?_toCue (carrier : HaworthCarrier V) :
    ofCue? (toCue carrier) = some carrier := by
  obtain ⟨reference, orientation, closure, depiction⟩ := carrier
  rfl

/-- Adapter recovery after relabelling the reference atom. -/
@[simp] theorem ofCue?_mapAtom_toCue (e : V ≃ W) (carrier : HaworthCarrier V) :
    ofCue? (ConventionCue.mapAtom e (toCue carrier)) = some (carrier.mapAtom e) := by
  obtain ⟨reference, orientation, closure, depiction⟩ := carrier
  rfl

/-- The retained numbering sense is exactly the source function applied to the retained
orientation. -/
@[simp] theorem toCue_numbering (carrier : HaworthCarrier V) :
    (toCue carrier).haworthNumbering? =
      some (Carbohydrate1996Foundation.haworthNumberingSense carrier.orientation) := rfl

/-- The cue's only atom reference is the labelled reference atom. -/
@[simp] theorem toCue_atomReferences (carrier : HaworthCarrier V) :
    (toCue carrier).atomReferences = [carrier.reference] := rfl

/-- The cue's only non-atom indexes are the two ring-closure locants. -/
@[simp] theorem toCue_locants (carrier : HaworthCarrier V) :
    (toCue carrier).locants =
      [carrier.closure.carbonylLocant, carrier.closure.hydroxyLocant] := rfl

end HaworthCarrier

/-- A Mills carrier.  `MillsBond` is the only atom-level Mills data carrier in the source; the
paper-plane and wedge restrictions are `Prop`-valued policies and are not data here. -/
structure MillsCarrier (V : Type*) where
  atom : V
  bond : Carbohydrate1996Foundation.MillsBond
  deriving DecidableEq, Repr

namespace MillsCarrier

variable {V W : Type*}

/-- Adapt actual Mills bond data. -/
def toCue (carrier : MillsCarrier V) : ConventionCue V :=
  .millsBond carrier.atom carrier.bond

/-- Recover a Mills carrier, if the cue is a Mills cue. -/
def ofCue? : ConventionCue V → Option (MillsCarrier V)
  | .millsBond atom bond => some { atom := atom, bond := bond }
  | _ => none

/-- Move only the labelled atom. -/
def mapAtom (e : V ≃ W) (carrier : MillsCarrier V) : MillsCarrier W :=
  { carrier with atom := e carrier.atom }

/-- Adapter and recovery are mutually inverse on Mills carrier data. -/
@[simp] theorem ofCue?_toCue (carrier : MillsCarrier V) :
    ofCue? (toCue carrier) = some carrier := by
  obtain ⟨atom, bond⟩ := carrier
  rfl

/-- Adapter recovery after relabelling the atom. -/
@[simp] theorem ofCue?_mapAtom_toCue (e : V ≃ W) (carrier : MillsCarrier V) :
    ofCue? (ConventionCue.mapAtom e (toCue carrier)) = some (carrier.mapAtom e) := by
  obtain ⟨atom, bond⟩ := carrier
  rfl

/-- The cue's only atom reference is the labelled atom. -/
@[simp] theorem toCue_atomReferences (carrier : MillsCarrier V) :
    (toCue carrier).atomReferences = [carrier.atom] := rfl

/-- The side meaning available from the source is retained: it is computed by the existing
`millsSide` function, not invented by this channel. -/
theorem ofCue?_toCue_side (carrier : MillsCarrier V) :
    (ofCue? (toCue carrier)).map
        (fun recovered => Carbohydrate1996Foundation.millsSide recovered.bond) =
      some (Carbohydrate1996Foundation.millsSide carrier.bond) := by
  obtain ⟨atom, bond⟩ := carrier
  rfl

end MillsCarrier

/-- A non-tetrahedral reference carrier: an atom label and the existing geometry enum. -/
structure NonTetrahedralCarrier (V : Type*) where
  atom : V
  geometry : IUPACDrawing2006.ST1.NonTetrahedralGeometry
  deriving DecidableEq, Repr

namespace NonTetrahedralCarrier

variable {V W : Type*}

/-- Adapt an explicit non-tetrahedral reference cue. -/
def toCue (carrier : NonTetrahedralCarrier V) : ConventionCue V :=
  .nonTetrahedralReference carrier.atom carrier.geometry

/-- Recover a non-tetrahedral carrier, if the cue is one. -/
def ofCue? : ConventionCue V → Option (NonTetrahedralCarrier V)
  | .nonTetrahedralReference atom geometry =>
      some { atom := atom, geometry := geometry }
  | _ => none

/-- Move only the labelled atom. -/
def mapAtom (e : V ≃ W) (carrier : NonTetrahedralCarrier V) : NonTetrahedralCarrier W :=
  { carrier with atom := e carrier.atom }

@[simp] theorem ofCue?_toCue (carrier : NonTetrahedralCarrier V) :
    ofCue? (toCue carrier) = some carrier := by
  obtain ⟨atom, geometry⟩ := carrier
  rfl

@[simp] theorem ofCue?_mapAtom_toCue (e : V ≃ W) (carrier : NonTetrahedralCarrier V) :
    ofCue? (ConventionCue.mapAtom e (toCue carrier)) = some (carrier.mapAtom e) := by
  obtain ⟨atom, geometry⟩ := carrier
  rfl

/-- The cue's only atom reference is the labelled atom. -/
@[simp] theorem toCue_atomReferences (carrier : NonTetrahedralCarrier V) :
    (toCue carrier).atomReferences = [carrier.atom] := rfl

end NonTetrahedralCarrier

/-! ## The ordered list channel -/

/-- The ordered convention channel.  It is literally a list so that a main-domain record can carry
it as one field without choosing between an absent channel and an empty list.  Order, duplicates
and missing entries are all retained. -/
abbrev ConventionChannel (V : Type*) := List (OrganicConventionSource V)

namespace ConventionChannel

variable {V W : Type*}

/-- Encode every record in the channel through the one external equivalence. -/
def encode (e : V ≃ W) (channel : ConventionChannel V) : ConventionChannel W :=
  channel.map (OrganicConventionSource.encode e)

/-- Decode every record in the channel through the same equivalence. -/
def decode (e : V ≃ W) (channel : ConventionChannel W) : ConventionChannel V :=
  channel.map (OrganicConventionSource.decode e)

/-- Decoder recovery for the whole ordered channel. -/
@[simp] theorem decode_encode (e : V ≃ W) (channel : ConventionChannel V) :
    decode e (encode e channel) = channel := by
  change (channel.map (OrganicConventionSource.encode e)).map
      (OrganicConventionSource.decode e) = channel
  exact list_map_map_of_leftInverse (OrganicConventionSource.encode e)
    (OrganicConventionSource.decode e)
    (fun source => OrganicConventionSource.decode_encode e source) channel

/-- The channel length is retained. -/
@[simp] theorem encode_length (e : V ≃ W) (channel : ConventionChannel V) :
    (encode e channel).length = channel.length := by
  change (channel.map (OrganicConventionSource.encode e)).length = channel.length
  rw [List.length_map]

/-- Ordered lookup at a channel position is the encoding of the source record at that same
position. -/
theorem encode_get? (e : V ≃ W) (channel : ConventionChannel V) (index : Nat)
    (bound : index < channel.length) :
    (encode e channel)[index]? =
      some (OrganicConventionSource.encode e (channel[index]'bound)) := by
  change (channel.map (OrganicConventionSource.encode e))[index]? =
    some (OrganicConventionSource.encode e (channel[index]'bound))
  rw [List.getElem?_map, List.getElem?_eq_getElem bound]
  rfl

/-- The channel encoding is injective. -/
theorem encode_injective (e : V ≃ W) : Function.Injective (encode e) := by
  intro first second equal
  have applied := congrArg (decode e) equal
  simpa [decode_encode e first, decode_encode e second] using applied

end ConventionChannel

/-- Sidecar shape for a main-domain record: the existing certified authoritative input is carried
unchanged and the drawing-convention evidence is one ordered list field.  This structure is local
to this module; the shared authoritative type is not modified. -/
structure ConventionEvidence (V : Type*) where
  authoritative : CertifiedAuthoritativeChemicalInput
  channel : ConventionChannel V

namespace ConventionEvidence

variable {V W : Type*}

/-- Encode the convention channel and leave the authoritative input untouched. -/
def encode (e : V ≃ W) (evidence : ConventionEvidence V) : ConventionEvidence W :=
  { evidence with channel := ConventionChannel.encode e evidence.channel }

/-- Decode the convention channel and leave the authoritative input untouched. -/
def decode (e : V ≃ W) (evidence : ConventionEvidence W) : ConventionEvidence V :=
  { evidence with channel := ConventionChannel.decode e evidence.channel }

@[simp] theorem encode_authoritative (e : V ≃ W) (evidence : ConventionEvidence V) :
    (encode e evidence).authoritative = evidence.authoritative := rfl

@[simp] theorem encode_channel (e : V ≃ W) (evidence : ConventionEvidence V) :
    (encode e evidence).channel = ConventionChannel.encode e evidence.channel := rfl

/-- Decoder recovery for the sidecar; the authoritative input is literally unchanged. -/
@[simp] theorem decode_encode (e : V ≃ W) (evidence : ConventionEvidence V) :
    decode e (encode e evidence) = evidence := by
  obtain ⟨authoritative, channel⟩ := evidence
  simp [decode, encode, ConventionChannel.decode_encode]

end ConventionEvidence

/-! ## Optional graph binding for atom references

Only atom lookup agreement is asserted.  A supplied `BondGlyph` now carries a source occurrence
index, but this retention layer makes no bound claim about it: the bound and the two
endpoint-membership proofs are supplied by `OrganicStereoSourceGlyphIngress`, which stores a
`Fin graph.interactions.length` occurrence and compiles it to this cue.  `atomReferences` exposes
the ordered references, so `atom? = none` is not read as "no references". -/

section GraphBinding

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A reference-frame atom is looked up at the same enumeration index that the graph encoding uses
for its semantic atom data. -/
theorem referenceEntry_agrees_with_graph
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (entry : ReferenceEntry V) :
    listGet? (graph.encode e).atoms (e entry.atom).val =
      some (graph.atomData entry.atom) := by
  simpa using graph.encode_atomAt e (e entry.atom)

/-- When a cue names a single atom, that atom is looked up at the same enumeration index that the
graph encoding uses for its semantic atom data.  `bondGlyph` has no single-atom focus, so the
hypothesis is impossible for it. -/
theorem cueAtom_agrees_with_graph
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (cue : ConventionCue V) {atom : V} (observed : cue.atom? = some atom) :
    listGet? (graph.encode e).atoms (e atom).val = some (graph.atomData atom) := by
  cases cue with
  | fischerCenter atom' locant geometry hydroxySide domain =>
      have equal : atom' = atom := by
        simpa [ConventionCue.atom?] using observed
      rw [← equal]
      simpa using graph.encode_atomAt e (e atom')
  | fischerRotation turn =>
      exfalso
      simp [ConventionCue.atom?] at observed
  | haworthRing reference orientation numbering closure depiction =>
      have equal : reference = atom := by
        simpa [ConventionCue.atom?] using observed
      rw [← equal]
      simpa using graph.encode_atomAt e (e reference)
  | haworthSubstituent atom' side =>
      have equal : atom' = atom := by
        simpa [ConventionCue.atom?] using observed
      rw [← equal]
      simpa using graph.encode_atomAt e (e atom')
  | millsBond atom' bond =>
      have equal : atom' = atom := by
        simpa [ConventionCue.atom?] using observed
      rw [← equal]
      simpa using graph.encode_atomAt e (e atom')
  | nonTetrahedralReference atom' geometry =>
      have equal : atom' = atom := by
        simpa [ConventionCue.atom?] using observed
      rw [← equal]
      simpa using graph.encode_atomAt e (e atom')
  | bondGlyph glyph =>
      exfalso
      simp [ConventionCue.atom?] at observed
  | bondCrossing crossing =>
      exfalso
      simp [ConventionCue.atom?] at observed

/-- Every atom reference of a cue is looked up at the same enumeration index that the graph
encoding uses for its semantic atom data.  This includes both ordered endpoints of a
`bondGlyph` and the concatenated ordered endpoints of both glyphs of a `bondCrossing`. -/
theorem atomReferences_agrees_with_graph
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (cue : ConventionCue V) {atom : V} (_member : atom ∈ cue.atomReferences) :
    listGet? (graph.encode e).atoms (e atom).val = some (graph.atomData atom) := by
  simpa using graph.encode_atomAt e (e atom)

end GraphBinding

/-! ## Policy versus data -/



theorem mills_policy_value :
    IUPACDrawing2006.ST1Special.millsRecommendation =
      IUPACDrawing2006.ST0.Recommendation.preferred := rfl

end TetraStereo.OneCenter
