import TetraStereo.OneCenter.StereochemicalElements
import TetraStereo.OneCenter.ExplicitHydrogens
import TetraStereo.OneCenter.BranchSphereKey

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

/-!
  Automatic population of official CIP rule contexts.

  `CIPOfficialRules` defines the courtroom: an official-rule-aware comparator that can consult
  Rules 3, 4a, 4b, 4c, and 5 once ordinary graph keys tie.  This module starts summoning the
  witnesses automatically from normalized chemistry and descriptor evidence.

  The first executable perception pass covers:

  * Rule 3 contexts from parsed directional double-bond stereobond markers,
  * Rule 4a/4c/5 contexts from perceived descriptor facts,
  * Rule 4b like/unlike contexts from descriptor pairs.
-/

namespace Option

/-- Prefer the first optional value, falling back to the second. -/
def first {α : Type*} : Option α → Option α → Option α
  | some value, _ => some value
  | none, fallback => fallback

@[simp] theorem first_some {α : Type*} (value : α) (fallback : Option α) :
    first (some value) fallback = some value :=
  rfl

@[simp] theorem first_none {α : Type*} (fallback : Option α) :
    first none fallback = fallback :=
  rfl

end Option

namespace DirectionalBondMarker

/-- Interpret a directional marker as the lightweight side label used by `AlkeneEZ`. -/
def toAlkeneSide : DirectionalBondMarker → AlkeneSide
  | up => AlkeneSide.above
  | down => AlkeneSide.below

@[simp] theorem toAlkeneSide_up :
    toAlkeneSide up = AlkeneSide.above :=
  rfl

@[simp] theorem toAlkeneSide_down :
    toAlkeneSide down = AlkeneSide.below :=
  rfl

end DirectionalBondMarker

namespace DoubleBondStereo

/-- Convert parsed double-bond stereo into `AlkeneEZ` when it is specified. -/
def toAlkeneEZ? : DoubleBondStereo → Option AlkeneEZ
  | E => some AlkeneEZ.E
  | Z => some AlkeneEZ.Z
  | unspecified => none

/-- Convert parsed double-bond stereo into official Rule-3 geometry when specified. -/
def toRule3Geometry? (stereo : DoubleBondStereo) : Option OfficialRule3Geometry :=
  stereo.toAlkeneEZ?.map AlkeneEZ.toRule3Geometry

/-- Convert parsed double-bond stereo into an official ligand context when specified. -/
def toOfficialLigandRuleContext? (stereo : DoubleBondStereo) :
    Option CIPRuleEngine.OfficialLigandRuleContext :=
  stereo.toAlkeneEZ?.map AlkeneEZ.toOfficialLigandRuleContext

@[simp] theorem toRule3Geometry?_E :
    toRule3Geometry? E = some OfficialRule3Geometry.seqtrans :=
  rfl

@[simp] theorem toRule3Geometry?_Z :
    toRule3Geometry? Z = some OfficialRule3Geometry.seqcis :=
  rfl

@[simp] theorem toRule3Geometry?_unspecified :
    toRule3Geometry? unspecified = none :=
  rfl

end DoubleBondStereo

namespace StereobondAnnotation

/-- Whether an annotation is incident to an atom. -/
def incidentTo (annotation : StereobondAnnotation) (atom : ℕ) : Bool :=
  annotation.source == atom || annotation.target == atom

/-- Whether an annotation is incident to `atom` and not to the opposite double-bond endpoint. -/
def incidentToSideOf (annotation : StereobondAnnotation) (atom opposite : ℕ) : Bool :=
  annotation.incidentTo atom && !annotation.incidentTo opposite

/-- The side the annotated substituent occupies relative to `atom`.

`marker` records where the annotation's `target` sits relative to its `source`, which is the reading
order of the original OpenSMILES string.  When `atom` is the `target` rather than the `source`, the
same bond is being read backwards, so the recorded side must be reversed before it can be compared
with the side at the far end of a double bond.

Without this reorientation, equivalent spellings disagree: `F/C=C/F` writes both slashes with the
alkene carbon as `target` then `source`, while `C(\F)=C/F` writes both with the alkene carbon as
`source`, yet the two strings denote the same molecule.

`atom` is expected to be one of the annotation's own endpoints; callers establish that with
`incidentToSideOf` before asking for a side. An unrelated atom falls into the flip branch rather
than being rejected, so this is not a total function on arbitrary atoms. -/
def sideMarkerAt (annotation : StereobondAnnotation) (atom : ℕ) : DirectionalBondMarker :=
  if annotation.source == atom then annotation.marker else annotation.marker.flip

@[simp] theorem sideMarkerAt_source (annotation : StereobondAnnotation) :
    annotation.sideMarkerAt annotation.source = annotation.marker := by
  simp [sideMarkerAt]

/-- Read from the far endpoint, the recorded side is reversed.  This is the branch that makes
equivalent OpenSMILES spellings agree. -/
theorem sideMarkerAt_target (annotation : StereobondAnnotation)
    (h : annotation.source ≠ annotation.target) :
    annotation.sideMarkerAt annotation.target = annotation.marker.flip := by
  simp [sideMarkerAt, h]

end StereobondAnnotation

namespace StereobondSemantics

/-- Does a stored double-bond assignment have the requested undirected endpoints? -/
def doubleBondAssignmentConnects (assignment : ℕ × ℕ × DoubleBondStereo) (u v : ℕ) : Bool :=
  match assignment with
  | (left, right, _) => (left == u && right == v) || (left == v && right == u)

/-- Extract the stereo value from a stored double-bond assignment. -/
def doubleBondAssignmentStereo (assignment : ℕ × ℕ × DoubleBondStereo) : DoubleBondStereo :=
  match assignment with
  | (_, _, stereo) => stereo

/-- Stored specified stereo for a double bond, if present.  `unspecified` is intentionally treated
as absent so directional marker perception can still fill the context. -/
def storedDoubleBondStereo? (semantics : StereobondSemantics) (u v : ℕ) :
    Option DoubleBondStereo :=
  match semantics.doubleBondAssignments.find? fun assignment =>
      doubleBondAssignmentConnects assignment u v with
  | none => none
  | some assignment =>
      match doubleBondAssignmentStereo assignment with
      | DoubleBondStereo.unspecified => none
      | stereo => some stereo

/-- Directional stereobond annotation on the substituent side of one double-bond endpoint.

The result carries the annotation's raw reading-order `marker`, which is *not* a side relative to
`atom`.  Consumers comparing sides across a double bond must go through
`StereobondAnnotation.sideMarkerAt atom` (or use `directionalMarkersAtSide`, which already does);
reading `.marker` directly reintroduces the spelling-dependence that reorientation removes. -/
def directionalAtSide? (semantics : StereobondSemantics) (atom opposite : ℕ) :
    Option StereobondAnnotation :=
  semantics.directionalBonds.find? fun annotation =>
    annotation.incidentToSideOf atom opposite

/-- Directional marker values on one substituent side of a double-bond endpoint, reoriented so that
every marker describes a side relative to `atom` rather than to the parsed bond direction. -/
def directionalMarkersAtSide (semantics : StereobondSemantics) (atom opposite : ℕ) :
    List DirectionalBondMarker :=
  semantics.directionalBonds.filterMap fun annotation =>
    if annotation.incidentToSideOf atom opposite then
      some (annotation.sideMarkerAt atom)
    else
      none

/-- A unique side marker, refusing absent or contradictory directional marker evidence. -/
def uniqueDirectionalMarker? (markers : List DirectionalBondMarker) :
    Option DirectionalBondMarker :=
  let hasUp := markers.any fun marker => decide (marker = DirectionalBondMarker.up)
  let hasDown := markers.any fun marker => decide (marker = DirectionalBondMarker.down)
  match hasUp, hasDown with
  | true, false => some DirectionalBondMarker.up
  | false, true => some DirectionalBondMarker.down
  | _, _ => none

/-- Unique directional marker on one substituent side of a double bond. -/
def uniqueDirectionalMarkerAtSide? (semantics : StereobondSemantics) (atom opposite : ℕ) :
    Option DirectionalBondMarker :=
  uniqueDirectionalMarker? (semantics.directionalMarkersAtSide atom opposite)

/-- Reoriented side marker recorded on the specific bond between `carbon` and `substituent`.

This addresses one named substituent rather than a whole side, which is what CIP `E/Z` needs: the
descriptor is decided by where the *senior* substituent sits, and the senior one is often not the
one carrying the slash.

Uniqueness is checked per *bond*, which is the granularity at which markers can actually conflict: a
single bond cannot run both up and down, so two different reoriented values here are contradictory
input and are refused.  Two different values across the two *substituents* of one carbon are the
opposite situation — that is what a consistently marked endpoint looks like — and are handled by
`seniorSideAt?`. -/
def substituentSideMarker? (semantics : StereobondSemantics) (carbon substituent : ℕ) :
    Option DirectionalBondMarker :=
  match (semantics.directionalBonds.filterMap fun annotation =>
      if (annotation.source == carbon && annotation.target == substituent) ||
          (annotation.source == substituent && annotation.target == carbon) then
        some (annotation.sideMarkerAt carbon)
      else
        none).eraseDups with
  | [marker] => some marker
  | _ => none

/-- Lightweight conversion from the two side markers around a double bond to `E/Z`.

Both arguments must already be reoriented to their own double-bond endpoint by
`StereobondAnnotation.sideMarkerAt`; the parser stores raw reading-order markers and does *not*
normalize them.  Given reoriented sides, the two substituents lie on the same side exactly when the
markers agree, so matching sides produce `Z` and opposite sides produce `E`.

This is the primitive comparison only: it reports the relationship of whichever two sides it is
handed.  Getting a CIP `E/Z` label out of it requires handing it the sides of the *senior*
substituents, which is what `ChemistryNormalizationResult.cipDoubleBondStereo?` does.  Applying it
directly to marked-substituent sides answers a different question. -/
def stereoFromDirectionalMarkers (left right : DirectionalBondMarker) : DoubleBondStereo :=
  if left = right then DoubleBondStereo.Z else DoubleBondStereo.E

/-- Infer double-bond stereo from unambiguous directional markers at both double-bond endpoints. -/
def inferDoubleBondStereoFromMarkers? (semantics : StereobondSemantics) (u v : ℕ) :
    Option DoubleBondStereo :=
  match semantics.uniqueDirectionalMarkerAtSide? u v, semantics.uniqueDirectionalMarkerAtSide? v u with
  | some leftMarker, some rightMarker =>
      some (stereoFromDirectionalMarkers leftMarker rightMarker)
  | _, _ => none

/-- Marked-substituent stereo: explicit stored stereo wins, otherwise the directional markers are
read when both sides are available.

This works from stereobond annotations alone and so has no access to constitution, which means it
cannot rank substituents.  It reports the geometry of whichever atoms carry slashes, which coincides
with `E/Z` only when those atoms happen to be the senior ones.  Callers that have a normalized
molecule should prefer `ChemistryNormalizationResult.perceivedDoubleBondStereo?`, which selects the
CIP-senior substituent at each end. -/
def perceivedDoubleBondStereo? (semantics : StereobondSemantics) (u v : ℕ) :
    Option DoubleBondStereo :=
  Option.first (semantics.storedDoubleBondStereo? u v)
    (semantics.inferDoubleBondStereoFromMarkers? u v)

/-- Perceived official Rule-3 context for a double bond. -/
def perceivedRule3Context? (semantics : StereobondSemantics) (u v : ℕ) :
    Option CIPRuleEngine.OfficialLigandRuleContext :=
  match semantics.perceivedDoubleBondStereo? u v with
  | some stereo => stereo.toOfficialLigandRuleContext?
  | none => none

/-- Perceived Rule-3 contexts for all parsed double bonds whose stereo can be inferred or read. -/
def perceivedRule3Contexts (semantics : StereobondSemantics) :
    List ((ℕ × ℕ) × CIPRuleEngine.OfficialLigandRuleContext) :=
  semantics.doubleBondAssignments.filterMap fun assignment =>
    match assignment with
    | (u, v, _) =>
        match semantics.perceivedRule3Context? u v with
        | some context => some ((u, v), context)
        | none => none

@[simp] theorem stereoFromDirectionalMarkers_same (marker : DirectionalBondMarker) :
    stereoFromDirectionalMarkers marker marker = DoubleBondStereo.Z := by
  cases marker <;> rfl

@[simp] theorem stereoFromDirectionalMarkers_up_down :
    stereoFromDirectionalMarkers DirectionalBondMarker.up DirectionalBondMarker.down =
      DoubleBondStereo.E :=
  rfl

@[simp] theorem stereoFromDirectionalMarkers_down_up :
    stereoFromDirectionalMarkers DirectionalBondMarker.down DirectionalBondMarker.up =
      DoubleBondStereo.E :=
  rfl

/-- Contradictory directional markers on one side do not infer an `E/Z` descriptor. -/
example :
    ({ directionalBonds :=
        [ { source := 0, target := 1, marker := DirectionalBondMarker.up }
        , { source := 0, target := 1, marker := DirectionalBondMarker.down }
        , { source := 2, target := 3, marker := DirectionalBondMarker.down } ]
       tetrahedralAtoms := []
       doubleBondAssignments := [(1, 2, DoubleBondStereo.unspecified)] } :
      StereobondSemantics).perceivedDoubleBondStereo? 1 2 = none := by
  decide

end StereobondSemantics

/-! ### Descriptor-environment perception for Rules 4a, 4b, 4c, and 5 -/

/-- Descriptor facts that a stereochemical detector may attach to a ligand branch. -/
inductive PerceivedDescriptor where
  | tetrahedral (descriptor : RS)
  | pseudoTetrahedral (descriptor : PseudoRS)
  | pseudoOfficial (descriptor : OfficialPseudoasymmetricDescriptor)
  | helical (descriptor : HelicalDescriptor)
  | alkene (descriptor : AlkeneEZ)
  | officialRule5 (descriptor : OfficialRule5Descriptor)
  deriving DecidableEq, Repr

namespace PerceivedDescriptor

/-- Rule 3 geometry supplied by this descriptor, if any. -/
def rule3Geometry? : PerceivedDescriptor → Option OfficialRule3Geometry
  | alkene descriptor => some descriptor.toRule3Geometry
  | _ => none

/-- Rule 4a stereogenic-unit kind supplied by this descriptor, if any. -/
def rule4aKind? : PerceivedDescriptor → Option OfficialStereogenicUnitKind
  | tetrahedral _ => some OfficialStereogenicUnitKind.chiral
  | helical _ => some OfficialStereogenicUnitKind.chiral
  | officialRule5 _ => some OfficialStereogenicUnitKind.chiral
  | pseudoTetrahedral _ => some OfficialStereogenicUnitKind.pseudoasymmetric
  | pseudoOfficial _ => some OfficialStereogenicUnitKind.pseudoasymmetric
  | alkene _ => none

/-- Rule 4c pseudoasymmetric descriptor supplied by this descriptor, if any. -/
def rule4cDescriptor? : PerceivedDescriptor → Option OfficialPseudoasymmetricDescriptor
  | pseudoTetrahedral descriptor => some (OfficialPseudoasymmetricDescriptor.ofPseudoRS descriptor)
  | pseudoOfficial descriptor => some descriptor
  | _ => none

/-- Rule 5 senior/junior descriptor supplied by this descriptor, if any. -/
def rule5Descriptor? : PerceivedDescriptor → Option OfficialRule5Descriptor
  | tetrahedral descriptor => some (OfficialRule5Descriptor.ofRS descriptor)
  | helical descriptor => some descriptor.toRule5Descriptor
  | officialRule5 descriptor => some descriptor
  | _ => none

/-- Official context generated by one perceived descriptor fact. -/
def toOfficialLigandRuleContext (descriptor : PerceivedDescriptor) :
    CIPRuleEngine.OfficialLigandRuleContext where
  rule3Geometry? := descriptor.rule3Geometry?
  rule4aKind? := descriptor.rule4aKind?
  rule4bPair? := none
  rule4cDescriptor? := descriptor.rule4cDescriptor?
  rule5Descriptor? := descriptor.rule5Descriptor?

/-- Rule 4b pair kind generated by two descriptor facts with Rule-5 senses. -/
def pairKind? (left right : PerceivedDescriptor) : Option OfficialDescriptorPairKind :=
  match left.rule5Descriptor?, right.rule5Descriptor? with
  | some leftDescriptor, some rightDescriptor =>
      some (OfficialRule5Descriptor.pairKind leftDescriptor rightDescriptor)
  | _, _ => none

@[simp] theorem tetrahedral_R_rule5 :
    (tetrahedral RS.R).rule5Descriptor? = some OfficialRule5Descriptor.descriptorR :=
  rfl

@[simp] theorem pseudo_r_rule4c :
    (pseudoTetrahedral PseudoRS.r).rule4cDescriptor? =
      some OfficialPseudoasymmetricDescriptor.r :=
  rfl

@[simp] theorem helical_M_rule5 :
    (helical HelicalDescriptor.M).rule5Descriptor? =
      some OfficialRule5Descriptor.descriptorM :=
  rfl

@[simp] theorem alkene_Z_rule3 :
    (alkene AlkeneEZ.Z).rule3Geometry? = some OfficialRule3Geometry.seqcis :=
  rfl

@[simp] theorem pairKind_R_M :
    pairKind? (tetrahedral RS.R) (helical HelicalDescriptor.M) =
      some OfficialDescriptorPairKind.like :=
  rfl

@[simp] theorem pairKind_R_P :
    pairKind? (tetrahedral RS.R) (helical HelicalDescriptor.P) =
      some OfficialDescriptorPairKind.unlike :=
  rfl

end PerceivedDescriptor

/-- Perceived evidence available for one ligand branch. -/
structure PerceivedLigandEvidence where
  doubleBondStereo? : Option DoubleBondStereo := none
  descriptor? : Option PerceivedDescriptor := none
  descriptorPair? : Option (PerceivedDescriptor × PerceivedDescriptor) := none
  deriving DecidableEq, Repr

namespace PerceivedLigandEvidence

/-- Empty evidence yields no official rule context. -/
def empty : PerceivedLigandEvidence := {}

/-- Evidence from a perceived alkene/double-bond stereo assignment. -/
def ofDoubleBondStereo (stereo : DoubleBondStereo) : PerceivedLigandEvidence where
  doubleBondStereo? := some stereo

/-- Evidence from a single descriptor fact. -/
def ofDescriptor (descriptor : PerceivedDescriptor) : PerceivedLigandEvidence where
  descriptor? := some descriptor

/-- Evidence from a descriptor pair used by Rule 4b. -/
def ofDescriptorPair (left right : PerceivedDescriptor) : PerceivedLigandEvidence where
  descriptorPair? := some (left, right)

/-- Rule 3 geometry perceived from this evidence. -/
def rule3Geometry? (evidence : PerceivedLigandEvidence) : Option OfficialRule3Geometry :=
  Option.first (evidence.doubleBondStereo?.bind DoubleBondStereo.toRule3Geometry?)
    (evidence.descriptor?.bind PerceivedDescriptor.rule3Geometry?)

/-- Rule 4a unit kind perceived from this evidence. -/
def rule4aKind? (evidence : PerceivedLigandEvidence) : Option OfficialStereogenicUnitKind :=
  evidence.descriptor?.bind PerceivedDescriptor.rule4aKind?

/-- Rule 4b pair kind perceived from this evidence. -/
def rule4bPair? (evidence : PerceivedLigandEvidence) : Option OfficialDescriptorPairKind :=
  match evidence.descriptorPair? with
  | some (left, right) => PerceivedDescriptor.pairKind? left right
  | none => none

/-- Rule 4c pseudoasymmetric descriptor perceived from this evidence. -/
def rule4cDescriptor? (evidence : PerceivedLigandEvidence) :
    Option OfficialPseudoasymmetricDescriptor :=
  evidence.descriptor?.bind PerceivedDescriptor.rule4cDescriptor?

/-- Rule 5 descriptor perceived from this evidence. -/
def rule5Descriptor? (evidence : PerceivedLigandEvidence) : Option OfficialRule5Descriptor :=
  evidence.descriptor?.bind PerceivedDescriptor.rule5Descriptor?

/-- Populate an official ligand rule context from perceived branch evidence. -/
def toOfficialLigandRuleContext (evidence : PerceivedLigandEvidence) :
    CIPRuleEngine.OfficialLigandRuleContext where
  rule3Geometry? := evidence.rule3Geometry?
  rule4aKind? := evidence.rule4aKind?
  rule4bPair? := evidence.rule4bPair?
  rule4cDescriptor? := evidence.rule4cDescriptor?
  rule5Descriptor? := evidence.rule5Descriptor?

@[simp] theorem ofDoubleBondStereo_Z_rule3 :
    (ofDoubleBondStereo DoubleBondStereo.Z).rule3Geometry? =
      some OfficialRule3Geometry.seqcis :=
  rfl

@[simp] theorem ofDescriptor_pseudo_r_rule4c :
    (ofDescriptor (PerceivedDescriptor.pseudoTetrahedral PseudoRS.r)).rule4cDescriptor? =
      some OfficialPseudoasymmetricDescriptor.r :=
  rfl

@[simp] theorem ofDescriptorPair_like_rule4b :
    (ofDescriptorPair (PerceivedDescriptor.tetrahedral RS.R)
      (PerceivedDescriptor.helical HelicalDescriptor.M)).rule4bPair? =
      some OfficialDescriptorPairKind.like :=
  rfl

end PerceivedLigandEvidence

namespace RawMolecule

/-- Explicit substituents at one end of a double bond: parsed neighbours of `atom` other than its
double-bond `partner`.

Implicit hydrogens are not parsed atoms and deliberately do not appear here.  They never need to:
see `seniorAlkeneSubstituent?` for why hydrogen can be ranked without being represented. -/
def alkeneSubstituents (mol : RawMolecule) (carbon partner : ℕ) : List ℕ :=
  (mol.bonds.filterMap fun bond =>
    if bond.source == carbon && bond.target != partner then some bond.target
    else if bond.target == carbon && bond.source != partner then some bond.source
    else none).eraseDups

/-- Whether a double-bond endpoint contributes a lone-pair side in place of a second atom
substituent.

The first public extension is deliberately narrow: neutral or charged nitrogen in imines, oximes,
hydrazones, and azo units.  Its one explicit substituent competes with the nitrogen lone pair; the
lone pair has atomic-number label zero and is therefore junior to every known real atom. -/
def doubleBondEndpointHasLonePairSide (mol : RawMolecule) (atom partner : ℕ) : Bool :=
  match mol.atomAt? atom with
  | some spec => spec.element == Element.N && (mol.alkeneSubstituents atom partner).length == 1
  | none => false

/-- First-sphere CIP label of a parsed atom: atomic number, then the exact source-backed Rule-2
mass value. An unknown nuclide receives only the internal zero fallback and is refused below. -/
def firstSphereLabel? (mol : RawMolecule) (atom : ℕ) : Option (ℕ × ℕ) :=
  match mol.atoms[atom]? with
  | some spec => some (spec.element.atomicNumber, mol.atomMassAt atom)
  | none => none

/-- Rule-2 component of an exact first-sphere label. -/
def rankMass (label : ℕ × ℕ) : ℕ := label.2

/-- Strict first-sphere precedence: atomic number, then exact Rule-2 mass. -/
def firstSphereOutranks (left right : ℕ × ℕ) : Bool :=
  left.1 > right.1 || (left.1 == right.1 && rankMass left > rankMass right)

/-- Whether a first-sphere label stands for an unknown atom.

`Element.wildcard` is given atomic number `0`; an isotope absent from the frozen AME data has mass
key `0`. Both are sentinels and must never be compared as if they were physical atoms. -/
def firstSphereUnknown (label : ℕ × ℕ) : Bool :=
  label.1 == 0 || label.2 == 0

/-- The implicit hydrogen filling an unwritten position: protium. -/
def implicitHydrogenLabel : ℕ × ℕ := (1, rule2MassPico Element.H none)

/-- The CIP-senior substituent at one end of a double bond, when seniority is determined.

The cases are exhaustive for an sp2 carbon, and none of them requires hydrogens to be present as
atoms:

* **no explicit substituent** — the carbon bears two hydrogens, the end is not stereogenic, and
  there is no descriptor to assign;
* **one explicit substituent** — the other position holds an implicit hydrogen, so the explicit
  substituent is senior exactly when it outranks hydrogen.  That is the usual case and needs no
  real ranking, which is why `C/C=C/C` never depended on one.  It is *not* unconditional: an
  explicitly written `[H]` ties with the implicit hydrogen, so that end carries two hydrogens and is
  not stereogenic, while `[2H]` outranks it on mass and is senior;
* **two explicit substituents** — rank them by first-sphere atomic number, then isotope mass.  An
  explicit `[H]` competing against a real substituent is ranked normally here, since both positions
  are then accounted for.

A `*` wildcard is refused in *both* branches rather than compared.  Its atomic number `0` is a
sentinel for "unspecified", not a real element lighter than hydrogen, so treating it as the loser of
a comparison would emit a confident descriptor that a different reading of the wildcard would
contradict.

Anything else — more than two substituents, an unreadable atom index, or a first-sphere tie — is
refused rather than guessed.  The tie case is the honest boundary of this comparator: separating
branches that agree in the first sphere (ethyl versus methyl, say) needs the full hierarchical
digraph, so this reports no descriptor rather than picking one.  A refusal is a missing answer; the
alternative would be a wrong one. -/
def seniorAlkeneSubstituent? (mol : RawMolecule) (fuel carbon partner : ℕ) : Option ℕ :=
  match mol.alkeneSubstituents carbon partner with
  | [] => none
  | [s] =>
      -- The unwritten position holds an implicit hydrogen; `s` is senior exactly when it outranks
      -- that hydrogen.  A plain `[H]` ties and refuses, `[2H]` wins on mass, and `*` is unknown.
      match mol.firstSphereLabel? s with
      | some label =>
          if firstSphereUnknown label then none
          else if mol.doubleBondEndpointHasLonePairSide carbon partner then some s
          else if firstSphereOutranks label implicitHydrogenLabel then some s
          else none
      | none => none
  | [s, t] =>
      match mol.firstSphereLabel? s, mol.firstSphereLabel? t with
      | some ls, some lt =>
          if firstSphereUnknown ls || firstSphereUnknown lt then none
          else
            let sr := canonicalRoot carbon s
            let tr := canonicalRoot carbon t
            if mol.canonicalTerminal sr && mol.canonicalTerminal tr then
              -- Terminal roots have no descendant layers.  Comparing their canonical labels
              -- through Rule 2 is therefore the exact full-branch result, while remaining small
              -- enough for the kernel evaluator to check isotope-only ends directly.
              match mol.compareCanonicalNodeThrough? CanonicalRuleStage.rule2 sr tr with
              | some Ordering.gt => some s
              | some Ordering.lt => some t
              | _ => none
            else
              -- Rule 1a first, exhausted across the branch by the shared sphere key.
              match mol.compareBranches fuel carbon s t with
              | Ordering.gt => some s
              | Ordering.lt => some t
              | Ordering.eq =>
                  -- Rule 1a cannot separate them; fall through to Rule 2 on the first sphere.
                  if firstSphereOutranks ls lt then some s
                  else if firstSphereOutranks lt ls then some t
                  else none
      | _, _ => none
  | _ :: _ :: _ :: _ => none

end RawMolecule

namespace ChemistryNormalizationResult

/-- The side occupied by the CIP-senior substituent at one end of a double bond.

Directional markers are recorded per bond, so the senior substituent may carry no marker of its own.
The two substituents of an sp2 carbon lie on opposite sides, so an unmarked senior's side is the
`flip` of its partner's.

Ranking runs over the hydrogen-materialised molecule, so an implicit hydrogen is a real competitor
rather than an absent one.  That both sharpens the ranking — `CC/C(C)=C/Br` separates ethyl from
methyl at the second sphere, where a first-sphere comparison ties — and removes the need to special
case the hydrogen that fills an unwritten position.

When both substituents are marked, consistency requires their reoriented markers to *disagree*;
agreeing markers would place both substituents on the same side, which is the genuine contradiction
and is refused.  This is exactly the case a whole-side marker scan gets backwards, because after
reorientation a correctly marked endpoint always shows two different values. -/
def seniorSideAt? (result : ChemistryNormalizationResult) (carbon partner : ℕ) :
    Option DirectionalBondMarker :=
  let expanded := result.parsed.withExplicitHydrogens
  let fuel := 2 * expanded.atomCount + 2
  match expanded.seniorAlkeneSubstituent? fuel carbon partner with
  | none => none
  | some senior =>
      let seniorMarker? := result.stereobonds.substituentSideMarker? carbon senior
      let otherMarker? :=
        match (expanded.alkeneSubstituents carbon partner).filter (fun s => s != senior) with
        | [other] => result.stereobonds.substituentSideMarker? carbon other
        | _ => none
      match seniorMarker?, otherMarker? with
      | some s, some o => if s = o.flip then some s else none
      | some s, none => some s
      | none, some o => some o.flip
      | none, none => none

/-- CIP `E/Z` for a double bond, decided from the sides of the two senior substituents.

Unlike a bare marked-substituent reading, this consults CIP priority at each end, so it reports the
relationship of the senior groups rather than of whichever atoms happened to carry slashes. -/
def cipDoubleBondStereo? (result : ChemistryNormalizationResult) (u v : ℕ) :
    Option DoubleBondStereo :=
  if (result.stereobonds.directionalMarkersAtSide u v).isEmpty ||
      (result.stereobonds.directionalMarkersAtSide v u).isEmpty then
    none
  else
    match result.seniorSideAt? u v, result.seniorSideAt? v u with
    | some left, some right =>
        some (StereobondSemantics.stereoFromDirectionalMarkers left right)
    | _, _ => none

/-- Perceived stereo for a particular parsed double bond: an explicit stored assignment wins,
otherwise the senior-substituent CIP reading decides. -/
def perceivedDoubleBondStereo? (result : ChemistryNormalizationResult) (u v : ℕ) :
    Option DoubleBondStereo :=
  Option.first (result.stereobonds.storedDoubleBondStereo? u v) (result.cipDoubleBondStereo? u v)

/-- Perceived official Rule-3 context for a double bond of a normalized molecule. -/
def perceivedRule3Context? (result : ChemistryNormalizationResult) (u v : ℕ) :
    Option CIPRuleEngine.OfficialLigandRuleContext :=
  match result.perceivedDoubleBondStereo? u v with
  | some stereo => stereo.toOfficialLigandRuleContext?
  | none => none

/-- Perceived Rule-3 contexts for all parsed double bonds in a normalized molecule.

This runs through the senior-substituent reading, so a wrong marked-substituent geometry can no
longer be seeded into the official comparator as a Rule-3 fact. -/
def perceivedRule3Contexts (result : ChemistryNormalizationResult) :
    List ((ℕ × ℕ) × CIPRuleEngine.OfficialLigandRuleContext) :=
  result.stereobonds.doubleBondAssignments.filterMap fun assignment =>
    match assignment with
    | (u, v, _) =>
        match result.perceivedRule3Context? u v with
        | some context => some ((u, v), context)
        | none => none

end ChemistryNormalizationResult

/-! ### OpenSMILES directional-marker truth table

Per the OpenSMILES specification, two directional markers written the same way around a double bond
place the marked substituents on *opposite* sides, so `F/C=C/F` is trans-difluoroethene (`E`) and
`F/C=C\F` is the cis isomer (`Z`).  The markers are stored in string reading order, so recovering the
geometry requires `StereobondAnnotation.sideMarkerAt` to reorient each marker to its own double-bond
endpoint first.

These demonstrations pin both the absolute assignments and the spelling invariance that the
reorientation exists to provide: a branch changes which endpoint a marker is written from, so
`F/C=C/F` and `C(\F)=C/F` denote the same molecule and must perceive the same descriptor.

They evaluate the total OpenSMILES parser over `String` input.  The proofs use kernel reduction via
`decide`; they do not rely on compiled evaluator trust. -/

/-- `F/C=C/F` is trans-difluoroethene: matching slashes, opposite sides, `E`. -/
example :
    (match parseAndNormalizeOpenSMILES "F/C=C/F" with
      | Except.ok result => result.perceivedDoubleBondStereo? 1 2 = some DoubleBondStereo.E
      | Except.error _ => false) = true := by
  decide

/-- `F/C=C\F` is cis-difluoroethene: opposed slashes, same side, `Z`. -/
example :
    (match parseAndNormalizeOpenSMILES "F/C=C\\F" with
      | Except.ok result => result.perceivedDoubleBondStereo? 1 2 = some DoubleBondStereo.Z
      | Except.error _ => false) = true := by
  decide

/-- `C(\F)=C/F` spells the same molecule as `F/C=C/F` through a branch, and perceives the same `E`. -/
example :
    (match parseAndNormalizeOpenSMILES "C(\\F)=C/F" with
      | Except.ok result => result.perceivedDoubleBondStereo? 0 2 = some DoubleBondStereo.E
      | Except.error _ => false) = true := by
  decide

/-- `C(/F)=C/F` spells the same molecule as `F/C=C\F`, and perceives the same `Z`. -/
example :
    (match parseAndNormalizeOpenSMILES "C(/F)=C/F" with
      | Except.ok result => result.perceivedDoubleBondStereo? 0 2 = some DoubleBondStereo.Z
      | Except.error _ => false) = true := by
  decide

/-- `C/C=C/C` is trans-2-butene (`E`). -/
example :
    (match parseAndNormalizeOpenSMILES "C/C=C/C" with
      | Except.ok result => result.perceivedDoubleBondStereo? 1 2 = some DoubleBondStereo.E
      | Except.error _ => false) = true := by
  decide

/-- `C/C=C\C` is cis-2-butene (`Z`). -/
example :
    (match parseAndNormalizeOpenSMILES "C/C=C\\C" with
      | Except.ok result => result.perceivedDoubleBondStereo? 1 2 = some DoubleBondStereo.Z
      | Except.error _ => false) = true := by
  decide

/-- Reorientation is what makes the two spellings of trans-difluoroethene agree.  Reading the raw
stored markers instead makes them disagree, which is the defect this normalization removes. -/
example :
    (match parseAndNormalizeOpenSMILES "F/C=C/F", parseAndNormalizeOpenSMILES "C(\\F)=C/F" with
      | Except.ok slashed, Except.ok branched =>
          slashed.perceivedDoubleBondStereo? 1 2 = branched.perceivedDoubleBondStereo? 0 2
      | _, _ => false) = true := by
  decide

/-! ### Seniority, not slashes

The descriptor is decided by where the CIP-senior substituent sits, which is frequently not the atom
carrying the slash.  These demonstrations pin the two cases that a marked-substituent reading gets
wrong. -/

/-- In `F/C(Cl)=C/Br` the marked atoms F and Br are trans, but chlorine outranks fluorine, so the
senior pair Cl/Br is cis and the descriptor is `Z`.  Reading the marked atoms alone reports `E`. -/
example :
    (match parseAndNormalizeOpenSMILES "F/C(Cl)=C/Br" with
      | Except.ok result => result.perceivedDoubleBondStereo? 1 3 = some DoubleBondStereo.Z
      | Except.error _ => false) = true := by
  decide

/-- `F/C(/Cl)=C(/Br)\I` marks both substituents at both ends consistently.  Once each marker is
reoriented the two at a given carbon necessarily disagree, so a whole-side scan reads that as
contradictory evidence and refuses; selecting the senior substituent resolves it to `E`. -/
example :
    (match parseAndNormalizeOpenSMILES "F/C(/Cl)=C(/Br)\\I" with
      | Except.ok result => result.perceivedDoubleBondStereo? 1 3 = some DoubleBondStereo.E
      | Except.error _ => false) = true := by
  decide

/-- Ethyl outranks methyl at the second sphere, so this now resolves.

It is the capability the shared sphere key buys: a first-sphere comparison ties here, and the
earlier first-sphere-only ranking refused. -/
example :
    (match parseAndNormalizeOpenSMILES "CC/C(C)=C/Br" with
      | Except.ok result => result.perceivedDoubleBondStereo? 2 4 = some DoubleBondStereo.E
      | Except.error _ => false) = true := by
  decide

/-- An explicitly written `[H]` as the only substituent ties with the implicit hydrogen, so that end
bears two hydrogens and is not stereogenic. -/
example :
    (match parseAndNormalizeOpenSMILES "[H]/C=C/Br" with
      | Except.ok result => result.perceivedDoubleBondStereo? 1 2 = none
      | Except.error _ => false) = true := by
  decide

/-- A `*` wildcard ranks `0` and cannot be known to outrank the implicit hydrogen, so it refuses. -/
example :
    (match parseAndNormalizeOpenSMILES "*/C=C/Br" with
      | Except.ok result => result.perceivedDoubleBondStereo? 1 2 = none
      | Except.error _ => false) = true := by
  decide

/-- A wildcard competing against a real substituent also refuses rather than losing the comparison.
Atomic number `0` marks an unknown atom, and a `*` standing for bromine or iodine would outrank the
chlorine here and invert the descriptor. -/
example :
    (match parseAndNormalizeOpenSMILES "*/C(Cl)=C/Br" with
      | Except.ok result => result.perceivedDoubleBondStereo? 1 3 = none
      | Except.error _ => false) = true := by
  decide

/-- P-92.3 explicitly identifies ordinary `H` with `¹H`.  Consequently `[1H]` ties the implicit
protium at this alkene end and cannot create a stereogenic unit. -/
example :
    (match parseAndNormalizeOpenSMILES "[1H]/C=C/Br" with
      | Except.ok result => result.perceivedDoubleBondStereo? 1 2 = none
      | Except.error _ => false) = true := by
  decide

/-- Deuterium outranks the unlabelled implicit hydrogen on isotope mass, so that end *is*
stereogenic and resolves. -/
example :
    (match parseAndNormalizeOpenSMILES "[2H]/C=C/Br" with
      | Except.ok result => result.perceivedDoubleBondStereo? 1 2 = some DoubleBondStereo.E
      | Except.error _ => false) = true := by
  decide

/-- An explicit `[H]` competing against a real substituent is ranked normally: fluorine wins, and
because fluorine is the unmarked one its side is the flip of the marked hydrogen's. -/
example :
    (match parseAndNormalizeOpenSMILES "[H]/C(F)=C/Br" with
      | Except.ok result => result.perceivedDoubleBondStereo? 1 3 = some DoubleBondStereo.Z
      | Except.error _ => false) = true := by
  decide

/-- Perceived Rule-4b descriptor-pair evidence feeds the official context comparator. -/
example :
    cipTraceOutcome
      (CIPRuleEngine.compareOfficialContextTrace
        ((PerceivedLigandEvidence.ofDescriptorPair
          (PerceivedDescriptor.tetrahedral RS.R)
          (PerceivedDescriptor.helical HelicalDescriptor.M)).toOfficialLigandRuleContext)
        ((PerceivedLigandEvidence.ofDescriptorPair
          (PerceivedDescriptor.tetrahedral RS.R)
          (PerceivedDescriptor.helical HelicalDescriptor.P)).toOfficialLigandRuleContext)) =
      Ordering.gt := by
  rfl

end
end OneCenter
end TetraStereo
