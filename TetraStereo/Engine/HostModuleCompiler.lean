import TetraStereo.Engine.OfficialStereoBuilder

set_option autoImplicit false

namespace TetraStereo
namespace Engine

open OneCenter

noncomputable section

/-!
  Host Lean module compiler.

  This is the first source-level compiler for host-supplied molecule requests.  It takes structured
  Lean data for a predecoded molecule plus a compact official-stereo query target, then renders a
  standalone Lean module containing the raw molecule, checked intake success, compact query, build
  proof, checked host-query theorem, and generated certificate source entry.
-/

/-! ### Lean expression rendering for host molecule packets -/

/-- Render a Lean string literal. -/
def leanStringLit (text : String) : String :=
  toString (repr text)

/-- Render a Lean boolean literal. -/
def leanBoolExpr (value : Bool) : String :=
  if value then "true" else "false"

/-- Render a Lean natural-number list. -/
def leanNatListExpr (values : List ℕ) : String :=
  "[" ++ String.intercalate ", " (values.map toString) ++ "]"

/-- Render a Lean list from an element renderer. -/
def leanListExpr {α : Type*} (render : α → String) (values : List α) : String :=
  "[" ++ String.intercalate ", " (values.map render) ++ "]"

/-- Render a Lean option from an element renderer. -/
def leanOptionExpr {α : Type*} (render : α → String) : Option α → String
  | none => "none"
  | some value => "some (" ++ render value ++ ")"

/-- Render a Lean string list. -/
def leanStringListExpr (values : List String) : String :=
  "[" ++ String.intercalate ", " (values.map leanStringLit) ++ "]"

/-- Render a Lean namespace-qualified name. -/
def leanQualifiedName (namespacePath : List String) (name : String) : String :=
  String.intercalate "." (namespacePath ++ [name])

/-! ### Host request shape validation -/

/-- ASCII characters accepted at the start of generated Lean identifiers. -/
def leanIdentifierStartChars : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_".toList

/-- ASCII characters accepted after the first character in generated Lean identifiers. -/
def leanIdentifierRestChars : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_0123456789".toList

/-- Lean keywords and reserved command identifiers that generated names must not reuse. -/
def leanReservedIdentifierSegments : List String :=
  [ "_", "Prop", "Sort", "Type", "abbrev", "attribute", "axiom", "break", "builtin_initialize"
  , "by", "calc", "case", "catch", "class", "coinductive_fixpoint", "continue"
  , "dbg_trace", "declare_syntax_cat", "decreasing_by", "def", "deriving", "do", "elab"
  , "elab_rules", "else", "end", "example", "export", "extends", "exists", "false"
  , "finally", "for", "forall", "from", "fun", "generalizing", "have", "if", "import"
  , "in", "include", "inductive", "inductive_fixpoint", "infix", "infixl", "infixr"
  , "init_quot", "initialize", "instance", "leading_parser", "let", "local", "macro"
  , "macro_rules", "match", "meta", "mutual", "namespace", "nofun", "noncomputable"
  , "notation", "omit", "opaque", "open", "partial", "partial_fixpoint", "postfix"
  , "prefix", "private", "protected", "public", "recommended_spelling", "repeat", "return"
  , "scoped", "section", "set_option", "show", "simproc", "sorry", "structure", "syntax"
  , "tactic_alt", "termination_by", "then", "theorem", "trailing_parser", "true", "try"
  , "unif_hint", "universe", "universes", "unsafe", "unless", "using", "variable", "where"
  , "while", "with" ]

/-- Whether a character list begins with the fixed generated-declaration prefix `host`. -/
def hasHostGeneratedIdentifierPrefix : List Char → Bool
  | 'h' :: 'o' :: 's' :: 't' :: _ => true
  | _ => false

/-- The reserved identifier table contains no entry in the generated `host…` namespace. -/
theorem leanReservedIdentifierSegments_no_host_prefix :
    leanReservedIdentifierSegments.all
      (fun segment => !hasHostGeneratedIdentifierPrefix segment.toList) = true := by
  rfl

/-- Whether every character is legal after the first character of a generated Lean identifier. -/
def leanIdentifierRestSafe (text : String) : Bool :=
  text.toList.all fun char => leanIdentifierRestChars.contains char

/-- Identifier-rest safety composes across string concatenation. -/
theorem leanIdentifierRestSafe_append (left right : String)
    (hleft : leanIdentifierRestSafe left = true)
    (hright : leanIdentifierRestSafe right = true) :
    leanIdentifierRestSafe (left ++ right) = true := by
  unfold leanIdentifierRestSafe at hleft hright ⊢
  rw [String.toList_append, List.all_append, hleft, hright]
  rfl

/-- Conservative generated Lean identifier validator used at source/export boundaries. -/
def leanIdentifierSegment? (segment : String) : Bool :=
  match segment.toList with
  | [] => false
  | head :: tail =>
      (hasHostGeneratedIdentifierPrefix (head :: tail) ||
          !leanReservedIdentifierSegments.contains segment) &&
        leanIdentifierStartChars.contains head &&
          tail.all fun char => leanIdentifierRestChars.contains char

/-- A `host…` generated name is a valid identifier when its remaining characters are safe. -/
theorem leanIdentifierSegment_host_of_rest_safe (tail : String)
    (htail : leanIdentifierRestSafe tail = true) :
    leanIdentifierSegment? ("host" ++ tail) = true := by
  unfold leanIdentifierRestSafe at htail
  have htail' : ∀ char ∈ tail.toList, char ∈ leanIdentifierRestChars := by
    intro char hmem
    have hsafe := List.all_eq_true.mp htail char hmem
    simpa using hsafe
  unfold leanIdentifierRestChars at htail'
  unfold leanIdentifierSegment?
  rw [String.toList_append]
  rw [show "host".toList = ['h', 'o', 's', 't'] by rfl]
  simp [hasHostGeneratedIdentifierPrefix, leanIdentifierStartChars,
    leanIdentifierRestChars]
  exact ⟨by decide, by decide, by decide, by decide, htail'⟩

/-- A generated `host` name remains safe when assembled from three safe identifier bodies. -/
theorem leanIdentifierSegment_host_parts_safe (prefixText bodyText suffixText : String)
    (hprefix : leanIdentifierRestSafe prefixText = true)
    (hbody : leanIdentifierRestSafe bodyText = true)
    (hsuffix : leanIdentifierRestSafe suffixText = true) :
    leanIdentifierSegment? ("host" ++ prefixText ++ bodyText ++ suffixText) = true := by
  have hbodySuffix := leanIdentifierRestSafe_append bodyText suffixText hbody hsuffix
  have htail := leanIdentifierRestSafe_append prefixText (bodyText ++ suffixText)
    hprefix hbodySuffix
  simpa only [String.append_assoc] using
    leanIdentifierSegment_host_of_rest_safe (prefixText ++ (bodyText ++ suffixText)) htail

/-- Split a character list at one delimiter, preserving empty fields.

Unlike `String.splitOn`, this structural helper reduces in the kernel. -/
def splitCharListOn (delimiter : Char) : List Char → List (List Char)
  | [] => [[]]
  | char :: rest =>
      let fields := splitCharListOn delimiter rest
      if char == delimiter then
        [] :: fields
      else
        match fields with
        | [] => [[char]]
        | field :: remaining => (char :: field) :: remaining

/-- Conservative generated Lean module-name validator. -/
def leanModuleName? (moduleName : String) : Bool :=
  (splitCharListOn '.' moduleName.toList).all fun chars =>
    leanIdentifierSegment? (String.ofList chars)

/-- Conservative allowlist for generated option commands. -/
def leanOptionLine? (line : String) : Bool :=
  line = "set_option autoImplicit false" ||
    line = "set_option maxHeartbeats 1000000" ||
      line = "set_option maxRecDepth 10000"

/-- Characters accepted in generated file basenames. -/
def generatedFileNameChars : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_0123456789-.".toList

/-- Conservative basename validator for generated files. -/
def generatedFileName? (fileName : String) : Bool :=
  match fileName.toList with
  | [] => false
  | chars =>
      fileName != "." && fileName != ".." &&
        chars.all fun char => generatedFileNameChars.contains char

/-- Sanitized name used for private generated `.olean` roots when package paths cannot enter `LEAN_PATH`. -/
def leanPathSafeRootName (root : String) : String :=
  "root-" ++ toString (hash root)

/-- Require a boolean condition while validating generated host-request shape. -/
def requireHostRequestShape (condition : Bool) (message : String) : Except String Unit :=
  if condition then Except.ok () else Except.error message

/-- Reserved separator between an external request key and one generated child-package key segment. -/
def hostPackageKeySeparator : String :=
  "::"

/-- Characters accepted in one host-facing generated package-key segment. -/
def hostPackageKeySegmentChars : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_.".toList

/-- Conservative validator for one generated host package-key segment.

Segments are printable ASCII slugs and are not allowed to contain the reserved `::` separator;
exact ownership metadata, not string-prefix parsing, determines which molecule request owns a
generated child package. -/
def hostPackageKeySegment? (segment : String) : Bool :=
  match segment.toList with
  | [] => false
  | chars => chars.all fun char => hostPackageKeySegmentChars.contains char

/-- Canonical child-package key for a package owned by one external molecule request. -/
def hostScopedPackageKey (ownerRequestKey packageKeySuffix : String) : String :=
  ownerRequestKey ++ hostPackageKeySeparator ++ packageKeySuffix

/-- Fixed declaration name exported by every generated host module for its owner request key. -/
def hostOfficialStereoOwnerRequestKeyDeclarationName : String :=
  "hostOfficialStereoOwnerRequestKey"

/-- Fixed declaration name exported by every generated host module for its package-key suffix. -/
def hostOfficialStereoPackageKeySuffixDeclarationName : String :=
  "hostOfficialStereoPackageKeySuffix"

/-- Validate a generated namespace path as nonempty ASCII Lean identifiers. -/
def validateNamespacePath (label : String) (path : List String) : Except String Unit := do
  match path with
  | [] => Except.error (label ++ " must not be empty")
  | segments =>
      for segment in segments do
        requireHostRequestShape (leanIdentifierSegment? segment)
          (label ++ " contains an unsafe Lean namespace segment: " ++ reprStr segment)

/-- Validate a list of generated Lean names. -/
def validateLeanNames (label : String) : List String → Except String Unit
  | [] => Except.ok ()
  | name :: rest => do
      requireHostRequestShape (leanIdentifierSegment? name)
        (label ++ " contains an unsafe Lean identifier: " ++ reprStr name)
      validateLeanNames label rest

/-- A list whose entries all pass the identifier predicate passes generated-name validation. -/
theorem validateLeanNames_eq_ok_of_all (label : String) (names : List String)
    (hall : names.all leanIdentifierSegment? = true) :
    validateLeanNames label names = Except.ok () := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      have hparts := List.all_eq_true.mp hall
      have hname := hparts name (by simp)
      have hrestAll : rest.all leanIdentifierSegment? = true :=
        List.all_eq_true.mpr fun value hmem => hparts value (by simp [hmem])
      unfold validateLeanNames
      simp [requireHostRequestShape, hname, ih hrestAll]
      rfl

/-- Validate a list of generated import module names. -/
def validateModuleNames (label : String) : List String → Except String Unit
  | [] => Except.ok ()
  | name :: rest => do
      requireHostRequestShape (leanModuleName? name)
        (label ++ " contains an unsafe Lean module name: " ++ reprStr name)
      validateModuleNames label rest

/-- Validate generated option commands. -/
def validateOptionLines (label : String) : List String → Except String Unit
  | [] => Except.ok ()
  | line :: rest => do
      requireHostRequestShape (leanOptionLine? line)
        (label ++ " contains an unsafe generated option command: " ++ reprStr line)
      validateOptionLines label rest

/-- Validate a generated file basename. -/
def validateGeneratedFileName (label fileName : String) : Except String Unit :=
  requireHostRequestShape (generatedFileName? fileName)
    (label ++ " is not a safe generated file basename: " ++ reprStr fileName)

namespace HostLeanExpr

namespace AxialDescriptor

/-- Render an axial descriptor as a Lean expression. -/
def expr : AxialDescriptor → String
  | AxialDescriptor.Ra => "TetraStereo.OneCenter.AxialDescriptor.Ra"
  | AxialDescriptor.Sa => "TetraStereo.OneCenter.AxialDescriptor.Sa"

end AxialDescriptor

namespace PlanarDescriptor

/-- Render a planar descriptor as a Lean expression. -/
def expr : PlanarDescriptor → String
  | PlanarDescriptor.Rp => "TetraStereo.OneCenter.PlanarDescriptor.Rp"
  | PlanarDescriptor.Sp => "TetraStereo.OneCenter.PlanarDescriptor.Sp"

end PlanarDescriptor

namespace HelicalDescriptor

/-- Render a helical descriptor as a Lean expression. -/
def expr : HelicalDescriptor → String
  | HelicalDescriptor.P => "TetraStereo.OneCenter.HelicalDescriptor.P"
  | HelicalDescriptor.M => "TetraStereo.OneCenter.HelicalDescriptor.M"

end HelicalDescriptor

namespace OfficialStereogenicUnitKind

/-- Render an official stereogenic-unit kind as a Lean expression. -/
def expr : OfficialStereogenicUnitKind → String
  | OfficialStereogenicUnitKind.chiral =>
      "TetraStereo.OneCenter.OfficialStereogenicUnitKind.chiral"
  | OfficialStereogenicUnitKind.pseudoasymmetric =>
      "TetraStereo.OneCenter.OfficialStereogenicUnitKind.pseudoasymmetric"
  | OfficialStereogenicUnitKind.nonstereogenic =>
      "TetraStereo.OneCenter.OfficialStereogenicUnitKind.nonstereogenic"

end OfficialStereogenicUnitKind

namespace OfficialRule5DescriptorKind

/-- Render an official Rule-5 descriptor family as a Lean expression. -/
def expr : OfficialRule5DescriptorKind → String
  | OfficialRule5DescriptorKind.tetrahedralCenter =>
      "TetraStereo.OneCenter.OfficialRule5DescriptorKind.tetrahedralCenter"
  | OfficialRule5DescriptorKind.axisOrPlane =>
      "TetraStereo.OneCenter.OfficialRule5DescriptorKind.axisOrPlane"
  | OfficialRule5DescriptorKind.doubleBondOrCumulene =>
      "TetraStereo.OneCenter.OfficialRule5DescriptorKind.doubleBondOrCumulene"

end OfficialRule5DescriptorKind

namespace OfficialDescriptorSense

/-- Render an official senior/junior descriptor sense as a Lean expression. -/
def expr : OfficialDescriptorSense → String
  | OfficialDescriptorSense.senior => "TetraStereo.OneCenter.OfficialDescriptorSense.senior"
  | OfficialDescriptorSense.junior => "TetraStereo.OneCenter.OfficialDescriptorSense.junior"

end OfficialDescriptorSense

namespace OfficialRule5Descriptor

/-- Render an official Rule-5 descriptor as a Lean expression. -/
def expr (descriptor : OfficialRule5Descriptor) : String :=
  "{ kind := " ++ OfficialRule5DescriptorKind.expr descriptor.kind ++
    ", auxiliary := " ++ leanBoolExpr descriptor.auxiliary ++
    ", sense := " ++ OfficialDescriptorSense.expr descriptor.sense ++ " }"

end OfficialRule5Descriptor

namespace DoubleBondStereo

/-- Render a double-bond `E/Z` descriptor as a Lean expression. -/
def expr : DoubleBondStereo → String
  | DoubleBondStereo.E => "TetraStereo.OneCenter.DoubleBondStereo.E"
  | DoubleBondStereo.Z => "TetraStereo.OneCenter.DoubleBondStereo.Z"
  | DoubleBondStereo.unspecified => "TetraStereo.OneCenter.DoubleBondStereo.unspecified"

end DoubleBondStereo

namespace VirtualNodeResolutionPolicy

/-- Render a virtual-node resolution policy as a Lean expression. -/
def expr : VirtualNodeResolutionPolicy → String
  | VirtualNodeResolutionPolicy.exactDistance =>
      "TetraStereo.OneCenter.VirtualNodeResolutionPolicy.exactDistance"
  | VirtualNodeResolutionPolicy.kindFallback =>
      "TetraStereo.OneCenter.VirtualNodeResolutionPolicy.kindFallback"
  | VirtualNodeResolutionPolicy.kindOnly =>
      "TetraStereo.OneCenter.VirtualNodeResolutionPolicy.kindOnly"

end VirtualNodeResolutionPolicy

namespace DescriptorSourcePolicyProfile

/-- Render a descriptor-source policy profile as a Lean expression. -/
def expr (profile : DescriptorSourcePolicyProfile) : String :=
  "{ ordinaryAtomSources := " ++ leanBoolExpr profile.ordinaryAtomSources ++
    ", duplicateAtomSources := " ++ leanBoolExpr profile.duplicateAtomSources ++
    ", phantomSources := " ++ leanBoolExpr profile.phantomSources ++
    ", lonePairSources := " ++ leanBoolExpr profile.lonePairSources ++
    ", auxiliarySources := " ++ leanBoolExpr profile.auxiliarySources ++
    ", virtualNodeResolution := " ++
      VirtualNodeResolutionPolicy.expr profile.virtualNodeResolution ++ " }"

end DescriptorSourcePolicyProfile

namespace IndexedDetectedAxialUnit

/-- Render an indexed axial annotation as a Lean expression. -/
def expr (record : IndexedDetectedAxialUnit) : String :=
  "{ axisStart := " ++ toString record.axisStart ++
    ", axisEnd := " ++ toString record.axisEnd ++
    ", startHigh := " ++ toString record.startHigh ++
    ", startLow := " ++ toString record.startLow ++
    ", endHigh := " ++ toString record.endHigh ++
    ", endLow := " ++ toString record.endLow ++
    ", descriptor := " ++ AxialDescriptor.expr record.descriptor ++ " }"

end IndexedDetectedAxialUnit

namespace IndexedDetectedPlanarUnit

/-- Render an indexed planar annotation as a Lean expression. -/
def expr (record : IndexedDetectedPlanarUnit) : String :=
  "{ planeAtoms := " ++ leanNatListExpr record.planeAtoms ++
    ", pilotAtom := " ++ toString record.pilotAtom ++
    ", highReference := " ++ toString record.highReference ++
    ", lowReference := " ++ toString record.lowReference ++
    ", descriptor := " ++ PlanarDescriptor.expr record.descriptor ++ " }"

end IndexedDetectedPlanarUnit

namespace IndexedDetectedHelicalUnit

/-- Render an indexed helical annotation as a Lean expression. -/
def expr (record : IndexedDetectedHelicalUnit) : String :=
  "{ helixPath := " ++ leanNatListExpr record.helixPath ++
    ", frontReference := " ++ toString record.frontReference ++
    ", backReference := " ++ toString record.backReference ++
    ", descriptor := " ++ HelicalDescriptor.expr record.descriptor ++ " }"

end IndexedDetectedHelicalUnit

namespace IndexedDetectedConformationalState

/-- Render an indexed conformational annotation as a Lean expression. -/
def expr (record : IndexedDetectedConformationalState) : String :=
  "{ stateId := " ++ leanStringLit record.stateId ++
    ", support := " ++ leanNatListExpr record.support ++
    ", kind? := " ++ leanOptionExpr OfficialStereogenicUnitKind.expr record.kind? ++ " }"

end IndexedDetectedConformationalState

namespace IndexedDetectedEnsembleState

/-- Render an indexed ensemble annotation as a Lean expression. -/
def expr (record : IndexedDetectedEnsembleState) : String :=
  "{ stateId := " ++ leanStringLit record.stateId ++
    ", support := " ++ leanNatListExpr record.support ++
    ", kind? := " ++ leanOptionExpr OfficialStereogenicUnitKind.expr record.kind? ++ " }"

end IndexedDetectedEnsembleState

namespace IndexedDetectedAuxiliaryRule5Node

/-- Render an indexed auxiliary Rule-5-node annotation as a Lean expression. -/
def expr (record : IndexedDetectedAuxiliaryRule5Node) : String :=
  "{ anchor := " ++ toString record.anchor ++
    ", support := " ++ leanNatListExpr record.support ++
    ", descriptor := " ++ OfficialRule5Descriptor.expr record.descriptor ++
    ", rootDistance? := " ++ leanOptionExpr toString record.rootDistance? ++ " }"

end IndexedDetectedAuxiliaryRule5Node

namespace IndexedDetectedPhantomNode

/-- Render an indexed phantom-node annotation as a Lean expression. -/
def expr (record : IndexedDetectedPhantomNode) : String :=
  "{ anchor := " ++ toString record.anchor ++
    ", support := " ++ leanNatListExpr record.support ++
    ", rootDistance? := " ++ leanOptionExpr toString record.rootDistance? ++ " }"

end IndexedDetectedPhantomNode

namespace IndexedDetectedLonePairNode

/-- Render an indexed lone-pair-node annotation as a Lean expression. -/
def expr (record : IndexedDetectedLonePairNode) : String :=
  "{ anchor := " ++ toString record.anchor ++
    ", support := " ++ leanNatListExpr record.support ++
    ", rootDistance? := " ++ leanOptionExpr toString record.rootDistance? ++ " }"

end IndexedDetectedLonePairNode

namespace IndexedNoncenterStereoAnnotations

/-- Render typed indexed non-center annotations as a Lean expression. -/
def expr (annotations : IndexedNoncenterStereoAnnotations) : String :=
  "{ axes := " ++ leanListExpr IndexedDetectedAxialUnit.expr annotations.axes ++
    ", planes := " ++ leanListExpr IndexedDetectedPlanarUnit.expr annotations.planes ++
    ", helices := " ++ leanListExpr IndexedDetectedHelicalUnit.expr annotations.helices ++
    ", conformations := " ++
      leanListExpr IndexedDetectedConformationalState.expr annotations.conformations ++
    ", ensembles := " ++ leanListExpr IndexedDetectedEnsembleState.expr annotations.ensembles ++
    ", auxiliaryRule5Nodes := " ++
      leanListExpr IndexedDetectedAuxiliaryRule5Node.expr annotations.auxiliaryRule5Nodes ++
    ", phantomNodes := " ++ leanListExpr IndexedDetectedPhantomNode.expr annotations.phantomNodes ++
    ", lonePairNodes := " ++ leanListExpr IndexedDetectedLonePairNode.expr annotations.lonePairNodes ++
    " }"

end IndexedNoncenterStereoAnnotations

namespace Element

/-- Render an element as a Lean expression. -/
def expr : Element → String
  | Element.wildcard => "TetraStereo.OneCenter.Element.wildcard"
  | Element.H => "TetraStereo.OneCenter.Element.H"
  | Element.B => "TetraStereo.OneCenter.Element.B"
  | Element.C => "TetraStereo.OneCenter.Element.C"
  | Element.N => "TetraStereo.OneCenter.Element.N"
  | Element.O => "TetraStereo.OneCenter.Element.O"
  | Element.F => "TetraStereo.OneCenter.Element.F"
  | Element.P => "TetraStereo.OneCenter.Element.P"
  | Element.S => "TetraStereo.OneCenter.Element.S"
  | Element.Na => "TetraStereo.OneCenter.Element.Na"
  | Element.Si => "TetraStereo.OneCenter.Element.Si"
  | Element.Ge => "TetraStereo.OneCenter.Element.Ge"
  | Element.As => "TetraStereo.OneCenter.Element.As"
  | Element.Se => "TetraStereo.OneCenter.Element.Se"
  | Element.Sn => "TetraStereo.OneCenter.Element.Sn"
  | Element.Sb => "TetraStereo.OneCenter.Element.Sb"
  | Element.Te => "TetraStereo.OneCenter.Element.Te"
  | Element.Pb => "TetraStereo.OneCenter.Element.Pb"
  | Element.Bi => "TetraStereo.OneCenter.Element.Bi"
  | Element.Cl => "TetraStereo.OneCenter.Element.Cl"
  | Element.Br => "TetraStereo.OneCenter.Element.Br"
  | Element.I => "TetraStereo.OneCenter.Element.I"

end Element

namespace TetrahedralInputParity

/-- Render a tetrahedral input parity as a Lean expression. -/
def expr : TetrahedralInputParity → String
  | TetrahedralInputParity.anticlockwise =>
      "TetraStereo.OneCenter.TetrahedralInputParity.anticlockwise"
  | TetrahedralInputParity.clockwise =>
      "TetraStereo.OneCenter.TetrahedralInputParity.clockwise"

end TetrahedralInputParity

namespace ParsedBondKind

/-- Render a parsed bond kind as a Lean expression. -/
def expr : ParsedBondKind → String
  | ParsedBondKind.unspecified => "TetraStereo.OneCenter.ParsedBondKind.unspecified"
  | ParsedBondKind.single => "TetraStereo.OneCenter.ParsedBondKind.single"
  | ParsedBondKind.double => "TetraStereo.OneCenter.ParsedBondKind.double"
  | ParsedBondKind.triple => "TetraStereo.OneCenter.ParsedBondKind.triple"
  | ParsedBondKind.aromatic => "TetraStereo.OneCenter.ParsedBondKind.aromatic"
  | ParsedBondKind.up => "TetraStereo.OneCenter.ParsedBondKind.up"
  | ParsedBondKind.down => "TetraStereo.OneCenter.ParsedBondKind.down"

end ParsedBondKind

namespace AtomSpec

/-- Render an optional natural-number field as a Lean expression. -/
def natOptionExpr : Option ℕ → String
  | none => "none"
  | some value => "some " ++ toString value

/-- Render an optional tetrahedral input parity as a Lean expression. -/
def parityOptionExpr : Option TetrahedralInputParity → String
  | none => "none"
  | some parity => "some " ++ TetrahedralInputParity.expr parity

/-- Render an atom specification as a Lean expression. -/
def expr (atom : AtomSpec) : String :=
  "{ element := " ++ Element.expr atom.element ++
    ", isotope? := " ++ natOptionExpr atom.isotope? ++
    ", charge := " ++ toString atom.charge ++
    ", explicitHydrogens? := " ++ natOptionExpr atom.explicitHydrogens? ++
    ", aromatic := " ++ leanBoolExpr atom.aromatic ++
    ", tetrahedral? := " ++ parityOptionExpr atom.tetrahedral? ++ " }"

end AtomSpec

namespace RawBond

/-- Render a raw bond as a Lean expression. -/
def expr (bond : RawBond) : String :=
  "{ source := " ++ toString bond.source ++
    ", target := " ++ toString bond.target ++
    ", kind := " ++ ParsedBondKind.expr bond.kind ++ " }"

end RawBond

namespace AromaticCycle

/-- Render an aromatic-cycle candidate as a Lean expression. -/
def expr (cycle : AromaticCycle) : String :=
  "({ atoms := " ++ leanNatListExpr cycle.atoms ++
    " } : TetraStereo.OneCenter.AromaticCycle)"

end AromaticCycle

namespace ChemistryImportFormat

/-- Render a chemistry import format as a Lean expression. -/
def expr : ChemistryImportFormat → String
  | ChemistryImportFormat.openSMILES => "TetraStereo.OneCenter.ChemistryImportFormat.openSMILES"
  | ChemistryImportFormat.molfileV2000 =>
      "TetraStereo.OneCenter.ChemistryImportFormat.molfileV2000"
  | ChemistryImportFormat.molfileV3000 =>
      "TetraStereo.OneCenter.ChemistryImportFormat.molfileV3000"
  | ChemistryImportFormat.inChI => "TetraStereo.OneCenter.ChemistryImportFormat.inChI"
  | ChemistryImportFormat.rdkitMol => "TetraStereo.OneCenter.ChemistryImportFormat.rdkitMol"
  | ChemistryImportFormat.rdkitJSON => "TetraStereo.OneCenter.ChemistryImportFormat.rdkitJSON"
  | ChemistryImportFormat.rawMolecule =>
      "TetraStereo.OneCenter.ChemistryImportFormat.rawMolecule"

end ChemistryImportFormat

namespace ChemistryImportTrust

/-- Render an import-trust boundary as a Lean expression. -/
def expr : ChemistryImportTrust → String
  | ChemistryImportTrust.internalLeanParser =>
      "TetraStereo.OneCenter.ChemistryImportTrust.internalLeanParser"
  | ChemistryImportTrust.externalAdapter =>
      "TetraStereo.OneCenter.ChemistryImportTrust.externalAdapter"
  | ChemistryImportTrust.externalToolkit =>
      "TetraStereo.OneCenter.ChemistryImportTrust.externalToolkit"
  | ChemistryImportTrust.userSuppliedRawMolecule =>
      "TetraStereo.OneCenter.ChemistryImportTrust.userSuppliedRawMolecule"
  | ChemistryImportTrust.proofCertifiedAdapter =>
      "TetraStereo.OneCenter.ChemistryImportTrust.proofCertifiedAdapter"

end ChemistryImportTrust

namespace ValenceNormalizationPolicy

/-- Render a valence-normalization policy as a Lean expression. -/
def expr : ValenceNormalizationPolicy → String
  | ValenceNormalizationPolicy.lightweightLeanCheck =>
      "TetraStereo.OneCenter.ValenceNormalizationPolicy.lightweightLeanCheck"
  | ValenceNormalizationPolicy.trustExternalValence =>
      "TetraStereo.OneCenter.ValenceNormalizationPolicy.trustExternalValence"
  | ValenceNormalizationPolicy.skipValenceCheck =>
      "TetraStereo.OneCenter.ValenceNormalizationPolicy.skipValenceCheck"

end ValenceNormalizationPolicy

namespace AromaticityNormalizationPolicy

/-- Render an aromaticity-normalization policy as a Lean expression. -/
def expr : AromaticityNormalizationPolicy → String
  | AromaticityNormalizationPolicy.openSMILESDefaults =>
      "TetraStereo.OneCenter.AromaticityNormalizationPolicy.openSMILESDefaults"
  | AromaticityNormalizationPolicy.preserveInputFlags =>
      "TetraStereo.OneCenter.AromaticityNormalizationPolicy.preserveInputFlags"
  | AromaticityNormalizationPolicy.trustExternalAromaticity =>
      "TetraStereo.OneCenter.AromaticityNormalizationPolicy.trustExternalAromaticity"
  | AromaticityNormalizationPolicy.suppliedCandidateCycles =>
      "TetraStereo.OneCenter.AromaticityNormalizationPolicy.suppliedCandidateCycles"

end AromaticityNormalizationPolicy

namespace ResonanceNormalizationPolicy

/-- Render a resonance-normalization policy as a Lean expression. -/
def expr : ResonanceNormalizationPolicy → String
  | ResonanceNormalizationPolicy.localizedInputGraph =>
      "TetraStereo.OneCenter.ResonanceNormalizationPolicy.localizedInputGraph"
  | ResonanceNormalizationPolicy.recordAromaticDelocalization =>
      "TetraStereo.OneCenter.ResonanceNormalizationPolicy.recordAromaticDelocalization"
  | ResonanceNormalizationPolicy.trustExternalResonanceClass =>
      "TetraStereo.OneCenter.ResonanceNormalizationPolicy.trustExternalResonanceClass"

end ResonanceNormalizationPolicy

namespace TautomerNormalizationPolicy

/-- Render a tautomer-normalization policy as a Lean expression. -/
def expr : TautomerNormalizationPolicy → String
  | TautomerNormalizationPolicy.fixedHydrogenOnly =>
      "TetraStereo.OneCenter.TautomerNormalizationPolicy.fixedHydrogenOnly"
  | TautomerNormalizationPolicy.fixedHydrogenWithMobileMetadata =>
      "TetraStereo.OneCenter.TautomerNormalizationPolicy.fixedHydrogenWithMobileMetadata"
  | TautomerNormalizationPolicy.trustExternalCanonicalTautomer =>
      "TetraStereo.OneCenter.TautomerNormalizationPolicy.trustExternalCanonicalTautomer"

end TautomerNormalizationPolicy

namespace StereobondNormalizationPolicy

/-- Render a stereobond-normalization policy as a Lean expression. -/
def expr : StereobondNormalizationPolicy → String
  | StereobondNormalizationPolicy.preserveInputAnnotations =>
      "TetraStereo.OneCenter.StereobondNormalizationPolicy.preserveInputAnnotations"
  | StereobondNormalizationPolicy.trustExternalStereoPerception =>
      "TetraStereo.OneCenter.StereobondNormalizationPolicy.trustExternalStereoPerception"
  | StereobondNormalizationPolicy.ignoreInputStereo =>
      "TetraStereo.OneCenter.StereobondNormalizationPolicy.ignoreInputStereo"

end StereobondNormalizationPolicy

namespace ChemistryNormalizationPolicy

/-- Render a full chemistry-normalization policy as a Lean expression. -/
def expr (policy : ChemistryNormalizationPolicy) : String :=
  "{ valence := " ++ ValenceNormalizationPolicy.expr policy.valence ++
    ", aromaticity := " ++ AromaticityNormalizationPolicy.expr policy.aromaticity ++
    ", resonance := " ++ ResonanceNormalizationPolicy.expr policy.resonance ++
    ", tautomer := " ++ TautomerNormalizationPolicy.expr policy.tautomer ++
    ", stereobonds := " ++ StereobondNormalizationPolicy.expr policy.stereobonds ++
    " }"

end ChemistryNormalizationPolicy

namespace ChemistryImportSource

/-- Render optional source metadata as a Lean expression. -/
def stringOptionExpr : Option String → String
  | none => "none"
  | some value => "some " ++ leanStringLit value

/-- Render import-source metadata as a Lean expression. -/
def expr (source : ChemistryImportSource) : String :=
  "{ format := " ++ ChemistryImportFormat.expr source.format ++
    ", name? := " ++ stringOptionExpr source.name? ++
    ", payloadHash? := " ++ stringOptionExpr source.payloadHash? ++ " }"

end ChemistryImportSource

namespace RawMolecule

/-- Render an atom list as a Lean expression. -/
def atomListExpr (atoms : List AtomSpec) : String :=
  "[" ++ String.intercalate ", " (atoms.map AtomSpec.expr) ++ "]"

/-- Render a bond list as a Lean expression. -/
def bondListExpr (bonds : List RawBond) : String :=
  "[" ++ String.intercalate ", " (bonds.map RawBond.expr) ++ "]"

/-- Preserve per-atom written neighbor order in generated host modules. -/
def neighborOrderExpr (order : List (List ℕ)) : String :=
  "[" ++ String.intercalate ", " (order.map leanNatListExpr) ++ "]"

/-- Preserve the source-introduction prefix, including component roots and legacy absence. -/
def introductionPredecessorsExpr (predecessors : List (Option ℕ)) : String :=
  "[" ++ String.intercalate ", " (predecessors.map AtomSpec.natOptionExpr) ++ "]"

end RawMolecule

namespace ExternalRawMoleculePacket

/-- Render an aromatic-cycle list as a Lean expression. -/
def aromaticCycleListExpr (cycles : List AromaticCycle) : String :=
  "[" ++ String.intercalate ", " (cycles.map AromaticCycle.expr) ++ "]"

end ExternalRawMoleculePacket

end HostLeanExpr

/-! ### Host request compiler -/






























inductive HostOfficialStereoCertificateTarget where
  | computedComparison
  | comparison (expected : Ordering)
  | refusal (reason : RefusalReason)
  deriving DecidableEq, Repr

namespace HostOfficialStereoCertificateTarget

/-- Render the theorem statement for a generated target-claim proof.

`computedComparison` renders the optional-outcome reflexivity directly.  The literal `comparison`
and `refusal` forms render the transaction's own claim definitions, so their expected ordering or
refusal reason remains an actual emitted literal rather than a tautology. -/
def statement (target : HostOfficialStereoCertificateTarget) (requestExpr : String) : String :=
  match target with
  | computedComparison =>
      "(" ++ requestExpr ++ ").outcome = (" ++ requestExpr ++ ").outcome"
  | comparison expected =>
      "TetraStereo.Engine.OfficialStereoTransactionClaim " ++ requestExpr ++ " " ++
        orderingExpr expected
  | refusal reason =>
      "TetraStereo.Engine.OfficialStereoRefusalClaim " ++ requestExpr ++ " " ++
        refusalReasonExpr reason

/-- Render the proof term for a generated target-claim proof.

`computedComparison` is the compatibility-reflexivity equality, so `rfl` suffices.  A literal
comparison claim is a single equation checked by `rfl`.  A refusal claim is a conjunction of
"not certificate-ready" and "the declared reason is the one this request's own bounded certificate
justifies", so it needs the anonymous constructor.  The emitted term is checked by the kernel when
the generated module is compiled; this renderer never inserts a fallback value or a context
assumption. -/
def proofTerm (target : HostOfficialStereoCertificateTarget) : String :=
  match target with
  | computedComparison => "  rfl"
  | comparison _ => "  rfl"
  | refusal _ => "  ⟨rfl, rfl⟩"

/-- Documentation comment emitted for the target-claim theorem.

`computedComparison` is labelled as compatibility reflexivity so generated source does not present
it as a chemistry result. -/
def documentation (target : HostOfficialStereoCertificateTarget) : String :=
  match target with
  | computedComparison =>
      "/-- Compatibility reflexivity for this request's optional outcome: this proves only " ++
        "`outcome = outcome` and asserts no computed comparison value. -/"
  | comparison _ =>
      "/-- The generated request's bounded certificate exhibits the declared literal comparison " ++
        "outcome. -/"
  | refusal _ =>
      "/-- The generated request is not certificate-ready and its own computed refusal reason is " ++
        "the declared literal. A `none` certificate justifies only `implementationLimit`. -/"

end HostOfficialStereoCertificateTarget

/-- Structured input for compiling one host official-stereo request into a Lean module.

`definitionPrefix` and names are intentionally strings: they are part of the host API contract and
must be valid Lean identifiers/module names in generated output.  Non-center detector annotations
and descriptor-source policies are typed host data that this compiler serializes into Lean source
directly. -/
structure HostOfficialStereoRequest where
  key : String
  description : String
  ownerRequestKey : String := ""
  packageKeySuffix : String := ""
  moduleFileName : String
  namespacePath : List String := ["TetraStereoGenerated", "HostModules"]
  moduleImports : List String := ["TetraStereo.Engine.HostModuleCompiler"]
  options : List String := ["set_option autoImplicit false", "set_option maxHeartbeats 1000000"]
  definitionPrefix : String
  packet : ExternalRawMoleculePacket
  annotations : IndexedNoncenterStereoAnnotations := {}
  centerAtom : ℕ
  left : ℕ
  right : ℕ
  profile : DescriptorSourcePolicyProfile := DescriptorSourcePolicyProfile.exactDistance
  graphFuel : ℕ := 0
  scheduleFuel : ℕ := 0
  branchFuel : ℕ := 0
  target : HostOfficialStereoCertificateTarget :=
    HostOfficialStereoCertificateTarget.refusal RefusalReason.unresolvedOfficialPriorities
  certificateFileName : String
  certificateTheoremName : String
  certificateNamespacePath : List String := ["TetraStereoGenerated", "Certificates"]

namespace HostOfficialStereoRequest

/-- Fully qualified name for a local generated declaration. -/
def fullName (request : HostOfficialStereoRequest) (name : String) : String :=
  leanQualifiedName request.namespacePath name

def ownerRequestKeyName (_request : HostOfficialStereoRequest) : String :=
  hostOfficialStereoOwnerRequestKeyDeclarationName
def packageKeySuffixName (_request : HostOfficialStereoRequest) : String :=
  hostOfficialStereoPackageKeySuffixDeclarationName
def rawName (request : HostOfficialStereoRequest) : String := request.definitionPrefix ++ "Raw"
def packetName (request : HostOfficialStereoRequest) : String := request.definitionPrefix ++ "Packet"
def importRequestName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "ImportRequest"
def importResultName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "ImportResult"
def safeImportTheoremName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "SafeImport_eq_ok"
def intakePlanName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "IntakeTheoremPlan"
def intakeSuccessName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "IntakeSuccess"
def intakeSuccessCheckedName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "IntakeSuccess_checked"
def exportSpecName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "ExportSpec"
def queryName (request : HostOfficialStereoRequest) : String := request.definitionPrefix ++ "Query"
def blueprintName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "Blueprint"
def preparedResultName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "PreparedResult"
def preparedResultBuildsName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "PreparedResult_builds"
def centerMemTheoremName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "Center_mem"
def requestFallbackName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "RequestFallback"
def requestName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "Request"
def targetClaimTheoremName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "Request_target_claim"
def hostQueryBuildsName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "HostQueryBuilds"
def sourceSpecName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "HostQuerySourceSpec"
def sourceEntryName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "CertificateSourceEntry"
def sourceEntryKeyTheoremName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "CertificateSourceEntry_key"
def hostQueryClaimTheoremName (request : HostOfficialStereoRequest) : String :=
  request.definitionPrefix ++ "HostQueryClaim_checked"

/-- Local declaration names emitted by the generated host module. -/
def hostLocalDeclarationNames (request : HostOfficialStereoRequest) : List String :=
  [ request.ownerRequestKeyName
  , request.packageKeySuffixName
  , request.rawName
  , request.packetName
  , request.importRequestName
  , request.importResultName
  , request.safeImportTheoremName
  , request.intakePlanName
  , request.intakeSuccessName
  , request.intakeSuccessCheckedName
  , request.exportSpecName
  , request.queryName
  , request.blueprintName
  , request.preparedResultName
  , request.preparedResultBuildsName
  , request.centerMemTheoremName
  , request.requestFallbackName
  , request.requestName
  , request.targetClaimTheoremName
  , request.hostQueryBuildsName
  , request.sourceSpecName
  , request.sourceEntryName
  , request.sourceEntryKeyTheoremName
  , request.hostQueryClaimTheoremName ]

/-- Fully-qualified declaration names emitted by the generated host module. -/
def hostDeclarationNames (request : HostOfficialStereoRequest) : List String :=
  request.hostLocalDeclarationNames.map request.fullName

/-- Lean module name corresponding to the generated namespace path. -/
def moduleName (request : HostOfficialStereoRequest) : String :=
  String.intercalate "." request.namespacePath

/-- File stem for a generated Lean file name.

The suffix match is structural so host-request validation remains reducible in the kernel. -/
def hostGeneratedLeanFileStem (fileName : String) : String :=
  match fileName.toList.reverse with
  | 'n' :: 'a' :: 'e' :: 'l' :: '.' :: stemRev => String.ofList stemRev.reverse
  | _ => fileName

/-- Lean module name corresponding to the generated downstream certificate source. -/
def certificateModuleName (request : HostOfficialStereoRequest) : String :=
  leanQualifiedName request.certificateNamespacePath
    (hostGeneratedLeanFileStem request.certificateFileName)

/-- Slash-separated file stem corresponding to a Lean namespace/module path. -/
def pathStem (namespacePath : List String) : String :=
  String.intercalate "/" namespacePath

/-- Source path for a generated Lean module under a package root. -/
def leanSourcePathOfNamespace (packageRoot : String) (namespacePath : List String) :
    System.FilePath :=
  System.FilePath.mk (packageRoot ++ "/" ++ pathStem namespacePath ++ ".lean")

/-- OLean path for a generated Lean module under a package root. -/
def leanOLeanPathOfNamespace (packageRoot : String) (namespacePath : List String) :
    System.FilePath :=
  System.FilePath.mk (packageRoot ++ "/" ++ pathStem namespacePath ++ ".olean")

/-- Private generated-olean root for this host package. -/
def packageOLeanRoot (_request : HostOfficialStereoRequest) (packageRoot : String) : String :=
  if leanPathEntryHasSeparator packageRoot then
    "/tmp/tetrastereo-generated-olean/" ++ leanPathSafeRootName packageRoot
  else
    packageRoot ++ "/.olean"

/-- Importable source path for this generated host module under a package root. -/
def packageHostModulePath (request : HostOfficialStereoRequest) (packageRoot : String) :
    System.FilePath :=
  leanSourcePathOfNamespace packageRoot request.namespacePath

/-- Compiled olean path for this generated host module under a package root. -/
def packageHostModuleOLeanPath (request : HostOfficialStereoRequest) (packageRoot : String) :
    System.FilePath :=
  leanOLeanPathOfNamespace (request.packageOLeanRoot packageRoot) request.namespacePath

/-- Source path for the downstream generated certificate under a package root. -/
def packageCertificatePath (request : HostOfficialStereoRequest) (packageRoot : String) :
    System.FilePath :=
  System.FilePath.mk
    (packageRoot ++ "/" ++ pathStem request.certificateNamespacePath ++ "/" ++
      request.certificateFileName)

/-- Lean expression for a generated namespace-path list. -/
def namespacePathExpr (path : List String) : String :=
  leanStringListExpr path

/-- Validate host-supplied names that affect generated Lean syntax or generated file paths. -/
def validateGeneratedShape (request : HostOfficialStereoRequest) : Except String Unit := do
  requireHostRequestShape (request.key != "")
    "host official-stereo package key must not be empty"
  requireHostRequestShape
    ((request.ownerRequestKey == "" && request.packageKeySuffix == "") ||
      (request.ownerRequestKey != "" &&
        hostPackageKeySegment? request.ownerRequestKey &&
          hostPackageKeySegment? request.packageKeySuffix &&
            request.key == hostScopedPackageKey request.ownerRequestKey request.packageKeySuffix))
    "host official-stereo package key owner/suffix metadata must exactly match the key"
  validateNamespacePath "namespacePath" request.namespacePath
  validateNamespacePath "certificateNamespacePath" request.certificateNamespacePath
  validateModuleNames "moduleImports" request.moduleImports
  validateOptionLines "options" request.options
  validateGeneratedFileName "moduleFileName" request.moduleFileName
  validateGeneratedFileName "certificateFileName" request.certificateFileName
  requireHostRequestShape request.packet.raw.admissible?
    "host official-stereo raw molecule is not admissible"
  requireHostRequestShape (request.moduleName ≠ request.certificateModuleName)
    "host official-stereo package has colliding host-module and certificate module paths"
  requireHostRequestShape
    (if request.namespacePath = request.certificateNamespacePath then
      !request.hostLocalDeclarationNames.contains request.certificateTheoremName
    else
      true)
    "host official-stereo package has colliding host-module and certificate declarations"
  validateLeanNames "generated names"
    (request.definitionPrefix :: request.certificateTheoremName ::
      request.hostLocalDeclarationNames)

/-- Render exact owner metadata for generated suite/target-certificate provenance checks. -/
def ownerMetadataDeclarations (request : HostOfficialStereoRequest) : List String :=
  [ "/-- External molecule-analysis request key that owns this generated host module. -/"
  , "def " ++ request.ownerRequestKeyName ++ " : String :="
  , "  " ++ leanStringLit request.ownerRequestKey
  , ""
  , "/-- Single package-key segment used under the owning molecule-analysis request. -/"
  , "def " ++ request.packageKeySuffixName ++ " : String :="
  , "  " ++ leanStringLit request.packageKeySuffix
  ]

/-- Render the host raw-molecule declaration. -/
def rawDeclaration (request : HostOfficialStereoRequest) : List String :=
  [ "/-- Host-compiled raw molecule. -/"
  , "def " ++ request.rawName ++ " : TetraStereo.OneCenter.RawMolecule where"
  , "  atoms := " ++ HostLeanExpr.RawMolecule.atomListExpr request.packet.raw.atoms
  , "  bonds := " ++ HostLeanExpr.RawMolecule.bondListExpr request.packet.raw.bonds
  , "  neighborOrder := " ++
      HostLeanExpr.RawMolecule.neighborOrderExpr request.packet.raw.neighborOrder
  , "  introductionPredecessors := " ++
      HostLeanExpr.RawMolecule.introductionPredecessorsExpr
        request.packet.raw.introductionPredecessors
  ]

/-- Render the host packet declaration. -/
def packetDeclaration (request : HostOfficialStereoRequest) : List String :=
  [ "/-- Host-compiled external molecule packet. -/"
  , "def " ++ request.packetName ++ " : TetraStereo.OneCenter.ExternalRawMoleculePacket where"
  , "  source := " ++ HostLeanExpr.ChemistryImportSource.expr request.packet.source
  , "  trust := " ++ HostLeanExpr.ChemistryImportTrust.expr request.packet.trust
  , "  raw := " ++ request.rawName
  , "  policy := " ++ HostLeanExpr.ChemistryNormalizationPolicy.expr request.packet.policy
  , "  aromaticCycles := " ++
      HostLeanExpr.ExternalRawMoleculePacket.aromaticCycleListExpr request.packet.aromaticCycles
  , "  notes := " ++ leanStringListExpr request.packet.notes
  ]

/-- Render intake declarations and the checked intake success. -/
def intakeDeclarations (request : HostOfficialStereoRequest) : List String :=
  let successFull := request.fullName request.intakeSuccessName
  let successCheckedFull := request.fullName request.intakeSuccessCheckedName
  [ "/-- Host-compiled intake request. -/"
  , "def " ++ request.importRequestName ++ " : TetraStereo.Engine.ImportRequest :="
  , "  TetraStereo.Engine.ImportRequest.bridgePacket " ++ request.packetName
  , ""
  , "/-- Host-compiled concrete import result. -/"
  , "def " ++ request.importResultName ++ " : TetraStereo.OneCenter.ChemistryImportResult :="
  , "  TetraStereo.OneCenter.importExternalRawMoleculePacket " ++ request.packetName
  , ""
  , "/-- The generated bridge packet passes the checked intake boundary. -/"
  , "theorem " ++ request.safeImportTheoremName ++ " :"
  , "    " ++ request.importRequestName ++ ".safeImport? = Except.ok " ++
      request.importResultName ++ " :="
  , "  rfl"
  , ""
  , "/-- Render plan for the generated intake certificate. -/"
  , "def " ++ request.intakePlanName ++ " : TetraStereo.Engine.PublicIntakeTheoremPlan where"
  , "  imports := [" ++ leanStringLit request.moduleName ++ "]"
  , "  namespacePath := " ++ namespacePathExpr request.certificateNamespacePath
  , "  theoremName := " ++ leanStringLit (request.definitionPrefix ++ "_intake_imports")
  , "  statement := " ++ leanStringLit (successFull ++ ".artifact.claim")
  , "  proofTerm := " ++ leanStringLit ("  exact " ++ successCheckedFull)
  , ""
  , "/-- Checked intake success emitted by the host module compiler. -/"
  , "def " ++ request.intakeSuccessName ++ " :"
  , "    TetraStereo.Engine.CertifiedIntakeSuccess " ++ request.importRequestName ++ " where"
  , "  result := " ++ request.importResultName
  , "  success := " ++ request.safeImportTheoremName
  , "  rawAdmissible :="
  , "    (TetraStereo.OneCenter.RawMolecule.admissible?_eq_true_iff " ++
      request.rawName ++ ").1 rfl"
  , "  normalizedAdmissible :="
  , "    TetraStereo.OneCenter.RawMolecule.normalizeUnspecifiedBonds_admissible " ++
      request.rawName ++
      " ((TetraStereo.OneCenter.RawMolecule.admissible?_eq_true_iff " ++
      request.rawName ++ ").1 rfl)"
  , "  theoremPlan := " ++ request.intakePlanName
  , "  artifact :="
  , "    TetraStereo.Engine.compilePublicIntakeSuccess " ++ request.intakePlanName ++ " " ++
      request.importRequestName ++ " " ++ request.importResultName ++ " " ++
      request.safeImportTheoremName
  , "  artifact_eq := rfl"
  , ""
  , "/-- The generated intake artifact is checked. -/"
  , "theorem " ++ request.intakeSuccessCheckedName ++ " :"
  , "    " ++ request.intakeSuccessName ++ ".artifact.claim :="
  , "  " ++ request.intakeSuccessName ++ ".artifact_checked"
  ]

/-- Render the compact official-stereo query and export metadata. -/
def queryDeclarations (request : HostOfficialStereoRequest) : List String :=
  [ "/-- Export metadata for the generated official-stereo host query. -/"
  , "def " ++ request.exportSpecName ++ " : TetraStereo.Engine.OfficialStereoExportSpec where"
  , "  key := " ++ leanStringLit request.key
  , "  description := " ++ leanStringLit request.description
  , "  fileName := " ++ leanStringLit request.certificateFileName
  , "  imports := [" ++ leanStringLit request.moduleName ++ "]"
  , "  namespacePath := " ++ namespacePathExpr request.certificateNamespacePath
  , "  theoremName := " ++ leanStringLit request.certificateTheoremName
  , "  requestExpr := " ++ leanStringLit (request.fullName request.requestName)
  , "  proofTerm := " ++ leanStringLit ("  exact " ++ request.fullName request.targetClaimTheoremName)
  , ""
  , "/-- Compact official-stereo query emitted from the host request. -/"
  , "def " ++ request.queryName ++ " :"
  , "    TetraStereo.Engine.IntakeOfficialStereoQuery " ++ request.importRequestName ++ " " ++
      request.intakeSuccessName ++ " where"
  , "  annotations := " ++ HostLeanExpr.IndexedNoncenterStereoAnnotations.expr request.annotations
  , "  centerAtom := ⟨" ++ toString request.centerAtom ++ ", by decide⟩"
  , "  left := ⟨" ++ toString request.left ++ ", by decide⟩"
  , "  right := ⟨" ++ toString request.right ++ ", by decide⟩"
  , "  profile := " ++ HostLeanExpr.DescriptorSourcePolicyProfile.expr request.profile
  , "  graphFuel := " ++ toString request.graphFuel
  , "  scheduleFuel := " ++ toString request.scheduleFuel
  , "  branchFuel := " ++ toString request.branchFuel
  , "  exportSpec := " ++ request.exportSpecName
  , ""
  , "/-- Normalized blueprint induced by the generated compact query. -/"
  , "def " ++ request.blueprintName ++ " : TetraStereo.Engine.OfficialStereoRequestBlueprint :="
  , "  " ++ request.queryName ++ ".toSpec.toBlueprint"
  , ""
  , "/-- Prepared official-stereo transaction produced by the generated host query. -/"
  , "def " ++ request.preparedResultName ++ " :"
  , "    Except TetraStereo.Engine.OfficialStereoBuildFailure " ++
      "TetraStereo.Engine.PreparedOfficialStereoTransaction :="
  , "  TetraStereo.Engine.prepareOfficialStereoTransactionFromIntakeQuery " ++ request.queryName
  , ""
  , "/-- The generated compact host query builds a prepared transaction. -/"
  , "theorem " ++ request.preparedResultBuildsName ++ " :"
  , "    (match " ++ request.preparedResultName ++ " with"
  , "      | Except.ok _ => true"
  , "      | Except.error _ => false) = true :="
  , "  rfl"
  ]

/-- Render the request target claim and host-query certificate declarations. -/
def certificateDeclarations (request : HostOfficialStereoRequest) : List String :=
  let queryFull := request.fullName request.queryName
  let buildFull := request.fullName request.hostQueryBuildsName
  [ "/-- The selected atom is detected as a tetrahedral center. -/"
  , "theorem " ++ request.centerMemTheoremName ++ " :"
  , "    (⟨" ++ toString request.centerAtom ++
      ", by decide⟩ : Fin " ++ request.blueprintName ++ ".normalized.parsed.atomCount) ∈"
  , "      " ++ request.blueprintName ++ ".molecule.centers := by"
  , "  simp [" ++ request.blueprintName ++ ", " ++ request.queryName ++ ","
  , "    TetraStereo.Engine.IntakeOfficialStereoQuery.toSpec,"
  , "    TetraStereo.Engine.IntakeOfficialStereoSpec.toBlueprint,"
  , "    TetraStereo.Engine.OfficialStereoRequestBlueprint.molecule,"
  , "    TetraStereo.Engine.OfficialStereoRequestBlueprint.graph,"
  , "    TetraStereo.OneCenter.MoleculeGraph.detectedMultiCenterMolecule,"
  , "    TetraStereo.OneCenter.MoleculeGraph.tetrahedralCenterSet]"
  , "  decide"
  , ""
  , "/-- Fallback official-stereo request used only to make extraction total. -/"
  , "def " ++ request.requestFallbackName ++ " : TetraStereo.Engine.OfficialStereoRequest :="
  , "  { normalized := " ++ request.blueprintName ++ ".normalized"
  , "    annotations := " ++ request.blueprintName ++ ".annotations"
  , "    molecule := " ++ request.blueprintName ++ ".molecule"
  , "    profile := " ++ request.blueprintName ++ ".profile"
  , "    graphFuel := " ++ request.blueprintName ++ ".graphFuel"
  , "    scheduleFuel := " ++ request.blueprintName ++ ".scheduleFuel"
  , "    branchFuel := " ++ request.blueprintName ++ ".branchFuel"
  , "    center := ⟨⟨" ++ toString request.centerAtom ++ ", by decide⟩, " ++
      request.centerMemTheoremName ++ "⟩"
  , "    localMolecule :="
  , "      " ++ request.blueprintName ++ ".molecule.toOneCenterMolecule"
  , "        ⟨⟨" ++ toString request.centerAtom ++ ", by decide⟩, " ++
      request.centerMemTheoremName ++ "⟩"
  , "    left := " ++ request.queryName ++ ".left"
  , "    right := " ++ request.queryName ++ ".right"
  , "    theoremPlan := " ++ request.queryName ++ ".exportSpec.theoremPlan }"
  , ""
  , "/-- Official-stereo request extracted from the generated prepared transaction. -/"
  , "def " ++ request.requestName ++ " : TetraStereo.Engine.OfficialStereoRequest :="
  , "  match " ++ request.blueprintName ++ ".toOfficialStereoRequest with"
  , "  | Except.ok request => request"
  , "  | Except.error _ => " ++ request.requestFallbackName
  , ""
  , request.target.documentation
  , "theorem " ++ request.targetClaimTheoremName ++ " :"
  , "    " ++ request.target.statement request.requestName ++ " :="
  , request.target.proofTerm
  , ""
  , "/-- The compact host query really builds a prepared transaction. -/"
  , "theorem " ++ request.hostQueryBuildsName ++ " :"
  , "    TetraStereo.Engine.OfficialStereoHostQueryBuilds " ++ request.queryName ++ " := by"
  , "  unfold TetraStereo.Engine.OfficialStereoHostQueryBuilds"
  , "  change (match " ++ request.preparedResultName ++ " with"
  , "    | Except.ok _ => True"
  , "    | Except.error _ => False)"
  , "  cases h : " ++ request.preparedResultName ++ " with"
  , "  | ok prepared =>"
  , "      trivial"
  , "  | error failure =>"
  , "      have hbool := " ++ request.preparedResultBuildsName
  , "      rw [h] at hbool"
  , "      simp at hbool"
  , ""
  , "/-- Source-only generated host-query module spec. -/"
  , "def " ++ request.sourceSpecName ++ " : TetraStereo.Engine.OfficialStereoHostQuerySourceSpec :="
  , "  " ++ request.queryName ++ ".hostQuerySourceSpec"
  , "    " ++ leanStringLit queryFull
  , "    " ++ leanStringLit buildFull
  , "    " ++ leanStringLit request.certificateTheoremName
  , ""
  , "/-- Source-registry entry generated directly from the compact host query. -/"
  , "def " ++ request.sourceEntryName ++ " : TetraStereo.Engine.CertificateSourceEntry :="
  , "  " ++ request.queryName ++ ".hostQuerySourceEntry"
  , "    " ++ leanStringLit queryFull
  , "    " ++ leanStringLit buildFull
  , "    " ++ leanStringLit request.certificateTheoremName
  , ""
  , "/-- The generated source-registry entry uses the host-facing key. -/"
  , "theorem " ++ request.sourceEntryKeyTheoremName ++ " :"
  , "    " ++ request.sourceEntryName ++ ".key = " ++ leanStringLit request.key ++ " :="
  , "  rfl"
  , ""
  , "/-- The generated host query built a checked prepared transaction. -/"
  , "theorem " ++ request.hostQueryClaimTheoremName ++ " :"
  , "    TetraStereo.Engine.OfficialStereoHostQueryClaim " ++ request.queryName ++ " :="
  , "  TetraStereo.Engine.officialStereoHostQueryClaim_checked " ++ request.queryName ++ " " ++
      request.hostQueryBuildsName
  ]

/-- Render all declarations for this generated host module. -/
def declarationLines (request : HostOfficialStereoRequest) : List String :=
  request.ownerMetadataDeclarations ++ [""] ++
    request.rawDeclaration ++ [""] ++
    request.packetDeclaration ++ [""] ++
      request.intakeDeclarations ++ [""] ++
        request.queryDeclarations ++ [""] ++
          request.certificateDeclarations

/-- Render import lines for this generated host module. -/
def importLines (request : HostOfficialStereoRequest) : List String :=
  request.moduleImports.map fun moduleName => "import " ++ moduleName

/-- Render namespace-open lines for this generated host module. -/
def namespaceOpenLines (request : HostOfficialStereoRequest) : List String :=
  request.namespacePath.map fun namespaceName => "namespace " ++ namespaceName

/-- Render namespace-close lines for this generated host module. -/
def namespaceCloseLines (request : HostOfficialStereoRequest) : List String :=
  request.namespacePath.reverse.map fun namespaceName => "end " ++ namespaceName

/-- Render the complete standalone Lean source for this host request module. -/
def moduleSource (request : HostOfficialStereoRequest) : String :=
  OneCenter.joinLines
    (request.importLines ++ [""] ++ request.options ++ [""] ++
      request.namespaceOpenLines ++ [""] ++ ["open TetraStereo.OneCenter", ""] ++
        ["noncomputable section", ""] ++ request.declarationLines ++ [""] ++
          ["end", ""] ++ request.namespaceCloseLines)

/-- Source-entry view of the generated host module itself. -/
def moduleSourceEntry (request : HostOfficialStereoRequest) : CertificateSourceEntry where
  key := request.key ++ "::host-module"
  description := "generated host Lean module for " ++ request.description
  fileName := request.moduleFileName
  source := request.moduleSource

/-- Source-only spec for the downstream certificate theorem importing this generated host module. -/
def certificateSourceSpec (request : HostOfficialStereoRequest) :
    OfficialStereoHostQuerySourceSpec :=
  { key := request.key
    description := "checked " ++ request.description
    fileName := request.certificateFileName
    imports := [request.moduleName]
    namespacePath := request.certificateNamespacePath
    theoremName := request.certificateTheoremName
    queryExpr := request.fullName request.queryName
    buildProofExpr := request.fullName request.hostQueryBuildsName }

/-- Source-entry view of the downstream generated certificate theorem. -/
def certificateSourceEntry (request : HostOfficialStereoRequest) : CertificateSourceEntry :=
  request.certificateSourceSpec.sourceEntry

/-- File paths written for a two-stage generated host certificate package. -/
structure PackagePaths where
  hostModulePath : System.FilePath
  hostModuleOLeanPath : System.FilePath
  certificatePath : System.FilePath

/-- Write the generated host module and downstream certificate source to import-correct paths. -/
def writePackageSources (request : HostOfficialStereoRequest) (packageRoot : String) :
    IO PackagePaths := do
  match request.validateGeneratedShape with
  | Except.ok () => pure ()
  | Except.error message => throw (IO.userError message)
  let hostModulePath := request.packageHostModulePath packageRoot
  let hostModuleOLeanPath := request.packageHostModuleOLeanPath packageRoot
  let certificatePath := request.packageCertificatePath packageRoot
  let _ ← writeLeanSourceFile hostModulePath request.moduleSource
  let _ ← writeLeanSourceFile certificatePath request.certificateSourceEntry.source
  pure { hostModulePath := hostModulePath
         hostModuleOLeanPath := hostModuleOLeanPath
         certificatePath := certificatePath }

end HostOfficialStereoRequest

end
end Engine
end TetraStereo
