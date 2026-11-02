import TetraStereo.OneCenter.LocalizedRule3DescriptorBearingReference
import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3Key

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Endpoint priority from the first constitutional sphere

P-92.1.3 orders Rule 1a before Rule 1b and Rule 2; P-92.1.6 applies the same ordered rules at
every ranked digraph node and records the first decisive difference.  The complete endpoint
selector `localizedRule3EndpointPriority` therefore cannot be decided by a later Rule-3 geometry
observation whenever the two ligand roots already differ in atomic number: the earlier decision
persists, and there is no suppression rule that would allow a deeper sphere or a later rule to
override it.

This module makes that first-sphere short-circuit precise and executable.  The descriptor-bearing
reroot key compiler always retains its cursor's atomic-number observation as the addressed root of
Rule 1a, so a strict root difference selects the corresponding endpoint reference at every fuel,
excluded-unit list, and cursor.  A separate plain root-observation comparator on two actual cursors
records the same three-way outcome; equality is `defer`, never `nonstereogenic`, because the two
roots may still differ in later spheres or Rules 3--5.
-/

/-- Three-way first-sphere root outcome.  `defer` is the equal-root case and carries no
stereochemical assertion: only the complete Rules-1a--5 comparison may decide the endpoint. -/
inductive LocalizedRerootCursorConstitutionalRootOutcome where
  | firstSenior
  | secondSenior
  | defer
  deriving DecidableEq, Repr

namespace CertifiedLocalizedCIPInput

/-- The first-sphere root observation of a localized reroot cursor: the atomic number of the node
at the cursor's own coordinate.  This is exactly the Rule-1a head of every constitutional key
rooted at the cursor. -/
def localizedRerootCursorRootAtomicNumber
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) : Nat :=
  (ofLex (input.moleculeGraph.officialNodeAtomLabel cursor.occurrence.1.node)).1

/-- Plain root-observation comparator on two actual localized reroot cursors.  This inspects only
the first sphere of Rule 1a: a strict atomic-number difference decides, equality defers. -/
def compareLocalizedRerootCursorConstitutionalRoot
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedRerootCursor carrierFuel) : Ordering :=
  compare (input.localizedRerootCursorRootAtomicNumber first)
    (input.localizedRerootCursorRootAtomicNumber second)

/-- The three-way first-sphere outcome of two actual cursors. -/
def localizedRerootCursorConstitutionalRootOutcomeOf
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedRerootCursor carrierFuel) :
    LocalizedRerootCursorConstitutionalRootOutcome :=
  match input.compareLocalizedRerootCursorConstitutionalRoot first second with
  | Ordering.gt => .firstSenior
  | Ordering.lt => .secondSenior
  | Ordering.eq => .defer

/-- A strictly higher first root selects the first cursor. -/
theorem localizedRerootCursorConstitutionalRootOutcomeOf_eq_firstSenior_of_gt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedRerootCursor carrierFuel)
    (higher : input.localizedRerootCursorRootAtomicNumber second <
      input.localizedRerootCursorRootAtomicNumber first) :
    input.localizedRerootCursorConstitutionalRootOutcomeOf first second = .firstSenior := by
  have compared : compare (input.localizedRerootCursorRootAtomicNumber first)
      (input.localizedRerootCursorRootAtomicNumber second) = Ordering.gt :=
    compare_gt_iff_gt.mpr higher
  simp [localizedRerootCursorConstitutionalRootOutcomeOf,
    compareLocalizedRerootCursorConstitutionalRoot, compared]

/-- A strictly lower first root selects the second cursor. -/
theorem localizedRerootCursorConstitutionalRootOutcomeOf_eq_secondSenior_of_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedRerootCursor carrierFuel)
    (lower : input.localizedRerootCursorRootAtomicNumber first <
      input.localizedRerootCursorRootAtomicNumber second) :
    input.localizedRerootCursorConstitutionalRootOutcomeOf first second = .secondSenior := by
  have compared : compare (input.localizedRerootCursorRootAtomicNumber first)
      (input.localizedRerootCursorRootAtomicNumber second) = Ordering.lt :=
    compare_lt_iff_lt.mpr lower
  simp [localizedRerootCursorConstitutionalRootOutcomeOf,
    compareLocalizedRerootCursorConstitutionalRoot, compared]

/-- Equal first-sphere roots defer to the complete comparison; they are never classified as
nonstereogenic by the root observation alone. -/
theorem localizedRerootCursorConstitutionalRootOutcomeOf_eq_defer_of_root_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedRerootCursor carrierFuel)
    (tied : input.localizedRerootCursorRootAtomicNumber first =
      input.localizedRerootCursorRootAtomicNumber second) :
    input.localizedRerootCursorConstitutionalRootOutcomeOf first second = .defer := by
  simp [localizedRerootCursorConstitutionalRootOutcomeOf,
    compareLocalizedRerootCursorConstitutionalRoot, tied]

/-- Every successful descriptor-bearing reroot key retains its cursor's atomic-number observation
as the singleton first sphere and first parent address of Rule 1a.  Both the terminal and the
assembled outer cases place the cursor's real-root key at the head; no recursive child derivation
is needed. -/
theorem buildLocalizedRerootDescriptorBearingRule3Key?_constitutional_rule1a_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
      (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootRecursiveRule3SpatialKey),
      input.buildLocalizedRerootDescriptorBearingRule3Key?
          target view fuel excluded cursor = some key →
        key.constitutional.rule1a.head? =
          some [([], (ofLex (input.moleculeGraph.officialNodeAtomLabel
            cursor.occurrence.1.node)).1)]
  | 0, excluded, cursor, key, computed => by
      unfold buildLocalizedRerootDescriptorBearingRule3Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed :
              input.localizedDescriptorBearingRule3StructuralNode?
                cursor.occurrence with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                simp
              · simp [childrenComputed, observationComputed, terminal] at computed
  | fuel + 1, excluded, cursor, key, computed => by
      unfold buildLocalizedRerootDescriptorBearingRule3Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed : input.localizedDescriptorBearingRule3NodeWith?
              target cursor.occurrence view
              (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
              excluded with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                simp
              · cases childKeysComputed : children.mapM
                    (input.buildLocalizedRerootDescriptorBearingRule3Key?
                      target view fuel excluded) with
                | none =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                | some childKeys =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                    subst key
                    simp [OfficialRuleMajorKey.assemble]

/-- The same head fact in terms of the plain cursor root observation. -/
theorem buildLocalizedRerootDescriptorBearingRule3Key?_constitutional_rule1a_head_observation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : input.buildLocalizedRerootDescriptorBearingRule3Key?
      target view fuel excluded cursor = some key) :
    key.constitutional.rule1a.head? =
      some [([], input.localizedRerootCursorRootAtomicNumber cursor)] := by
  unfold localizedRerootCursorRootAtomicNumber
  exact input.buildLocalizedRerootDescriptorBearingRule3Key?_constitutional_rule1a_head
    target view fuel excluded cursor key computed

/-- The symmetric strict constitutional case: a smaller retained real-root key selects the second
endpoint reference. -/
theorem localizedRule3EndpointPriority_of_constitutional_lt
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame)
    (strict : OfficialRuleMajorKey.compare
      frame.firstKey.rule3.constitutional
      frame.secondKey.rule3.constitutional = Ordering.lt) :
    input.localizedRule3EndpointPriority frame = .senior frame.second := by
  have rule3Strict : input.compareLocalizedRerootRecursiveRule3SpatialKeys
      frame.firstKey.rule3 frame.secondKey.rule3 = Ordering.lt := by
    simp [compareLocalizedRerootRecursiveRule3SpatialKeys, compareLex,
      Ordering.byKey, strict]
  simp [localizedRule3EndpointPriority,
    compareLocalizedOccurrenceRule3Through5Keys, compareLex, Ordering.byKey,
    rule3Strict]

/-- A strictly higher real root atomic number decides the endpoint before Rule 1b, Rule 2, or any
recursive Rule-3 geometry is inspected. -/
theorem localizedRule3EndpointPriority_of_rule1a_head_gt
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame)
    {firstZ secondZ : Nat}
    (firstHead : frame.firstKey.rule3.constitutional.rule1a.head? =
      some [([], firstZ)])
    (secondHead : frame.secondKey.rule3.constitutional.rule1a.head? =
      some [([], secondZ)])
    (higher : secondZ < firstZ) :
    input.localizedRule3EndpointPriority frame = .senior frame.first := by
  have rule1aStrict : OfficialRuleMajorKey.compareSparseLayers
      OfficialRuleMajorKey.compareNat
      frame.firstKey.rule3.constitutional.rule1a
      frame.secondKey.rule3.constitutional.rule1a = Ordering.gt :=
    MoleculeGraph.officialRuleMajorKey_compare_rule1a_gt_of_heads_gt
      firstHead secondHead higher
  have constitutionalStrict : OfficialRuleMajorKey.compare
      frame.firstKey.rule3.constitutional
      frame.secondKey.rule3.constitutional = Ordering.gt := by
    simp [OfficialRuleMajorKey.compare, compareLex, Ordering.byKey, rule1aStrict]
  exact input.localizedRule3EndpointPriority_of_constitutional_gt frame constitutionalStrict

/-- The symmetric strict case: a lower first root atomic number selects the second endpoint
reference before any later sphere or rule is inspected. -/
theorem localizedRule3EndpointPriority_of_rule1a_head_lt
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame)
    {firstZ secondZ : Nat}
    (firstHead : frame.firstKey.rule3.constitutional.rule1a.head? =
      some [([], firstZ)])
    (secondHead : frame.secondKey.rule3.constitutional.rule1a.head? =
      some [([], secondZ)])
    (lower : firstZ < secondZ) :
    input.localizedRule3EndpointPriority frame = .senior frame.second := by
  have rule1aStrict : OfficialRuleMajorKey.compareSparseLayers
      OfficialRuleMajorKey.compareNat
      frame.firstKey.rule3.constitutional.rule1a
      frame.secondKey.rule3.constitutional.rule1a = Ordering.lt :=
    MoleculeGraph.officialRuleMajorKey_compare_rule1a_lt_of_heads_lt
      firstHead secondHead lower
  have constitutionalStrict : OfficialRuleMajorKey.compare
      frame.firstKey.rule3.constitutional
      frame.secondKey.rule3.constitutional = Ordering.lt := by
    simp [OfficialRuleMajorKey.compare, compareLex, Ordering.byKey, rule1aStrict]
  exact input.localizedRule3EndpointPriority_of_constitutional_lt frame constitutionalStrict

namespace LocalizedRule3EndpointKeyFrame

/-- A full endpoint key frame is a first-sphere exact pair of two actual cursors when its two
cumulative keys carry exactly the root atomic-number observations of those cursors.  This is the
exactness premise under which the first-sphere short-circuit is sound; it does not commit to any
particular recursive key builder. -/
def FirstSphereRootExact
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (frame : input.LocalizedRule3EndpointKeyFrame)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  frame.firstKey.rule3.constitutional.rule1a.head? =
      some [([], input.localizedRerootCursorRootAtomicNumber firstCursor)] ∧
    frame.secondKey.rule3.constitutional.rule1a.head? =
      some [([], input.localizedRerootCursorRootAtomicNumber secondCursor)]

/-- Descriptor-bearing reroot keys discharge the first-sphere exact-pair premise.  This is the only
place the fresh descriptor-bearing builder is consulted; its keys are not claimed to equal any
occurrence-path key. -/
theorem FirstSphereRootExact_of_descriptorBearing
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedRule3EndpointKeyFrame)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (firstRule3 secondRule3 : input.LocalizedRerootRecursiveRule3SpatialKey)
    (firstKeyEq : frame.firstKey.rule3 = firstRule3)
    (secondKeyEq : frame.secondKey.rule3 = secondRule3)
    (firstComputed : input.buildLocalizedRerootDescriptorBearingRule3Key?
      target view fuel excluded firstCursor = some firstRule3)
    (secondComputed : input.buildLocalizedRerootDescriptorBearingRule3Key?
      target view fuel excluded secondCursor = some secondRule3) :
    FirstSphereRootExact frame firstCursor secondCursor := by
  constructor
  · rw [firstKeyEq]
    exact input.buildLocalizedRerootDescriptorBearingRule3Key?_constitutional_rule1a_head_observation
      target view fuel excluded firstCursor firstRule3 firstComputed
  · rw [secondKeyEq]
    exact input.buildLocalizedRerootDescriptorBearingRule3Key?_constitutional_rule1a_head_observation
      target view fuel excluded secondCursor secondRule3 secondComputed

end LocalizedRule3EndpointKeyFrame

/-- First-sphere strictness selects the senior endpoint reference exactly as the complete
comparator would: a higher first root selects the first reference. -/
theorem localizedRule3EndpointPriority_of_cursor_root_gt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedRule3EndpointKeyFrame)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (exactPair : LocalizedRule3EndpointKeyFrame.FirstSphereRootExact
      frame firstCursor secondCursor)
    (higher : input.localizedRerootCursorRootAtomicNumber secondCursor <
      input.localizedRerootCursorRootAtomicNumber firstCursor) :
    input.localizedRule3EndpointPriority frame = .senior frame.first := by
  rcases exactPair with ⟨firstHead, secondHead⟩
  exact input.localizedRule3EndpointPriority_of_rule1a_head_gt frame
    firstHead secondHead higher

/-- The symmetric strict case: a lower first root selects the second endpoint reference. -/
theorem localizedRule3EndpointPriority_of_cursor_root_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedRule3EndpointKeyFrame)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (exactPair : LocalizedRule3EndpointKeyFrame.FirstSphereRootExact
      frame firstCursor secondCursor)
    (lower : input.localizedRerootCursorRootAtomicNumber firstCursor <
      input.localizedRerootCursorRootAtomicNumber secondCursor) :
    input.localizedRule3EndpointPriority frame = .senior frame.second := by
  rcases exactPair with ⟨firstHead, secondHead⟩
  exact input.localizedRule3EndpointPriority_of_rule1a_head_lt frame
    firstHead secondHead lower

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
