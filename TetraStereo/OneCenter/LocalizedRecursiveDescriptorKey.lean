import TetraStereo.OneCenter.LocalizedDescriptorHierarchy

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Recursively re-ranked localized descriptor keys

An addressed flat projection is not by itself sufficient for branching ligands: children tied by
Rules 1a--2 must be re-ranked under the selected descriptor rule before their descendants receive
parent-slot addresses.  This module compiles a unary key recursively.  Every child subtree is
first compiled independently, then sorted by its complete constitutional key followed by the
selected descriptor projection, and only then merged beneath its parent slot.

The construction is also valid for cyclic ligands because nodes are provenance-bearing
`OfficialCIPNode`s; ring and multiple-bond duplicates are terminal occurrences rather than graph
vertices revisited without context.
-/

/-- Uppercase-seed descriptor stage used while compiling one unary branch key. -/
inductive LocalizedConstitutionalDescriptorStage where
  | rule4a
  | rule4b (reference : RS)
  | rule5 (reference : RS)
  deriving DecidableEq, Repr

namespace CertifiedLocalizedCIPInput

/-- Numeric observation at one provenance occurrence for the selected descriptor stage. -/
def localizedConstitutionalDescriptorPriority
    (input : CertifiedLocalizedCIPInput)
    (stage : LocalizedConstitutionalDescriptorStage)
    (source : Option input.ConstitutionalSeedSource) : ℕ :=
  match stage, source with
  | _, none => 0
  | .rule4a, some _ => 2
  | .rule4b reference, some source
  | .rule5 reference, some source => if source.2 == reference then 1 else 0

/-- A recursively canonical unary key: the constitutional component ranks children before the
descriptor component is allowed to refine a constitutional tie. -/
structure LocalizedRecursiveDescriptorKey (input : CertifiedLocalizedCIPInput) where
  constitutional : OfficialRuleMajorKey input.Atom
  descriptor : List (List (OfficialSparseEntry ℕ))

/-- Normative comparison of recursively compiled unary keys. -/
def compareLocalizedRecursiveDescriptorKeys (input : CertifiedLocalizedCIPInput) :
    input.LocalizedRecursiveDescriptorKey →
      input.LocalizedRecursiveDescriptorKey → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.constitutional) OfficialRuleMajorKey.compare)
    (Ordering.byKey (fun key => key.descriptor)
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))

/-- The complete constitutional-then-descriptor unary comparator is oriented and transitive. -/
theorem compareLocalizedRecursiveDescriptorKeys_transCmp
    (input : CertifiedLocalizedCIPInput) :
    Std.TransCmp input.compareLocalizedRecursiveDescriptorKeys := by
  letI : Std.TransCmp (@OfficialRuleMajorKey.compare input.Atom) :=
    OfficialRuleMajorKey.compare_transCmp
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  unfold compareLocalizedRecursiveDescriptorKeys
    OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer
    OfficialRuleMajorKey.compareSparseEntry
  infer_instance

/-- Structural descending insertion.  Descriptor-key construction never delegates its chemical
ordering to a platform sort implementation. -/
def insertLocalizedRecursiveDescriptorKey (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRecursiveDescriptorKey) :
    List input.LocalizedRecursiveDescriptorKey →
      List input.LocalizedRecursiveDescriptorKey
  | [] => [key]
  | head :: tail =>
      match input.compareLocalizedRecursiveDescriptorKeys key head with
      | Ordering.lt => head :: input.insertLocalizedRecursiveDescriptorKey key tail
      | Ordering.eq | Ordering.gt => key :: head :: tail

/-- Structural descending sort used independently at every parent occurrence. -/
def sortLocalizedRecursiveDescriptorKeys (input : CertifiedLocalizedCIPInput) :
    List input.LocalizedRecursiveDescriptorKey →
      List input.LocalizedRecursiveDescriptorKey
  | [] => []
  | key :: keys =>
      input.insertLocalizedRecursiveDescriptorKey key
        (input.sortLocalizedRecursiveDescriptorKeys keys)

theorem insertLocalizedRecursiveDescriptorKey_perm
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRecursiveDescriptorKey) :
    ∀ keys,
      (input.insertLocalizedRecursiveDescriptorKey key keys).Perm (key :: keys)
  | [] => List.Perm.refl _
  | head :: tail => by
      unfold insertLocalizedRecursiveDescriptorKey
      cases comparison : input.compareLocalizedRecursiveDescriptorKeys key head with
      | eq => exact List.Perm.refl _
      | gt => exact List.Perm.refl _
      | lt =>
          exact (List.Perm.cons head
            (input.insertLocalizedRecursiveDescriptorKey_perm key tail)).trans
              (List.Perm.swap key head tail)

theorem sortLocalizedRecursiveDescriptorKeys_perm
    (input : CertifiedLocalizedCIPInput) :
    ∀ keys,
      (input.sortLocalizedRecursiveDescriptorKeys keys).Perm keys
  | [] => List.Perm.refl []
  | key :: keys =>
      (input.insertLocalizedRecursiveDescriptorKey_perm key
        (input.sortLocalizedRecursiveDescriptorKeys keys)).trans
          (List.Perm.cons key (input.sortLocalizedRecursiveDescriptorKeys_perm keys))

/-- Descending recursive sibling priority. -/
def LocalizedRecursiveDescriptorKeysDescending (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRecursiveDescriptorKey) : Prop :=
  keys.Pairwise fun left right =>
    input.compareLocalizedRecursiveDescriptorKeys left right ≠ Ordering.lt

theorem insertLocalizedRecursiveDescriptorKey_descending
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRecursiveDescriptorKey) :
    ∀ keys,
      input.LocalizedRecursiveDescriptorKeysDescending keys →
      input.LocalizedRecursiveDescriptorKeysDescending
        (input.insertLocalizedRecursiveDescriptorKey key keys)
  | [], _ => by
      simp [insertLocalizedRecursiveDescriptorKey,
        LocalizedRecursiveDescriptorKeysDescending]
  | head :: tail, sorted => by
      letI : Std.TransCmp input.compareLocalizedRecursiveDescriptorKeys :=
        input.compareLocalizedRecursiveDescriptorKeys_transCmp
      have headOverTail : ∀ observed ∈ tail,
          input.compareLocalizedRecursiveDescriptorKeys head observed ≠ Ordering.lt :=
        (List.pairwise_cons.mp sorted).1
      have tailSorted : input.LocalizedRecursiveDescriptorKeysDescending tail :=
        (List.pairwise_cons.mp sorted).2
      unfold insertLocalizedRecursiveDescriptorKey
      cases comparison : input.compareLocalizedRecursiveDescriptorKeys key head with
      | gt =>
          rw [LocalizedRecursiveDescriptorKeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | eq =>
          rw [LocalizedRecursiveDescriptorKeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | lt =>
          have insertedSorted :=
            input.insertLocalizedRecursiveDescriptorKey_descending key tail tailSorted
          rw [LocalizedRecursiveDescriptorKeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            have permutation :=
              input.insertLocalizedRecursiveDescriptorKey_perm key tail
            have sourcePresent : observed ∈ key :: tail :=
              (permutation.mem_iff).mp present
            rcases List.mem_cons.mp sourcePresent with same | tailPresent
            · subst observed
              have reverse :
                  input.compareLocalizedRecursiveDescriptorKeys head key = Ordering.gt := by
                rw [Std.OrientedCmp.gt_iff_lt]
                exact comparison
              exact by simp [reverse]
            · exact headOverTail observed tailPresent
          · exact insertedSorted

theorem sortLocalizedRecursiveDescriptorKeys_descending
    (input : CertifiedLocalizedCIPInput) :
    ∀ keys,
      input.LocalizedRecursiveDescriptorKeysDescending
        (input.sortLocalizedRecursiveDescriptorKeys keys)
  | [] => by simp [sortLocalizedRecursiveDescriptorKeys,
      LocalizedRecursiveDescriptorKeysDescending]
  | key :: keys =>
      input.insertLocalizedRecursiveDescriptorKey_descending key
        (input.sortLocalizedRecursiveDescriptorKeys keys)
        (input.sortLocalizedRecursiveDescriptorKeys_descending keys)

/-- Maximum descriptor sphere count among already compiled child keys. -/
def localizedDescriptorChildLayerCount (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRecursiveDescriptorKey) : ℕ :=
  children.foldl (fun longest child => max longest child.descriptor.length) 0

/-- Merge recursively ranked child descriptor spheres beneath their final sibling slots. -/
def mergeLocalizedDescriptorChildren (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRecursiveDescriptorKey) :
    List (List (OfficialSparseEntry ℕ)) :=
  let count := input.localizedDescriptorChildLayerCount children
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2
        (child.1.descriptor.getD depth [])

/-- Compile a complete recursively re-ranked descriptor key.  At zero remaining depth the node
must be terminal; this prevents a truncated descriptor hierarchy from being treated as complete. -/
def buildLocalizedRecursiveDescriptorKey?
    (input : CertifiedLocalizedCIPInput)
    (stage : LocalizedConstitutionalDescriptorStage) :
    ℕ → OfficialCIPNode input.Atom →
      Option input.LocalizedRecursiveDescriptorKey
  | 0, node => do
      if !((input.executableOfficialCIPChildren node).isEmpty) then none else
        let constitutional ← input.buildExecutableOfficialRuleMajorKey 0 node
        let observation ←
          input.observeAddressedConstitutionalSeed? ([], node)
        some
          { constitutional := constitutional
            descriptor := [[([],
              input.localizedConstitutionalDescriptorPriority stage observation.2)]] }
  | fuel + 1, node => do
      let constitutional ←
        input.buildExecutableOfficialRuleMajorKey (fuel + 1) node
      let observation ←
        input.observeAddressedConstitutionalSeed? ([], node)
      let childKeys ← (input.executableOfficialCIPChildren node).mapM
        (input.buildLocalizedRecursiveDescriptorKey? stage fuel)
      let sorted := input.sortLocalizedRecursiveDescriptorKeys childKeys
      some
        { constitutional := constitutional
          descriptor :=
            [[([], input.localizedConstitutionalDescriptorPriority stage observation.2)]] ++
              input.mergeLocalizedDescriptorChildren sorted }

/- Independent recursive derivation for a successful stage-key compilation.  It records the
fresh constitutional expansion, declarative node observation, a derivation for every enumerated
child, and the fact that recursive child ranking is a permutation before addressed merging. -/
mutual
  inductive DeclarativeLocalizedRecursiveDescriptorKey
      (input : CertifiedLocalizedCIPInput)
      (stage : LocalizedConstitutionalDescriptorStage) :
      ℕ → OfficialCIPNode input.Atom →
        input.LocalizedRecursiveDescriptorKey → Prop
    | leaf {node constitutional observation}
        (terminal : input.executableOfficialCIPChildren node = [])
        (constitution : OfficialRuleMajorKey.DeclarativeAddressedExpansion
          input.moleculeGraph input.executableOfficialCIPChildren
          0 node constitutional.sourceNodes)
        (observed : input.DeclarativeAddressedConstitutionalSeedObservation
          ([], node) observation) :
        DeclarativeLocalizedRecursiveDescriptorKey input stage 0 node
          { constitutional := constitutional
            descriptor := [[([],
              input.localizedConstitutionalDescriptorPriority stage observation.2)]] }
    | branch {fuel node constitutional observation childKeys sorted}
        (constitution : OfficialRuleMajorKey.DeclarativeAddressedExpansion
          input.moleculeGraph input.executableOfficialCIPChildren
          (fuel + 1) node constitutional.sourceNodes)
        (observed : input.DeclarativeAddressedConstitutionalSeedObservation
          ([], node) observation)
        (children : DeclarativeLocalizedRecursiveDescriptorKeyList input stage fuel
          (input.executableOfficialCIPChildren node) childKeys)
        (ranking : sorted.Perm childKeys)
        (descending : input.LocalizedRecursiveDescriptorKeysDescending sorted) :
        DeclarativeLocalizedRecursiveDescriptorKey input stage (fuel + 1) node
          { constitutional := constitutional
            descriptor :=
              [[([], input.localizedConstitutionalDescriptorPriority stage observation.2)]] ++
                input.mergeLocalizedDescriptorChildren sorted }

  /-- Pointwise recursive derivations for every enumerated child without nesting the recursive
  key relation inside a library inductive. -/
  inductive DeclarativeLocalizedRecursiveDescriptorKeyList
      (input : CertifiedLocalizedCIPInput)
      (stage : LocalizedConstitutionalDescriptorStage) :
      ℕ → List (OfficialCIPNode input.Atom) →
        List input.LocalizedRecursiveDescriptorKey → Prop
    | nil (fuel : ℕ) :
        DeclarativeLocalizedRecursiveDescriptorKeyList input stage fuel [] []
    | cons {fuel node nodes key keys}
        (head : DeclarativeLocalizedRecursiveDescriptorKey input stage fuel node key)
        (tail : DeclarativeLocalizedRecursiveDescriptorKeyList input stage fuel nodes keys) :
        DeclarativeLocalizedRecursiveDescriptorKeyList input stage fuel
          (node :: nodes) (key :: keys)
end

/-- Arbitrary-root executable constitutional compilation satisfies the independent addressed
expansion semantics. -/
theorem buildExecutableOfficialRuleMajorKey_declarative
    (input : CertifiedLocalizedCIPInput) (fuel : ℕ)
    (node : OfficialCIPNode input.Atom) (key : OfficialRuleMajorKey input.Atom)
    (computed : input.buildExecutableOfficialRuleMajorKey fuel node = some key) :
    OfficialRuleMajorKey.DeclarativeAddressedExpansion
      input.moleculeGraph input.executableOfficialCIPChildren fuel node key.sourceNodes := by
  unfold buildExecutableOfficialRuleMajorKey at computed
  exact input.moleculeGraph.buildOfficialRuleMajorKey_declarativeAddressedExpansion
    input.executableOfficialCIPChildren fuel node key computed

/-- `mapM` of the recursive compiler retains one declarative derivation for every child. -/
private theorem mapM_buildLocalizedRecursiveDescriptorKey?_sound
    (input : CertifiedLocalizedCIPInput)
    (stage : LocalizedConstitutionalDescriptorStage) (fuel : ℕ)
    (sound : ∀ node key,
      input.buildLocalizedRecursiveDescriptorKey? stage fuel node = some key →
      input.DeclarativeLocalizedRecursiveDescriptorKey stage fuel node key) :
    ∀ nodes keys,
      nodes.mapM (input.buildLocalizedRecursiveDescriptorKey? stage fuel) = some keys →
      DeclarativeLocalizedRecursiveDescriptorKeyList input stage fuel nodes keys
  | [], keys, computed => by
      simp at computed
      subst keys
      exact DeclarativeLocalizedRecursiveDescriptorKeyList.nil fuel
  | node :: nodes, keys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildLocalizedRecursiveDescriptorKey? stage fuel node with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed :
              nodes.mapM (input.buildLocalizedRecursiveDescriptorKey? stage fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact DeclarativeLocalizedRecursiveDescriptorKeyList.cons
                (sound node head headComputed)
                (mapM_buildLocalizedRecursiveDescriptorKey?_sound
                  input stage fuel sound nodes tail tailComputed)

/-- Every successful recursive stage-key compilation has a kernel-checked derivation covering
every provenance child; fuel exhaustion and unresolved descriptor sources are fail-closed. -/
theorem buildLocalizedRecursiveDescriptorKey?_sound
    (input : CertifiedLocalizedCIPInput)
    (stage : LocalizedConstitutionalDescriptorStage) :
    ∀ fuel node key,
      input.buildLocalizedRecursiveDescriptorKey? stage fuel node = some key →
      input.DeclarativeLocalizedRecursiveDescriptorKey stage fuel node key
  | 0, node, key, computed => by
      unfold buildLocalizedRecursiveDescriptorKey? at computed
      by_cases terminal : input.executableOfficialCIPChildren node = []
      · simp [terminal] at computed
        cases constitutionalComputed :
            input.buildExecutableOfficialRuleMajorKey 0 node with
        | none => simp [constitutionalComputed] at computed
        | some constitutional =>
            cases observationComputed :
                input.observeAddressedConstitutionalSeed? ([], node) with
            | none => simp [constitutionalComputed, observationComputed] at computed
            | some observation =>
                simp [constitutionalComputed, observationComputed] at computed
                subst key
                exact DeclarativeLocalizedRecursiveDescriptorKey.leaf terminal
                  (input.buildExecutableOfficialRuleMajorKey_declarative
                    0 node constitutional constitutionalComputed)
                  (input.observeAddressedConstitutionalSeed?_sound
                    ([], node) observation observationComputed)
      · simp [terminal] at computed
  | fuel + 1, node, key, computed => by
      unfold buildLocalizedRecursiveDescriptorKey? at computed
      cases constitutionalComputed :
          input.buildExecutableOfficialRuleMajorKey (fuel + 1) node with
      | none => simp [constitutionalComputed] at computed
      | some constitutional =>
          cases observationComputed :
              input.observeAddressedConstitutionalSeed? ([], node) with
          | none => simp [constitutionalComputed, observationComputed] at computed
          | some observation =>
              cases childrenComputed :
                  (input.executableOfficialCIPChildren node).mapM
                    (input.buildLocalizedRecursiveDescriptorKey? stage fuel) with
              | none =>
                  simp [constitutionalComputed, observationComputed,
                    childrenComputed] at computed
              | some childKeys =>
                  simp [constitutionalComputed, observationComputed,
                    childrenComputed] at computed
                  subst key
                  exact DeclarativeLocalizedRecursiveDescriptorKey.branch
                    (input.buildExecutableOfficialRuleMajorKey_declarative
                      (fuel + 1) node constitutional constitutionalComputed)
                    (input.observeAddressedConstitutionalSeed?_sound
                      ([], node) observation observationComputed)
                    (mapM_buildLocalizedRecursiveDescriptorKey?_sound
                      input stage fuel
                      (input.buildLocalizedRecursiveDescriptorKey?_sound stage fuel)
                      (input.executableOfficialCIPChildren node) childKeys childrenComputed)
                    (input.sortLocalizedRecursiveDescriptorKeys_perm childKeys)
                    (input.sortLocalizedRecursiveDescriptorKeys_descending childKeys)

/-- Compile a recursively re-ranked descriptor key for one localized ligand at the proved finite
molecular expansion bound. -/
def localizedRecursiveDescriptorKeyAt?
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (stage : LocalizedConstitutionalDescriptorStage) :
    Option input.LocalizedRecursiveDescriptorKey :=
  input.buildLocalizedRecursiveDescriptorKey? stage
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index))

/-- Every emitted localized recursive key covers the complete canonical ligand root through the
same proved finite bound. -/
theorem localizedRecursiveDescriptorKeyAt?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (stage : LocalizedConstitutionalDescriptorStage)
    (key : input.LocalizedRecursiveDescriptorKey)
    (computed : input.localizedRecursiveDescriptorKeyAt? center index stage = some key) :
    input.DeclarativeLocalizedRecursiveDescriptorKey stage
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index)) key := by
  exact input.buildLocalizedRecursiveDescriptorKey?_sound stage
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index)) key computed

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
