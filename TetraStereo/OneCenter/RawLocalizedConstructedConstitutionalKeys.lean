/-
  Constructed constitutional-key correspondence.

  This module connects the *actually constructed* raw canonical branch key

  `RawMolecule.buildCanonicalBranchKey mol cap fuel node`

  with the *actually constructed* localized official rule-major key

  `MoleculeGraph.buildOfficialRuleMajorKey m children fuel onode`

  at a child enumeration that is induced by the same raw canonical child copies.  The localized
  constructor is the existing one; the only new input is the child enumeration
  `localizedConstitutionalChildren`, which extends the official node by the canonical copies in
  canonical order.  This makes the two recursive child lists positionally aligned, so the
  correspondence is proved by an ordinary fuel induction rather than by assuming matching key
  columns or by assuming the desired comparator equality.

  The endpoint `ConstitutionalKeyCorresponds` is the existing structure from
  `LocalizedCanonicalRuntimeKeyCorrespondence`; the comparator equality is derived from it with the
  existing theorem `compareCanonicalBranchKeys_eq_officialRuleMajorKey_compare`.

  Domain conditions are explicit:

  * `CanonicalRule1aPlainDomain` records the mancude-free Rule-1a availability used by the existing
    correspondence bridge.  It is the only extra label hypothesis; it is not a key-column or
    comparator premise.
  * Reachability `ReachableCanonical mol root node` supplies the raw atom-index bound through
    `reachable_atom_lt`.
  * No oxido subtree hypothesis is needed by the correspondence itself because the localized child
    enumeration is derived from the canonical raw copies; the executable graph-order enumeration is
    *not* used here.  The exact relation of this canonical-order enumeration to the runtime
    executable enumeration is a permutation (`RawLocalizedChildNodeTransport.productionCIPChildren_
    forall₂_canonicalChildren`) and is deliberately not assumed to be an order equality.
-/

import TetraStereo.OneCenter.LocalizedCanonicalRuntimeKeyCorrespondence
import TetraStereo.OneCenter.RawLocalizedOxidoPathInvariant
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RawMolecule
open RawLocalizedChildNodeTransport
open RawLocalizedOxidoPathInvariant

/-! ## Rule-1a projection helpers -/

/-- Project one raw Rule-1a entry to the localized sparse vocabulary. -/
def rule1aEntryProjection (entry : RawMolecule.CanonicalAtomicEntry) :
    OfficialSparseEntry ℕ :=
  (entry.1, entry.2.numerator)

/-- Project one raw Rule-1a layer. -/
def rule1aLayerProjection (layer : List RawMolecule.CanonicalAtomicEntry) :
    List (OfficialSparseEntry ℕ) :=
  layer.map rule1aEntryProjection

/-- The projection of a list of layers is the list of projected layers. -/
theorem plainRule1aProjection_eq_map
    (layers : List (List RawMolecule.CanonicalAtomicEntry)) :
    plainRule1aProjection layers = layers.map rule1aLayerProjection :=
  rfl

/-- Layer-wise projection commutes with append. -/
theorem plainRule1aProjection_append
    (left right : List (List RawMolecule.CanonicalAtomicEntry)) :
    plainRule1aProjection (left ++ right) =
      plainRule1aProjection left ++ plainRule1aProjection right := by
  simp [plainRule1aProjection]

/-- Projection commutes with the sibling-slot prefix. -/
theorem rule1aLayerProjection_prefix (slot : ℕ)
    (layer : List RawMolecule.CanonicalAtomicEntry) :
    rule1aLayerProjection (RawMolecule.prefixCanonicalAtomicLayer slot layer) =
      OfficialRuleMajorKey.prefixLayer slot (rule1aLayerProjection layer) := by
  simp [rule1aLayerProjection, RawMolecule.prefixCanonicalAtomicLayer,
    OfficialRuleMajorKey.prefixLayer, rule1aEntryProjection, List.map_map]

/-- Mapping a `getD`-selected layer. -/
theorem map_getD_layer {α β : Type*} (f : α → β)
    (layers : List (List α)) (depth : ℕ) :
    (layers.getD depth []).map f =
      (layers.map (List.map f)).getD depth [] := by
  induction layers generalizing depth with
  | nil => rfl
  | cons layer layers ih =>
      cases depth with
      | zero => rfl
      | succ depth => simpa using ih depth

/-- Projection commutes with the layer-indexed `getD`. -/
theorem rule1aLayerProjection_getD
    (layers : List (List RawMolecule.CanonicalAtomicEntry)) (depth : ℕ) :
    rule1aLayerProjection (layers.getD depth []) =
      (layers.map rule1aLayerProjection).getD depth [] :=
  map_getD_layer rule1aEntryProjection layers depth

/-- A projectively corresponding pair of child keys has equal projected Rule-1a columns. -/
theorem rule1aProjection_eq_of_corresponds
    {V : Type*} {raw : RawMolecule.CanonicalBranchKey}
    {loc : OfficialRuleMajorKey V}
    (h : ConstitutionalKeyCorresponds raw loc) :
    raw.rule1a.map rule1aLayerProjection = loc.rule1a := by
  simpa [plainRule1aProjection_eq_map] using h.rule1a

/-! ## Generic list lemmas -/

/-- `Forall₂`-aligned `attach`/`map`: pointwise relation on all members induces the aligned
`Forall₂`. -/
theorem forall₂_attach_map_map_of_forall {α β γ : Type*} (R : β → γ → Prop)
    (l : List α) (f : {x // x ∈ l} → β) (g : α → γ)
    (h : ∀ x (hx : x ∈ l), R (f ⟨x, hx⟩) (g x)) :
    List.Forall₂ R (l.attach.map f) (l.map g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a as ih =>
      rw [List.attach_cons]
      simp only [List.map_cons, List.map_map]
      refine List.Forall₂.cons (h a (by simp)) ?_
      have htail := ih
        (fun x => f ⟨x.1, List.mem_cons_of_mem a x.2⟩) g
        (fun x hx => h x (List.mem_cons_of_mem a hx))
      simpa [Function.comp_def] using htail

/-- Two `Forall₂`-related lists have equal emptiness. -/
theorem isEmpty_eq_of_forall₂ {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) :
    xs.isEmpty = ys.isEmpty := by
  rw [Bool.eq_iff_iff, List.isEmpty_iff_length_eq_zero, List.isEmpty_iff_length_eq_zero,
    h.length_eq]

/-- Appending `Forall₂`-related lists. -/
theorem forall₂_append {α β : Type*} {R : α → β → Prop}
    {xs ys : List α} {us vs : List β}
    (h₁ : List.Forall₂ R xs us) (h₂ : List.Forall₂ R ys vs) :
    List.Forall₂ R (xs ++ ys) (us ++ vs) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hhead htail ih => simpa using List.Forall₂.cons hhead ih

/-- `zipIdx` transports pointwise along a `Forall₂`. -/
theorem forall₂_zipIdx {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) :
    ∀ start : ℕ,
      List.Forall₂ (fun a b => R a.1 b.1 ∧ a.2 = b.2)
        (xs.zipIdx start) (ys.zipIdx start) := by
  induction h with
  | nil => intro start; simp
  | cons hhead htail ih =>
      intro start
      simp [List.zipIdx_cons, hhead, ih (start + 1)]

/-- `flatMap` equality from pointwise equality on a `Forall₂`-aligned list. -/
theorem flatMap_eq_of_forall₂ {α β γ : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys)
    (f : α → List γ) (g : β → List γ)
    (hf : ∀ a b, R a b → f a = g b) :
    xs.flatMap f = ys.flatMap g := by
  induction h with
  | nil => rfl
  | cons hhead htail ih =>
      simp [List.flatMap_cons, hf _ _ hhead, ih]

/-- An entry of the layer selected by `getD` is an entry of the flattened layer list. -/
theorem mem_flatten_getD {α : Type*} {layers : List (List α)} {depth : ℕ} {e : α}
    (h : e ∈ layers.getD depth []) : e ∈ layers.flatten := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hlayer : layers[depth]? with
  | none => simp [hlayer] at h
  | some layer =>
      exact List.mem_flatten.mpr ⟨layer, List.mem_of_getElem? hlayer, by simpa [hlayer] using h⟩

/-! ## Correspondence of the root key -/

/-- Raw `atomZAt` reads the same parsed-atom atomic number as the raw parser-index lookup. -/
theorem atomZAt_eq_get (mol : RawMolecule) (idx : ℕ) (h : idx < mol.atomCount) :
    mol.atomZAt idx =
      (mol.atoms.get ⟨idx, by simpa [RawMolecule.atomCount] using h⟩).element.atomicNumber := by
  unfold RawMolecule.atomZAt RawMolecule.atomAt?
  rw [listGet?_eq_some_get mol.atoms ⟨idx, by simpa [RawMolecule.atomCount] using h⟩]

/-- Case analysis on provenance correspondence, exposed as an ordinary disjunction so that
dependent elimination is not performed on a projection. -/
theorem nodeProvenance_cases {provenanceO : OfficialCIPNodeProvenance}
    {provenanceC : RawMolecule.CanonicalNodeProvenance}
    (h : NodeProvenanceCorresponds provenanceO provenanceC) :
    (provenanceO = OfficialCIPNodeProvenance.realAtom ∧
      provenanceC = RawMolecule.CanonicalNodeProvenance.realAtom) ∨
    (∃ distance, provenanceO = OfficialCIPNodeProvenance.multipleBondDuplicate distance ∧
      provenanceC = RawMolecule.CanonicalNodeProvenance.multipleBondDuplicate distance) ∨
    (∃ distance, provenanceO = OfficialCIPNodeProvenance.ringDuplicate distance ∧
      provenanceC = RawMolecule.CanonicalNodeProvenance.ringDuplicate distance) := by
  cases h with
  | realAtom => exact Or.inl ⟨rfl, rfl⟩
  | multipleBondDuplicate distance => exact Or.inr (Or.inl ⟨distance, rfl, rfl⟩)
  | ringDuplicate distance => exact Or.inr (Or.inr ⟨distance, rfl, rfl⟩)

/-- The mancude-free Rule-1a label domain used by the constructed-key bridge. -/
def CanonicalRule1aPlainDomain (mol : RawMolecule)
    (node : RawMolecule.CanonicalBranchNode) : Prop :=
  mol.canonicalRule1aLabel? node =
    some { numerator := mol.atomZAt node.atom, denominator := 1 }

/-- The first component of the localized node label is the raw atomic number at the node atom. -/
theorem officialNodeAtomLabel_first_eq
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    {node : RawMolecule.CanonicalBranchNode}
    {onode : OfficialCIPNode input.Atom}
    (hcorr : NodeCorresponds (fun atom : input.Atom => atom.val) onode node)
    (atomBound : node.atom < mol.atomCount) :
    (ofLex (input.moleculeGraph.officialNodeAtomLabel onode)).1 = mol.atomZAt node.atom := by
  obtain ⟨atom, hcurrent⟩ := hcorr.exists_current
  have hval : atom.val = node.atom := by
    have h := hcorr.current
    rw [hcurrent] at h
    simpa using h
  let rawIndex : Fin mol.atomCount := ⟨node.atom, atomBound⟩
  have hloc : localizedIndexOf mol input agreement rawIndex = atom := by
    apply Fin.ext
    simp [rawIndex, localizedIndexOf, hval]
  have hz := (intakeAtomDataCorresponds mol input agreement rawIndex).1
  rw [hloc] at hz
  rw [MoleculeGraph.officialNodeAtomLabel, hcurrent]
  split <;>
    simp [MoleculeGraph.rawCIPAtomLabel, hz, atomZAt_eq_get mol node.atom atomBound, rawIndex]

/-- The second component of the localized node label is the raw Rule-2 mass for real atoms and
zero for duplicate/placeholder provenance. -/
theorem officialNodeAtomLabel_second_eq
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    {node : RawMolecule.CanonicalBranchNode}
    {onode : OfficialCIPNode input.Atom}
    (hcorr : NodeCorresponds (fun atom : input.Atom => atom.val) onode node)
    (atomBound : node.atom < mol.atomCount) :
    (ofLex (input.moleculeGraph.officialNodeAtomLabel onode)).2 =
      (match node.provenance with
       | RawMolecule.CanonicalNodeProvenance.realAtom => mol.atomMassAt node.atom
       | _ => 0) := by
  obtain ⟨atom, hcurrent⟩ := hcorr.exists_current
  have hval : atom.val = node.atom := by
    have h := hcorr.current
    rw [hcurrent] at h
    simpa using h
  let rawIndex : Fin mol.atomCount := ⟨node.atom, atomBound⟩
  have hloc : localizedIndexOf mol input agreement rawIndex = atom := by
    apply Fin.ext
    simp [rawIndex, localizedIndexOf, hval]
  have hm := (intakeAtomDataCorresponds mol input agreement rawIndex).2
  rw [hloc] at hm
  have hmAt : mol.atomMassAt node.atom = input.moleculeGraph.atomMass atom := hm.symm
  obtain hreal | ⟨distance, hpo, hpc⟩ | ⟨distance, hpo, hpc⟩ :=
    nodeProvenance_cases hcorr.provenance
  · rw [MoleculeGraph.officialNodeAtomLabel, hcurrent, hpo]
    simp [MoleculeGraph.rawCIPAtomLabel, hpc, hmAt]
  · rw [MoleculeGraph.officialNodeAtomLabel, hcurrent, hpo, hpc]
    simp
  · rw [MoleculeGraph.officialNodeAtomLabel, hcurrent, hpo, hpc]
    simp

/-- Columns-level constitutional correspondence.  This is the `ConstitutionalKeyCorresponds`
content without the completeness flag; it is what the recursive assembly transports. -/
structure ConstitutionalKeyColumnsCorrespond {V : Type*}
    (raw : RawMolecule.CanonicalBranchKey) (loc : OfficialRuleMajorKey V) : Prop where
  plain : ∀ e, e ∈ raw.rule1a.flatten → e.2.denominator = 1
  rule1a : plainRule1aProjection raw.rule1a = loc.rule1a
  rule1b : raw.rule1b = loc.rule1b
  rule2 : raw.rule2 = loc.rule2

/-- Forget the completeness field. -/
theorem ConstitutionalKeyCorresponds.toColumns {V : Type*}
    {raw : RawMolecule.CanonicalBranchKey} {loc : OfficialRuleMajorKey V}
    (h : ConstitutionalKeyCorresponds raw loc) :
    ConstitutionalKeyColumnsCorrespond raw loc :=
  ⟨h.plain, h.rule1a, h.rule1b, h.rule2⟩

/-- Add a proved completeness equality. -/
theorem ConstitutionalKeyColumnsCorrespond.toCorresponds {V : Type*}
    {raw : RawMolecule.CanonicalBranchKey} {loc : OfficialRuleMajorKey V}
    (h : ConstitutionalKeyColumnsCorrespond raw loc) (hcomplete : raw.complete = loc.complete) :
    ConstitutionalKeyCorresponds raw loc :=
  ⟨h.plain, h.rule1a, h.rule1b, h.rule2, hcomplete⟩

/-- Column correspondence for the two actually constructed root keys, at arbitrary completeness
flags. -/
theorem canonicalRootKey_columns
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    {node : RawMolecule.CanonicalBranchNode}
    {onode : OfficialCIPNode input.Atom}
    (hcorr : NodeCorresponds (fun atom : input.Atom => atom.val) onode node)
    (atomBound : node.atom < mol.atomCount)
    (domain : CanonicalRule1aPlainDomain mol node)
    (rawComplete locComplete : Bool) :
    ConstitutionalKeyColumnsCorrespond
      (mol.canonicalRootKey node rawComplete)
      (input.moleculeGraph.officialRuleMajorRootKey onode locComplete) := by
  have hlabel : mol.canonicalRule1aLabel node =
      { numerator := mol.atomZAt node.atom, denominator := 1 } := by
    unfold RawMolecule.canonicalRule1aLabel
    rw [domain]
  have hz := officialNodeAtomLabel_first_eq mol input agreement hcorr atomBound
  have hm := officialNodeAtomLabel_second_eq mol input agreement hcorr atomBound
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    have he' : e = ([], mol.canonicalRule1aLabel node) := by
      simpa [RawMolecule.canonicalRootKey] using he
    rw [he', hlabel]
  · simp [RawMolecule.canonicalRootKey, MoleculeGraph.officialRuleMajorRootKey,
      plainRule1aProjection, hlabel, hz]
  · simp [RawMolecule.canonicalRootKey, MoleculeGraph.officialRuleMajorRootKey,
      RawMolecule.CanonicalBranchNode.rule1bCode, hcorr.rule1bRootDistance_eq]
  · simp [RawMolecule.canonicalRootKey, MoleculeGraph.officialRuleMajorRootKey, hm]

/-! ## The canonical-order localized child enumeration -/

/-- The canonical branch node reconstructed from an official node's actual constructor data.
This is a total definition: the fallbacks are only inspected at nodes without a correspondence.
Placeholder provenance maps to the explicit phantom class, but the correspondence relation below
never relates a placeholder node. -/
def canonicalShadow {V : Type*} (toRaw : V → ℕ) (onode : OfficialCIPNode V) :
    RawMolecule.CanonicalBranchNode where
  atom := (onode.current?.map toRaw).getD 0
  parent :=
    match onode.parent? with
    | some parent => toRaw parent
    | none => (onode.current?.map toRaw).getD 0
  history := onode.history.map toRaw
  provenance :=
    match onode.provenance with
    | OfficialCIPNodeProvenance.realAtom => RawMolecule.CanonicalNodeProvenance.realAtom
    | OfficialCIPNodeProvenance.multipleBondDuplicate distance =>
        RawMolecule.CanonicalNodeProvenance.multipleBondDuplicate distance
    | OfficialCIPNodeProvenance.ringDuplicate distance =>
        RawMolecule.CanonicalNodeProvenance.ringDuplicate distance
    | OfficialCIPNodeProvenance.placeholder _ distance =>
        RawMolecule.CanonicalNodeProvenance.phantom distance

/-- A corresponding official node reconstructs exactly its canonical partner. -/
theorem canonicalShadow_eq_of_nodeCorresponds {V : Type*} {toRaw : V → ℕ}
    {onode : OfficialCIPNode V} {node : RawMolecule.CanonicalBranchNode}
    (h : NodeCorresponds toRaw onode node) :
    canonicalShadow toRaw onode = node := by
  obtain ⟨atom, hcurrent⟩ := h.exists_current
  have hatom : toRaw atom = node.atom := by
    have hmap := h.current
    rw [hcurrent] at hmap
    simpa using hmap
  have hshadowAtom : (onode.current?.map toRaw).getD 0 = node.atom := by
    rw [hcurrent]
    simpa using hatom
  have hshadowParent :
      (match onode.parent? with
       | some parent => toRaw parent
       | none => (onode.current?.map toRaw).getD 0) = node.parent := by
    cases hp : onode.parent? with
    | none =>
        have hnone := h.parent
        rw [hp] at hnone
        have heq : node.parent = node.atom := by
          by_cases hcase : node.parent = node.atom
          · exact hcase
          · rw [if_neg hcase] at hnone
            cases hnone
        rw [hp, hshadowAtom]
        exact heq.symm
    | some parent =>
        have hsome := h.parent
        rw [hp] at hsome
        have heq : node.parent = toRaw parent := by
          by_cases hcase : node.parent = node.atom
          · rw [if_pos hcase] at hsome
            cases hsome
          · rw [if_neg hcase] at hsome
            exact (Option.some.inj hsome).symm
        rw [hp]
        exact heq.symm
  have hshadowProvenance :
      (match onode.provenance with
       | OfficialCIPNodeProvenance.realAtom => RawMolecule.CanonicalNodeProvenance.realAtom
       | OfficialCIPNodeProvenance.multipleBondDuplicate distance =>
           RawMolecule.CanonicalNodeProvenance.multipleBondDuplicate distance
       | OfficialCIPNodeProvenance.ringDuplicate distance =>
           RawMolecule.CanonicalNodeProvenance.ringDuplicate distance
       | OfficialCIPNodeProvenance.placeholder _ distance =>
           RawMolecule.CanonicalNodeProvenance.phantom distance) = node.provenance := by
    cases h.provenance <;> rfl
  cases node
  simp [canonicalShadow, hshadowAtom, hshadowParent, h.history, hshadowProvenance]

/-- A canonical child copy's neighbor atom is a parsed atom index. -/
theorem canonicalChildCopy_fst_lt (mol : RawMolecule) (wellFormed : mol.WellFormed)
    {node : RawMolecule.CanonicalBranchNode} {copy : ℕ × ℕ}
    (hmem : copy ∈ mol.canonicalChildCopies node) : copy.1 < mol.atomCount := by
  have hseed :=
    RawLocalizedOxidoPathInvariant.mem_canonicalSeedCopies_of_mem_childCopies mol hmem
  have hpositive :=
    (RawMolecule.mem_canonicalSeedCopies_iff mol node wellFormed copy.1 copy.2).mp hseed
  exact (RawMolecule.bondOrder_pos_endpoint_lt mol wellFormed hpositive.1).2

/-- A canonical child copy's neighbor atom differs from the current atom. -/
theorem canonicalChildCopy_fst_ne (mol : RawMolecule) (wellFormed : mol.WellFormed)
    {node : RawMolecule.CanonicalBranchNode} {copy : ℕ × ℕ}
    (hmem : copy ∈ mol.canonicalChildCopies node) : copy.1 ≠ node.atom := by
  have hseed :=
    RawLocalizedOxidoPathInvariant.mem_canonicalSeedCopies_of_mem_childCopies mol hmem
  have hpositive :=
    (RawMolecule.mem_canonicalSeedCopies_iff mol node wellFormed copy.1 copy.2).mp hseed
  intro heq
  rw [heq, RawMolecule.bondOrder_self] at hpositive
  exact Nat.lt_irrefl 0 hpositive.1

/-- The localized official child enumeration in canonical raw-copy order.  The existing official
constructor `buildOfficialRuleMajorKey` is applied to this enumeration. -/
def localizedConstitutionalChildren (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (onode : OfficialCIPNode input.Atom) :
    List (OfficialCIPNode input.Atom) :=
  let node := canonicalShadow (fun atom : input.Atom => atom.val) onode
  if node.forcedLeaf then []
  else
    (mol.canonicalChildCopies node).attach.map fun copy =>
      onode.extend
        (localizedIndexOf mol input agreement
          ⟨copy.1.1, canonicalChildCopy_fst_lt mol wellFormed copy.2⟩)
        copy.1.2

/-- The canonical-order localized children are pointwise `NodeCorresponds` to the actual raw
canonical children. -/
theorem localizedConstitutionalChildren_forall₂
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed)
    {node : RawMolecule.CanonicalBranchNode} {onode : OfficialCIPNode input.Atom}
    (hcorr : NodeCorresponds (fun atom : input.Atom => atom.val) onode node) :
    List.Forall₂ (NodeCorresponds (fun atom : input.Atom => atom.val))
      (localizedConstitutionalChildren mol input agreement wellFormed onode)
      (mol.canonicalChildren node) := by
  have hshadow := canonicalShadow_eq_of_nodeCorresponds hcorr
  unfold localizedConstitutionalChildren
  rw [hshadow]
  by_cases hforced : node.forcedLeaf = true
  · simp [RawMolecule.canonicalChildren, hforced]
  · rw [if_neg hforced,
      Rule1bRepresentedAtomObservation.canonicalChildren_eq_map_canonicalChildOfCopy, if_neg hforced]
    refine forall₂_attach_map_map_of_forall _ _ _ _ ?_
    intro copy hmem
    have hne : (fun atom : input.Atom => atom.val)
        (localizedIndexOf mol input agreement
          ⟨copy.1, canonicalChildCopy_fst_lt mol wellFormed hmem⟩) ≠ node.atom := by
      simpa [localizedIndexOf] using canonicalChildCopy_fst_ne mol wellFormed hmem
    exact nodeCorresponds_extend_childOfCopy hcorr Fin.val_injective
      (localizedIndexOf mol input agreement
        ⟨copy.1, canonicalChildCopy_fst_lt mol wellFormed hmem⟩) copy.2 hne

/-- The raw terminal flag is exactly the emptiness of the canonical-order localized child list. -/
theorem canonicalTerminal_eq_localizedChildren_isEmpty
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed)
    {node : RawMolecule.CanonicalBranchNode} {onode : OfficialCIPNode input.Atom}
    (hcorr : NodeCorresponds (fun atom : input.Atom => atom.val) onode node) :
    mol.canonicalTerminal node =
      (localizedConstitutionalChildren mol input agreement wellFormed onode).isEmpty := by
  have hchildren :=
    localizedConstitutionalChildren_forall₂ mol input agreement wellFormed hcorr
  have hisEmpty :
      (localizedConstitutionalChildren mol input agreement wellFormed onode).isEmpty =
        (mol.canonicalChildren node).isEmpty :=
    isEmpty_eq_of_forall₂ hchildren
  by_cases hforced : node.forcedLeaf = true
  · have hcanonicalEmpty : (mol.canonicalChildren node).isEmpty = true := by
      simp [RawMolecule.canonicalChildren, hforced]
    simp [RawMolecule.canonicalTerminal, hforced, hisEmpty, hcanonicalEmpty]
  · have hforcedFalse : node.forcedLeaf = false := by
      cases hleaf : node.forcedLeaf <;> simp_all
    simp [RawMolecule.canonicalTerminal, hforcedFalse, hisEmpty]

/-! ## Comparison, insertion and sort correspondence -/

/-- Safe key comparison agrees on corresponding keys. -/
theorem compareCanonicalBranchKeys?_eq_of_corresponds {V : Type*}
    (leftKey rightKey : RawMolecule.CanonicalBranchKey)
    (leftLoc rightLoc : OfficialRuleMajorKey V)
    (leftCorr : ConstitutionalKeyCorresponds leftKey leftLoc)
    (rightCorr : ConstitutionalKeyCorresponds rightKey rightLoc) :
    RawMolecule.compareCanonicalBranchKeys? leftKey rightKey =
      OfficialRuleMajorKey.compare? leftLoc rightLoc := by
  unfold RawMolecule.compareCanonicalBranchKeys? OfficialRuleMajorKey.compare?
  rw [compareSparseCanonicalLayers_rule1a_eq_of_plain leftKey.rule1a rightKey.rule1a
      leftCorr.plain rightCorr.plain,
    leftCorr.rule1a, rightCorr.rule1a, leftCorr.complete, rightCorr.complete]
  by_cases hcomplete : (leftLoc.complete && rightLoc.complete) = true
  · simp only [hcomplete, if_true]
    rw [compareCanonicalBranchKeys_eq_officialRuleMajorKey_compare leftKey rightKey
      leftLoc rightLoc leftCorr rightCorr]
    cases hcmp : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        leftLoc.rule1a rightLoc.rule1a <;> rfl
  · simp only [hcomplete, if_false]
    cases hcmp : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        leftLoc.rule1a rightLoc.rule1a <;> rfl

/-- Insertion preserves the pointwise correspondence and produces a corresponding result. -/
theorem insertCanonicalKey?_corresponds {V : Type*}
    (key : RawMolecule.CanonicalBranchKey) (locKey : OfficialRuleMajorKey V)
    (keyCorr : ConstitutionalKeyCorresponds key locKey) :
    ∀ (keys : List RawMolecule.CanonicalBranchKey) (locKeys : List (OfficialRuleMajorKey V)),
      List.Forall₂ ConstitutionalKeyCorresponds keys locKeys → ∀ result,
      RawMolecule.insertCanonicalKey? key keys = some result →
      ∃ locResult, OfficialRuleMajorKey.insert? locKey locKeys = some locResult ∧
        List.Forall₂ ConstitutionalKeyCorresponds result locResult := by
  intro keys
  induction keys with
  | nil =>
      intro locKeys hcorr result hresult
      rw [List.forall₂_nil_left_iff] at hcorr
      subst locKeys
      simp [RawMolecule.insertCanonicalKey?] at hresult
      subst result
      exact ⟨[locKey], by simp [OfficialRuleMajorKey.insert?],
        List.Forall₂.cons keyCorr List.Forall₂.nil⟩
  | cons head tail ih =>
      intro locKeys hcorr result hresult
      rcases List.forall₂_cons_left_iff.mp hcorr with
        ⟨locHead, locTail, hhead, htail, rfl⟩
      have hcmp := compareCanonicalBranchKeys?_eq_of_corresponds key head locKey locHead
        keyCorr hhead
      cases hdecision : RawMolecule.compareCanonicalBranchKeys? key head with
      | none =>
          simp [RawMolecule.insertCanonicalKey?, hdecision] at hresult
      | some decision =>
          cases decision with
          | gt =>
              simp only [RawMolecule.insertCanonicalKey?, hdecision] at hresult
              subst result
              exact ⟨locKey :: locHead :: locTail, by
                simp [OfficialRuleMajorKey.insert?, hcmp, hdecision],
                List.Forall₂.cons keyCorr (List.Forall₂.cons hhead htail)⟩
          | eq =>
              simp only [RawMolecule.insertCanonicalKey?, hdecision] at hresult
              subst result
              exact ⟨locKey :: locHead :: locTail, by
                simp [OfficialRuleMajorKey.insert?, hcmp, hdecision],
                List.Forall₂.cons keyCorr (List.Forall₂.cons hhead htail)⟩
          | lt =>
              simp only [RawMolecule.insertCanonicalKey?, hdecision] at hresult
              rw [Option.map_eq_some_iff] at hresult
              rcases hresult with ⟨inserted, hinserted, hresultEq⟩
              subst result
              obtain ⟨locInserted, hlocInserted, hinsertedCorr⟩ :=
                ih locTail htail inserted hinserted
              refine ⟨locHead :: locInserted, ?_,
                List.Forall₂.cons hhead hinsertedCorr⟩
              simp [OfficialRuleMajorKey.insert?, hcmp, hdecision, hlocInserted]

/-- Sort preserves the pointwise correspondence and produces a corresponding result. -/
theorem sortCanonicalKeys?_corresponds {V : Type*}
    (keys : List RawMolecule.CanonicalBranchKey)
    (locKeys : List (OfficialRuleMajorKey V))
    (keysCorr : List.Forall₂ ConstitutionalKeyCorresponds keys locKeys) :
    ∀ result, RawMolecule.sortCanonicalKeys? keys = some result →
      ∃ locResult, OfficialRuleMajorKey.sort? locKeys = some locResult ∧
        List.Forall₂ ConstitutionalKeyCorresponds result locResult := by
  induction keys generalizing locKeys with
  | nil =>
      intro hcorr result hresult
      rw [List.forall₂_nil_left_iff] at hcorr
      subst locKeys
      simp [RawMolecule.sortCanonicalKeys?] at hresult
      subst result
      exact ⟨[], by simp [OfficialRuleMajorKey.sort?], List.Forall₂.nil⟩
  | cons head tail ih =>
      intro hcorr result hresult
      rcases List.forall₂_cons_left_iff.mp hcorr with
        ⟨locHead, locTail, hhead, htail, rfl⟩
      simp only [RawMolecule.sortCanonicalKeys?] at hresult
      change Option.bind (RawMolecule.sortCanonicalKeys? tail)
        (fun sorted => RawMolecule.insertCanonicalKey? head sorted) = some result at hresult
      rw [Option.bind_eq_some_iff] at hresult
      rcases hresult with ⟨sortedTail, hsortTail, hinsert⟩
      obtain ⟨locSortedTail, hlocSortTail, htailCorr⟩ := ih htail sortedTail hsortTail
      obtain ⟨locResult, hlocInsert, hresultCorr⟩ :=
        insertCanonicalKey?_corresponds head locHead hhead
          sortedTail locSortedTail htailCorr result hinsert
      refine ⟨locResult, ?_, hresultCorr⟩
      simp only [OfficialRuleMajorKey.sort?]
      change Option.bind (OfficialRuleMajorKey.sort? locTail)
        (fun sorted => OfficialRuleMajorKey.insert? locHead sorted) = some locResult
      rw [hlocSortTail]
      simpa using hlocInsert

/-- The all-complete flags of corresponding child lists agree. -/
theorem all_complete_eq_of_forall₂ {V : Type*}
    {childrenRaw : List RawMolecule.CanonicalBranchKey}
    {childrenLoc : List (OfficialRuleMajorKey V)}
    (h : List.Forall₂ ConstitutionalKeyCorresponds childrenRaw childrenLoc) :
    childrenRaw.all (fun child => child.complete) =
      childrenLoc.all (fun child => child.complete) := by
  induction h with
  | nil => rfl
  | cons hhead htail ih =>
      simp [List.all_cons, hhead.complete, ih]

/-! ## Merge and assembly correspondence -/

/-- Layer counts agree for corresponding child lists. -/
theorem canonicalChildLayerCount_eq_of_forall₂ {V α β : Type*}
    (childrenRaw : List RawMolecule.CanonicalBranchKey)
    (childrenLoc : List (OfficialRuleMajorKey V))
    (layersRaw : RawMolecule.CanonicalBranchKey → List (List α))
    (layersLoc : OfficialRuleMajorKey V → List (List β))
    (hcorr : List.Forall₂ ConstitutionalKeyCorresponds childrenRaw childrenLoc)
    (hlayers : ∀ raw loc, ConstitutionalKeyCorresponds raw loc →
      (layersRaw raw).length = (layersLoc loc).length) :
    RawMolecule.canonicalChildLayerCount childrenRaw layersRaw =
      OfficialRuleMajorKey.childLayerCount childrenLoc layersLoc := by
  induction hcorr with
  | nil => rfl
  | cons hhead htail ih =>
      simp [RawMolecule.canonicalChildLayerCount, OfficialRuleMajorKey.childLayerCount,
        hlayers _ _ hhead, ih]

/-- Projecting the merged raw Rule-1a layers gives the localized merge. -/
theorem plainRule1aProjection_mergeCanonicalAtomicChildren {V : Type*}
    (childrenRaw : List RawMolecule.CanonicalBranchKey)
    (childrenLoc : List (OfficialRuleMajorKey V))
    (hcorr : List.Forall₂ ConstitutionalKeyCorresponds childrenRaw childrenLoc) :
    plainRule1aProjection (RawMolecule.mergeCanonicalAtomicChildren childrenRaw) =
      OfficialRuleMajorKey.mergeChildren childrenLoc OfficialRuleMajorKey.rule1a := by
  have hcount := canonicalChildLayerCount_eq_of_forall₂ childrenRaw childrenLoc
    (fun child => child.rule1a) (fun child => child.rule1a) hcorr
    (fun raw loc h => by
      have hlen := congrArg List.length (rule1aProjection_eq_of_corresponds h)
      simpa [plainRule1aProjection_eq_map] using hlen)
  simp only [RawMolecule.mergeCanonicalAtomicChildren, OfficialRuleMajorKey.mergeChildren]
  rw [hcount]
  rw [plainRule1aProjection_eq_map]
  apply List.map_congr_left
  intro depth _
  rw [List.map_flatMap]
  apply flatMap_eq_of_forall₂ (forall₂_zipIdx hcorr depth)
  rintro ⟨rawKey, slot⟩ ⟨locKey, slot'⟩ ⟨hkey, hslot⟩
  subst slot'
  rw [rule1aLayerProjection_prefix, rule1aLayerProjection_getD,
    rule1aProjection_eq_of_corresponds hkey]

/-- Merging corresponding natural-number columns gives equal columns. -/
theorem mergeCanonicalNatChildren_eq_of_forall₂ {V : Type*}
    (childrenRaw : List RawMolecule.CanonicalBranchKey)
    (childrenLoc : List (OfficialRuleMajorKey V))
    (layersRaw : RawMolecule.CanonicalBranchKey → List (List RawMolecule.CanonicalNatEntry))
    (layersLoc : OfficialRuleMajorKey V → List (List RawMolecule.CanonicalNatEntry))
    (hcorr : List.Forall₂ ConstitutionalKeyCorresponds childrenRaw childrenLoc)
    (hlayers : ∀ raw loc, ConstitutionalKeyCorresponds raw loc → layersRaw raw = layersLoc loc) :
    RawMolecule.mergeCanonicalNatChildren layersRaw childrenRaw =
      OfficialRuleMajorKey.mergeChildren childrenLoc layersLoc := by
  have hcount := canonicalChildLayerCount_eq_of_forall₂ childrenRaw childrenLoc
    layersRaw layersLoc hcorr
    (fun raw loc h => congrArg List.length (hlayers raw loc h))
  simp only [RawMolecule.mergeCanonicalNatChildren, OfficialRuleMajorKey.mergeChildren]
  rw [hcount]
  apply List.map_congr_left
  intro depth _
  rw [List.map_flatMap]
  apply flatMap_eq_of_forall₂ (forall₂_zipIdx hcorr depth)
  rintro ⟨rawKey, slot⟩ ⟨locKey, slot'⟩ ⟨hkey, hslot⟩
  subst slot'
  rw [hlayers rawKey locKey hkey]
  rfl

/-- Every raw entry after the Rule-1a child merge is plain when all child keys are. -/
theorem mergeCanonicalAtomicChildren_plain {V : Type*}
    (childrenRaw : List RawMolecule.CanonicalBranchKey)
    (childrenLoc : List (OfficialRuleMajorKey V))
    (hcorr : List.Forall₂ ConstitutionalKeyCorresponds childrenRaw childrenLoc) :
    ∀ e, e ∈ (RawMolecule.mergeCanonicalAtomicChildren childrenRaw).flatten →
      e.2.denominator = 1 := by
  intro e he
  rw [RawMolecule.mergeCanonicalAtomicChildren, List.mem_flatten] at he
  rcases he with ⟨layer, hlayer, helayer⟩
  rw [List.mem_map] at hlayer
  rcases hlayer with ⟨depth, _hdepth, rfl⟩
  rw [List.mem_flatMap] at helayer
  rcases helayer with ⟨child, hchild, hechild⟩
  have hkeyMem : child.1 ∈ childrenRaw :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hchild)
  have hkeyCorr : ∃ locKey : OfficialRuleMajorKey V,
      ConstitutionalKeyCorresponds child.1 locKey := by
    rw [List.mem_iff_getElem?] at hkeyMem
    rcases hkeyMem with ⟨i, hi⟩
    have hiLt : i < childrenRaw.length := (List.getElem?_eq_some_iff.mp hi).1
    have hiLt' : i < childrenLoc.length := by
      rw [← hcorr.length_eq]
      exact hiLt
    refine ⟨childrenLoc.get ⟨i, hiLt'⟩, ?_⟩
    have hget := hcorr.get hiLt hiLt'
    simpa [(List.getElem?_eq_some_iff.mp hi).2] using hget
  rcases hkeyCorr with ⟨locKey, hcorrKey⟩
  rw [RawMolecule.prefixCanonicalAtomicLayer, List.mem_map] at hechild
  rcases hechild with ⟨original, horiginal, heq⟩
  have horiginalFlat : original ∈ child.1.rule1a.flatten :=
    mem_flatten_getD horiginal
  have hplain := hcorrKey.plain original horiginalFlat
  rw [← heq]
  exact hplain

/-- Column correspondence is preserved by the assembled constructor. -/
theorem assembleCanonicalBranchKey_columns {V : Type*}
    (rootRaw : RawMolecule.CanonicalBranchKey) (rootLoc : OfficialRuleMajorKey V)
    (childrenRaw : List RawMolecule.CanonicalBranchKey)
    (childrenLoc : List (OfficialRuleMajorKey V))
    (rootColumns : ConstitutionalKeyColumnsCorrespond rootRaw rootLoc)
    (childrenCorr : List.Forall₂ ConstitutionalKeyCorresponds childrenRaw childrenLoc) :
    ConstitutionalKeyColumnsCorrespond
      (RawMolecule.assembleCanonicalBranchKey rootRaw childrenRaw)
      (OfficialRuleMajorKey.assemble rootLoc childrenLoc) := by
  refine ⟨?plain, ?rule1a, ?rule1b, ?rule2⟩
  · intro e he
    have he' : e ∈ (rootRaw.rule1a ++
        RawMolecule.mergeCanonicalAtomicChildren childrenRaw).flatten := by
      simpa [RawMolecule.assembleCanonicalBranchKey] using he
    rw [List.flatten_append, List.mem_append] at he'
    rcases he' with he' | he'
    · exact rootColumns.plain e he'
    · exact mergeCanonicalAtomicChildren_plain childrenRaw childrenLoc childrenCorr e he'
  · simp only [RawMolecule.assembleCanonicalBranchKey, OfficialRuleMajorKey.assemble]
    rw [plainRule1aProjection_append, rootColumns.rule1a,
      plainRule1aProjection_mergeCanonicalAtomicChildren childrenRaw childrenLoc childrenCorr]
  · simp only [RawMolecule.assembleCanonicalBranchKey, OfficialRuleMajorKey.assemble]
    rw [rootColumns.rule1b,
      mergeCanonicalNatChildren_eq_of_forall₂ childrenRaw childrenLoc
        (fun child => child.rule1b) (fun child => child.rule1b) childrenCorr
        (fun raw loc h => h.rule1b)]
  · simp only [RawMolecule.assembleCanonicalBranchKey, OfficialRuleMajorKey.assemble]
    rw [rootColumns.rule2,
      mergeCanonicalNatChildren_eq_of_forall₂ childrenRaw childrenLoc
        (fun child => child.rule2) (fun child => child.rule2) childrenCorr
        (fun raw loc h => h.rule2)]

/-! ## The fuel induction -/

/-- **Constructed constitutional-key correspondence.**  The actually constructed raw canonical
branch key and the official localized rule-major key built from the canonical-order child
enumeration have corresponding constitutional columns and completeness.

The induction is on the raw fuel.  At every node the child lists are positionally aligned by
`localizedConstitutionalChildren_forall₂`; the child key list correspondence is therefore an
ordinary `Forall₂`, and the sort is transported by `sortCanonicalKeys?_corresponds`. -/
theorem buildCanonicalBranchKey_constitutionalKeyCorresponds
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed)
    (root : RawMolecule.CanonicalBranchNode)
    (rootHist : root.history = [root.atom])
    (rootBound : root.atom < mol.atomCount)
    (plainDomain : ∀ node, ReachableCanonical mol root node →
      CanonicalRule1aPlainDomain mol node)
    (node : RawMolecule.CanonicalBranchNode)
    (onode : OfficialCIPNode input.Atom)
    (reach : ReachableCanonical mol root node)
    (hcorr : NodeCorresponds (fun atom : input.Atom => atom.val) onode node)
    (cap fuel : ℕ)
    (rawKey : RawMolecule.CanonicalBranchKey)
    (locKey : OfficialRuleMajorKey input.Atom)
    (rawBuild : mol.buildCanonicalBranchKey cap fuel node = some rawKey)
    (locBuild : input.moleculeGraph.buildOfficialRuleMajorKey
      (localizedConstitutionalChildren mol input agreement wellFormed) fuel onode =
        some locKey) :
    ConstitutionalKeyCorresponds rawKey locKey := by
  induction fuel generalizing node onode reach hcorr cap rawKey locKey with
  | zero =>
      have hdomain := plainDomain node reach
      have hterminal := canonicalTerminal_eq_localizedChildren_isEmpty
        mol input agreement wellFormed hcorr
      have hatomBound :=
        RawLocalizedOxidoPathInvariant.reachable_atom_lt mol root rootHist rootBound wellFormed
          node reach
      simp only [RawMolecule.buildCanonicalBranchKey] at rawBuild
      rw [hdomain] at rawBuild
      simp only [Option.bind_some, Option.some.injEq] at rawBuild
      simp only [MoleculeGraph.buildOfficialRuleMajorKey, Option.some.injEq] at locBuild
      subst rawKey
      subst locKey
      exact (canonicalRootKey_columns mol input agreement hcorr hatomBound hdomain
        (mol.canonicalTerminal node)
        (localizedConstitutionalChildren mol input agreement wellFormed onode).isEmpty).toCorresponds
        hterminal
  | succ fuel ih =>
      have hatomBound :=
        RawLocalizedOxidoPathInvariant.reachable_atom_lt mol root rootHist rootBound wellFormed
          node reach
      have hdomain := plainDomain node reach
      have hterminal := canonicalTerminal_eq_localizedChildren_isEmpty
        mol input agreement wellFormed hcorr
      have hchildrenList :=
        localizedConstitutionalChildren_forall₂ mol input agreement wellFormed hcorr
      by_cases hempty :
          (localizedConstitutionalChildren mol input agreement wellFormed onode).isEmpty = true
      · -- Terminal raw and localized nodes.
        have hterminalTrue : mol.canonicalTerminal node = true := by
          rw [hterminal, hempty]
        simp only [RawMolecule.buildCanonicalBranchKey] at rawBuild
        rw [hdomain, hterminalTrue] at rawBuild
        simp only [Option.some.injEq] at rawBuild
        simp only [MoleculeGraph.buildOfficialRuleMajorKey, hempty, Option.some.injEq] at locBuild
        subst rawKey
        subst locKey
        exact (canonicalRootKey_columns mol input agreement hcorr hatomBound hdomain
          true true).toCorresponds rfl
      · have hemptyFalse :
            (localizedConstitutionalChildren mol input agreement wellFormed onode).isEmpty =
              false := by
          cases hvalue :
              (localizedConstitutionalChildren mol input agreement wellFormed onode).isEmpty
          · rfl
          · exact absurd hvalue hempty
        have hterminalFalse : mol.canonicalTerminal node = false := by
          rw [hterminal, hemptyFalse]
        -- Raw side.
        simp only [RawMolecule.buildCanonicalBranchKey] at rawBuild
        rw [hdomain, hterminalFalse] at rawBuild
        simp only [Bool.false_eq_true, if_false] at rawBuild
        by_cases hwidth : 3 < (mol.canonicalChildren node).length
        · simp [hwidth] at rawBuild
        · rw [if_neg hwidth] at rawBuild
          simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at rawBuild
          rcases rawBuild with ⟨rawChildKeys, hrawChildBuild, rawBuild⟩
          rcases rawBuild with ⟨rawSorted, hrawSort, rawBuild⟩
          -- Last step: the budget guard and the final assembly.
          by_cases hcap : cap <
              (RawMolecule.assembleCanonicalBranchKey
                (mol.canonicalRootKey node
                  (rawSorted.all fun child => child.complete)) rawSorted).nodeCount
          · simp [hcap] at rawBuild
          · simp only [hcap, if_false, Option.some.injEq] at rawBuild
            -- Localized side.
            simp only [MoleculeGraph.buildOfficialRuleMajorKey, hemptyFalse] at locBuild
            simp only [Bool.false_eq_true, if_false, Option.bind_eq_some_iff] at locBuild
            rcases locBuild with ⟨locChildKeys, hlocChildBuild, locBuild⟩
            rcases locBuild with ⟨locSorted, hlocSort, locBuild⟩
            simp only [Option.some.injEq] at locBuild
            -- Child-key correspondence.
            have hreachAll :
                ∀ child ∈ mol.canonicalChildren node,
                  ReachableCanonical mol root child :=
              fun child hmem => ReachableCanonical.child node child reach hmem
            have hchildKeysCorr :
                List.Forall₂ ConstitutionalKeyCorresponds rawChildKeys locChildKeys := by
              have aux :
                  ∀ (officialChildren : List (OfficialCIPNode input.Atom))
                    (canonicalChildren : List RawMolecule.CanonicalBranchNode),
                    List.Forall₂ (NodeCorresponds (fun atom : input.Atom => atom.val))
                      officialChildren canonicalChildren →
                    (∀ child ∈ canonicalChildren,
                      ReachableCanonical mol root child) →
                    ∀ (remaining : ℕ)
                      (rawKeys : List RawMolecule.CanonicalBranchKey)
                      (locKeys : List (OfficialRuleMajorKey input.Atom)),
                      RawMolecule.buildCanonicalChildKeys
                        (fun remaining child =>
                          mol.buildCanonicalBranchKey remaining fuel child)
                        remaining canonicalChildren = some rawKeys →
                      officialChildren.mapM
                        (fun ochild =>
                          input.moleculeGraph.buildOfficialRuleMajorKey
                            (localizedConstitutionalChildren mol input agreement wellFormed)
                            fuel ochild) = some locKeys →
                      List.Forall₂ ConstitutionalKeyCorresponds rawKeys locKeys := by
                intro officialChildren canonicalChildren hmatches
                induction hmatches with
                | nil =>
                    intro hreachAll remaining rawKeys locKeys hraw hloc
                    simp only [RawMolecule.buildCanonicalChildKeys, Option.some.injEq] at hraw
                    simp only [List.mapM, Option.pure_def, Option.some.injEq] at hloc
                    subst rawKeys
                    subst locKeys
                    exact List.Forall₂.nil
                | cons hhead htail ihList =>
                    intro hreachAll remaining rawKeys locKeys hraw hloc
                    have hreachHead : ReachableCanonical mol root _ :=
                      hreachAll _ (by simp)
                    simp only [RawMolecule.buildCanonicalChildKeys] at hraw
                    rw [Option.bind_eq_some_iff] at hraw
                    rcases hraw with ⟨rawHead, hrawHead, hrawRest⟩
                    by_cases hguard : remaining < rawHead.nodeCount
                    · simp [hguard] at hrawRest
                    · rw [if_neg hguard, Option.bind_eq_some_iff] at hrawRest
                      rcases hrawRest with ⟨rawRest, hrawRestBuild, hrawOut⟩
                      simp only [List.mapM_cons] at hloc
                      rw [Option.bind_eq_some_iff] at hloc
                      rcases hloc with ⟨locHead, hlocHead, hlocRest⟩
                      rw [Option.bind_eq_some_iff] at hlocRest
                      rcases hlocRest with ⟨locRest, hlocRestBuild, hlocOut⟩
                      have hrawKeysEq : rawKeys = rawHead :: rawRest := by
                        simpa using hrawOut.symm
                      have hlocKeysEq : locKeys = locHead :: locRest := by
                        simpa using hlocOut.symm
                      subst rawKeys
                      subst locKeys
                      have hheadCorr : ConstitutionalKeyCorresponds rawHead locHead :=
                        ih _ _ hreachHead hhead remaining rawHead locHead hrawHead hlocHead
                      have htailReach :
                          ∀ child ∈ canonicalChildren,
                            ReachableCanonical mol root child :=
                        fun child hmem =>
                          hreachAll child (List.mem_cons_of_mem _ hmem)
                      have htailCorr : List.Forall₂ ConstitutionalKeyCorresponds rawRest locRest :=
                        ihList htailReach (remaining - rawHead.nodeCount) rawRest locRest
                          hrawRestBuild hlocRestBuild
                      exact List.Forall₂.cons hheadCorr htailCorr
              exact aux _ _ hchildrenList hreachAll (cap - 1) rawChildKeys locChildKeys
                hrawChildBuild hlocChildBuild
            -- Sorted child keys.
            obtain ⟨locSortedKey, hlocSortKey, hsortedCorr⟩ :=
              sortCanonicalKeys?_corresponds rawChildKeys locChildKeys hchildKeysCorr
                rawSorted hrawSort
            -- The localized sort result is the one produced by the localized builder.
            have hlocSortedEq : locSortedKey = locSorted := by
              rw [hlocSort] at hlocSortKey
              simpa using hlocSortKey.symm
            subst locSortedKey
            -- Root columns and assembly.
            have hrootColumns := canonicalRootKey_columns mol input agreement hcorr hatomBound
              hdomain (rawSorted.all fun child => child.complete) false
            have hassembleColumns :=
              assembleCanonicalBranchKey_columns
                (mol.canonicalRootKey node (rawSorted.all fun child => child.complete))
                (input.moleculeGraph.officialRuleMajorRootKey onode false)
                rawSorted locSorted hrootColumns hsortedCorr
            subst rawKey
            subst locKey
            refine hassembleColumns.toCorresponds ?_
            simp only [RawMolecule.assembleCanonicalBranchKey, OfficialRuleMajorKey.assemble]
            exact all_complete_eq_of_forall₂ hsortedCorr

/-! ## Comparator endpoint -/

/-- The actual constructed raw and localized constitutional comparators agree at every reachable
node, for the canonical-order localized child enumeration. -/
theorem constructed_constitutional_compare_eq
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed)
    (root : RawMolecule.CanonicalBranchNode)
    (rootHist : root.history = [root.atom])
    (rootBound : root.atom < mol.atomCount)
    (plainDomain : ∀ node, ReachableCanonical mol root node →
      CanonicalRule1aPlainDomain mol node)
    (node : RawMolecule.CanonicalBranchNode)
    (onode : OfficialCIPNode input.Atom)
    (reach : ReachableCanonical mol root node)
    (hcorr : NodeCorresponds (fun atom : input.Atom => atom.val) onode node)
    (cap fuel : ℕ)
    (rawKey : RawMolecule.CanonicalBranchKey)
    (locKey : OfficialRuleMajorKey input.Atom)
    (rawBuild : mol.buildCanonicalBranchKey cap fuel node = some rawKey)
    (locBuild : input.moleculeGraph.buildOfficialRuleMajorKey
      (localizedConstitutionalChildren mol input agreement wellFormed) fuel onode =
        some locKey) :
    RawMolecule.compareCanonicalBranchKeys rawKey rawKey =
      OfficialRuleMajorKey.compare locKey locKey := by
  have hcorrKey := buildCanonicalBranchKey_constitutionalKeyCorresponds mol input agreement
    wellFormed root rootHist rootBound plainDomain node onode reach hcorr cap fuel rawKey locKey
    rawBuild locBuild
  exact compareCanonicalBranchKeys_eq_officialRuleMajorKey_compare rawKey rawKey locKey locKey
    hcorrKey hcorrKey

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.rule1aEntryProjection
assert_kernel_only TetraStereo.OneCenter.rule1aLayerProjection
assert_kernel_only TetraStereo.OneCenter.plainRule1aProjection_eq_map
assert_kernel_only TetraStereo.OneCenter.plainRule1aProjection_append
assert_kernel_only TetraStereo.OneCenter.rule1aLayerProjection_prefix
assert_kernel_only TetraStereo.OneCenter.map_getD_layer
assert_kernel_only TetraStereo.OneCenter.rule1aLayerProjection_getD
assert_kernel_only TetraStereo.OneCenter.rule1aProjection_eq_of_corresponds
assert_kernel_only TetraStereo.OneCenter.forall₂_attach_map_map_of_forall
assert_kernel_only TetraStereo.OneCenter.isEmpty_eq_of_forall₂
assert_kernel_only TetraStereo.OneCenter.forall₂_append
assert_kernel_only TetraStereo.OneCenter.forall₂_zipIdx
assert_kernel_only TetraStereo.OneCenter.flatMap_eq_of_forall₂
assert_kernel_only TetraStereo.OneCenter.mem_flatten_getD
assert_kernel_only TetraStereo.OneCenter.atomZAt_eq_get
assert_kernel_only TetraStereo.OneCenter.CanonicalRule1aPlainDomain
assert_kernel_only TetraStereo.OneCenter.officialNodeAtomLabel_first_eq
assert_kernel_only TetraStereo.OneCenter.officialNodeAtomLabel_second_eq
assert_kernel_only TetraStereo.OneCenter.ConstitutionalKeyColumnsCorrespond
assert_kernel_only TetraStereo.OneCenter.ConstitutionalKeyCorresponds.toColumns
assert_kernel_only TetraStereo.OneCenter.ConstitutionalKeyColumnsCorrespond.toCorresponds
assert_kernel_only TetraStereo.OneCenter.canonicalRootKey_columns
assert_kernel_only TetraStereo.OneCenter.canonicalShadow
assert_kernel_only TetraStereo.OneCenter.canonicalShadow_eq_of_nodeCorresponds
assert_kernel_only TetraStereo.OneCenter.canonicalChildCopy_fst_lt
assert_kernel_only TetraStereo.OneCenter.canonicalChildCopy_fst_ne
assert_kernel_only TetraStereo.OneCenter.localizedConstitutionalChildren
assert_kernel_only TetraStereo.OneCenter.localizedConstitutionalChildren_forall₂
assert_kernel_only TetraStereo.OneCenter.canonicalTerminal_eq_localizedChildren_isEmpty
assert_kernel_only TetraStereo.OneCenter.compareCanonicalBranchKeys?_eq_of_corresponds
assert_kernel_only TetraStereo.OneCenter.insertCanonicalKey?_corresponds
assert_kernel_only TetraStereo.OneCenter.sortCanonicalKeys?_corresponds
assert_kernel_only TetraStereo.OneCenter.all_complete_eq_of_forall₂
assert_kernel_only TetraStereo.OneCenter.canonicalChildLayerCount_eq_of_forall₂
assert_kernel_only TetraStereo.OneCenter.plainRule1aProjection_mergeCanonicalAtomicChildren
assert_kernel_only TetraStereo.OneCenter.mergeCanonicalNatChildren_eq_of_forall₂
assert_kernel_only TetraStereo.OneCenter.mergeCanonicalAtomicChildren_plain
assert_kernel_only TetraStereo.OneCenter.assembleCanonicalBranchKey_columns
assert_kernel_only TetraStereo.OneCenter.buildCanonicalBranchKey_constitutionalKeyCorresponds
assert_kernel_only TetraStereo.OneCenter.constructed_constitutional_compare_eq
