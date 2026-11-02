
































import TetraStereo.OneCenter.CIPAuthoritativeRule1bObservation
import TetraStereo.OneCenter.OfficialRuleMajorObservation
import TetraStereo.OneCenter.LocalizedCanonicalRuntimeKeyCorrespondence
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.RawOfficialObservedKeyTransport

/-! ## Shared auxiliary definitions -/

/-- The Rule-2 mass of a canonical root key: the atomic mass at a real atom, zero otherwise
(matching the inline `mass` of `RawMolecule.canonicalRootKeyAuthoritativeWithRule1b?`). -/
def canonicalRootRule2Mass (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode) : ℕ :=
  match node.provenance with
  | RawMolecule.CanonicalNodeProvenance.realAtom => mol.atomMassAt node.atom
  | _ => 0

/-- Correspondence of a raw canonical branch key and a localized official rule-major key on the
constitutional comparison projection, *without* the `complete` flag.  This is the nonterminal-root
correspondence: the canonical root carries the sorted-child all-test while the official root is
`complete := false`. -/
structure ObservedKeyCorresponds {V : Type*}
    (raw : RawMolecule.CanonicalBranchKey) (loc : OfficialRuleMajorKey V) : Prop where
  plain : ∀ e, e ∈ raw.rule1a.flatten → e.2.denominator = 1
  rule1a : plainRule1aProjection raw.rule1a = loc.rule1a
  rule1b : raw.rule1b = loc.rule1b
  rule2 : raw.rule2 = loc.rule2

/-- Option-level relational correspondence: `some`/`some` carries `R`, `none`/`none` is vacuous. -/
def OptionCorresponds {α β : Type*} (R : α → β → Prop) : Option α → Option β → Prop
  | some a, some b => R a b
  | none, none => True
  | _, _ => False

/-- The inline canonical root structure of the observed-key builder, factored out so the root
correspondence can be stated without repeating the constructor. -/
def canonicalRootKeyWith (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (complete : Bool) (rule1a : RawMolecule.CIPAtomicLabel) (rule1bDistance : ℕ) :
    RawMolecule.CanonicalBranchKey :=
  { rule1a := [[([], rule1a)]]
    rule1b := [[([], rule1bDistance)]]
    rule2 := [[([], canonicalRootRule2Mass mol node)]]
    realAtoms :=
      match node.provenance with
      | RawMolecule.CanonicalNodeProvenance.realAtom => [[([], node.atom)]]
      | _ => [[]]
    sourceNodes := [[([], node)]]
    sourceOccurrences := [([], node)]
    sourceTree? := some (.node node .nil)
    complete := complete }

/-! ## Option / structure correspondence lemmas -/

private theorem OptionCorresponds.map {α β γ δ : Type*} (R : α → β → Prop) (S : γ → δ → Prop)
    (f : α → γ) (g : β → δ) (h : ∀ {a : α} {b : β}, R a b → S (f a) (g b))
    {oa : Option α} {ob : Option β} (hab : OptionCorresponds R oa ob) :
    OptionCorresponds S (oa.map f) (ob.map g) := by
  cases oa <;> cases ob <;> simp [OptionCorresponds] at hab ⊢
  exact h hab

private theorem OptionCorresponds.bind {α β γ δ : Type*} (R : α → β → Prop) (S : γ → δ → Prop)
    (f : α → Option γ) (g : β → Option δ)
    (h : ∀ {a : α} {b : β}, R a b → OptionCorresponds S (f a) (g b))
    {oa : Option α} {ob : Option β} (hab : OptionCorresponds R oa ob) :
    OptionCorresponds S (oa.bind f) (ob.bind g) := by
  cases oa <;> cases ob <;> simp [OptionCorresponds] at hab ⊢
  exact h hab

private theorem OptionCorresponds.some {α β : Type*} (R : α → β → Prop) {a : α} {b : β}
    (hab : R a b) : OptionCorresponds R (some a) (some b) := hab

private theorem ObservedKeyCorresponds.toConstitutional {V : Type*}
    {raw : RawMolecule.CanonicalBranchKey} {loc : OfficialRuleMajorKey V}
    (h : ObservedKeyCorresponds raw loc) (hcomplete : raw.complete = loc.complete) :
    ConstitutionalKeyCorresponds raw loc :=
  { plain := h.plain, rule1a := h.rule1a, rule1b := h.rule1b, rule2 := h.rule2,
    complete := hcomplete }

/-! ## List structural correspondence lemmas -/

private theorem foldl_max_length_eq_of_forall₂ {α β γ δ : Type*} {R : α → β → Prop}
    (f : α → List γ) (g : β → List δ)
    (h : ∀ {a : α} {b : β}, R a b → (f a).length = (g b).length) :
    ∀ (acc : ℕ) (as : List α) (bs : List β), List.Forall₂ R as bs →
      (as.foldl (fun longest a => max longest (f a).length) acc) =
        (bs.foldl (fun longest b => max longest (g b).length) acc)
  | acc, [], [], List.Forall₂.nil => by simp [List.foldl_nil]
  | acc, a :: as, b :: bs, List.Forall₂.cons hab hrest => by
      simp only [List.foldl_cons]
      rw [h hab]
      exact foldl_max_length_eq_of_forall₂ f g h (max acc (g b).length) as bs hrest

private theorem flatMap_zipIdx_eq_of_forall₂ {α β γ δ : Type*} {R : α → β → Prop}
    (f : α → ℕ → List γ) (g : β → ℕ → List δ)
    (h : ∀ {a : α} {b : β}, R a b → ∀ slot, f a slot = g b slot) :
    ∀ (as : List α) (bs : List β), List.Forall₂ R as bs → ∀ (start : ℕ),
      (as.zipIdx start).flatMap (fun child => f child.1 child.2) =
        (bs.zipIdx start).flatMap (fun child => g child.1 child.2)
  | [], [], List.Forall₂.nil => by
      intro start
      simp [List.zipIdx, List.flatMap]
  | a :: as, b :: bs, List.Forall₂.cons hab hrest => by
      intro start
      simp only [List.zipIdx_cons, List.flatMap_cons]
      rw [h hab start, flatMap_zipIdx_eq_of_forall₂ f g h as bs hrest (start + 1)]

private theorem Forall₂_exists_of_mem_left {α β : Type*} {R : α → β → Prop}
    {a : α} {as : List α} {bs : List β} :
    List.Forall₂ R as bs → a ∈ as → ∃ b, R a b ∧ b ∈ bs := by
  intro hfor
  induction hfor with
  | nil => intro hmem; cases hmem
  | cons h hrest ih => intro hmem
      rw [List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · subst a
        exact ⟨_, h, by simp⟩
      · rcases ih hmem with ⟨b, hb, hbmem⟩
        exact ⟨b, hb, by simp [hbmem]⟩

private theorem mem_getD_of_mem_flatten {α : Type*} {layers : List (List α)} {depth : ℕ} {e : α} :
    e ∈ layers.getD depth [] → e ∈ layers.flatten := by
  intro h
  rw [List.getD_eq_getElem?_getD] at h
  cases hget : layers[depth]? with
  | none => cases (show False by simpa [hget] using h)
  | some layer =>
      refine ⟨layer, ?_, ?_⟩
      · rw [List.mem_iff_getElem?]
        exact ⟨depth, hget⟩
      · simpa [hget] using h

private theorem Forall₂.all_eq {α β : Type*} {R : α → β → Prop} (f : α → Bool) (g : β → Bool)
    (h : ∀ {a : α} {b : β}, R a b → f a = g b) :
    ∀ (as : List α) (bs : List β), List.Forall₂ R as bs → as.all f = bs.all g
  | [], [], List.Forall₂.nil => by simp
  | a :: as, b :: bs, List.Forall₂.cons hab hrest => by
      simp only [List.all_cons]
      rw [h hab, Forall₂.all_eq f g h as bs hrest]

private theorem mapM_corresponds {α β γ δ : Type*} (R : α → β → Prop) (S : γ → δ → Prop)
    (f : α → Option γ) (g : β → Option δ)
    (h : ∀ {a : α} {b : β}, R a b → OptionCorresponds S (f a) (g b)) :
    ∀ (as : List α) (bs : List β), List.Forall₂ R as bs →
      OptionCorresponds (List.Forall₂ S) (as.mapM f) (bs.mapM g)
  | [], [], List.Forall₂.nil => by simp [OptionCorresponds]
  | a :: as, b :: bs, List.Forall₂.cons hab hrest => by
      simp only [List.mapM_cons]
      exact OptionCorresponds.bind S (List.Forall₂ S)
        (fun x => (as.mapM f).bind (fun xs => some (x :: xs)))
        (fun y => (bs.mapM g).bind (fun ys => some (y :: ys)))
        (fun x y hxy => OptionCorresponds.bind S (List.Forall₂ S)
          (fun xs => some (x :: xs)) (fun ys => some (y :: ys))
          (fun xs ys hxys => OptionCorresponds.some (List.Forall₂ S) (List.Forall₂.cons hxy hxys))
          (mapM_corresponds R S f g h as bs hrest))
        (h hab)

/-! ## Rule-1a projection lemmas -/

/-- Numerator projection of one plain Rule-1a layer, landing in the localized sparse-entry
vocabulary. -/
def plainRule1aLayer (layer : List RawMolecule.CanonicalAtomicEntry) :
    List (OfficialSparseEntry ℕ) :=
  layer.map fun e => (e.1, e.2.numerator)

private theorem plainRule1aLayer_prefix (slot : ℕ) (layer : List RawMolecule.CanonicalAtomicEntry) :
    plainRule1aLayer (RawMolecule.prefixCanonicalAtomicLayer slot layer) =
      OfficialRuleMajorKey.prefixLayer slot (plainRule1aProjection layer) := by
  unfold plainRule1aLayer RawMolecule.prefixCanonicalAtomicLayer
    OfficialRuleMajorKey.prefixLayer plainRule1aProjection
  rw [List.map_map, List.map_map]
  rfl

private theorem plainRule1aProjection_getD (layers : List (List RawMolecule.CanonicalAtomicEntry))
    (depth : ℕ) :
    plainRule1aProjection (layers.getD depth []) =
      (plainRule1aProjection layers).getD depth [] := by
  unfold plainRule1aProjection
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_map]
  cases h : layers[depth]? <;> rfl

private theorem plainRule1aProjection_append (a b : List (List RawMolecule.CanonicalAtomicEntry)) :
    plainRule1aProjection (a ++ b) = plainRule1aProjection a ++ plainRule1aProjection b := by
  simp [plainRule1aProjection]

private theorem mergeCanonicalAtomicChildren_plain_of_forall₂ {V : Type*}
    (rawList : List RawMolecule.CanonicalBranchKey) (locList : List (OfficialRuleMajorKey V))
    (corr : List.Forall₂ (@ConstitutionalKeyCorresponds V) rawList locList)
    (e : RawMolecule.CanonicalAtomicEntry) :
    e ∈ (RawMolecule.mergeCanonicalAtomicChildren rawList).flatten → e.2.denominator = 1 := by
  intro h
  unfold RawMolecule.mergeCanonicalAtomicChildren at h
  rw [List.mem_flatten] at h
  rcases h with ⟨layer, hlayer, he⟩
  rw [List.mem_map] at hlayer
  rcases hlayer with ⟨depth, _hdepth, rfl⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨child, hchild, he⟩
  rw [List.mem_map] at he
  rcases he with ⟨entry, hentry, rfl⟩
  have hchildMem : child.1 ∈ rawList := List.fst_mem_of_mem_zipIdx hchild
  rcases Forall₂_exists_of_mem_left corr hchildMem with ⟨loc, hcorr, _⟩
  exact hcorr.plain entry (mem_getD_of_mem_flatten hentry)

/-! ## Comparator / insertion / sort transport -/

/-- The safe key comparator is transported by the full key correspondence. -/
theorem compareCanonicalBranchKeys?_corresponds {V : Type*}
    (keyRaw keyOther : RawMolecule.CanonicalBranchKey)
    (keyLoc keyOtherLoc : OfficialRuleMajorKey V)
    (corr : ConstitutionalKeyCorresponds keyRaw keyLoc)
    (otherCorr : ConstitutionalKeyCorresponds keyOther keyOtherLoc) :
    RawMolecule.compareCanonicalBranchKeys? keyRaw keyOther =
      OfficialRuleMajorKey.compare? keyLoc keyOtherLoc := by
  simp only [RawMolecule.compareCanonicalBranchKeys?, OfficialRuleMajorKey.compare?]
  rw [compareSparseCanonicalLayers_rule1a_eq_of_plain keyRaw.rule1a keyOther.rule1a
      corr.plain otherCorr.plain,
    corr.rule1a, otherCorr.rule1a, corr.complete, otherCorr.complete,
    compareCanonicalBranchKeys_eq_officialRuleMajorKey_compare keyRaw keyOther keyLoc keyOtherLoc
      corr otherCorr]
  rfl

/-- Structural insertion transports the correspondence. -/
theorem insertCanonicalKey?_corresponds {V : Type*} :
    ∀ (keyRaw : RawMolecule.CanonicalBranchKey) (keyLoc : OfficialRuleMajorKey V)
      (keysRaw : List RawMolecule.CanonicalBranchKey) (keysLoc : List (OfficialRuleMajorKey V)),
      ConstitutionalKeyCorresponds keyRaw keyLoc →
      List.Forall₂ (@ConstitutionalKeyCorresponds V) keysRaw keysLoc →
        OptionCorresponds (List.Forall₂ (@ConstitutionalKeyCorresponds V))
          (RawMolecule.insertCanonicalKey? keyRaw keysRaw)
          (OfficialRuleMajorKey.insert? keyLoc keysLoc)
  | keyRaw, keyLoc, [], [], keyCorr, List.Forall₂.nil => by
      simp [RawMolecule.insertCanonicalKey?, OfficialRuleMajorKey.insert?, OptionCorresponds, keyCorr]
  | keyRaw, keyLoc, headRaw :: tailRaw, headLoc :: tailLoc, keyCorr, List.Forall₂.cons hCorr tCorr => by
      simp only [RawMolecule.insertCanonicalKey?, OfficialRuleMajorKey.insert?]
      rw [compareCanonicalBranchKeys?_corresponds keyRaw headRaw keyLoc headLoc keyCorr hCorr]
      cases hcmp : OfficialRuleMajorKey.compare? keyLoc headLoc with
      | none => simp [OptionCorresponds]
      | some decision =>
          cases decision with
          | gt => simp [OptionCorresponds, keyCorr, hCorr, tCorr]
          | eq => simp [OptionCorresponds, keyCorr, hCorr, tCorr]
          | lt =>
              change OptionCorresponds (List.Forall₂ (@ConstitutionalKeyCorresponds V))
                ((RawMolecule.insertCanonicalKey? keyRaw tailRaw).map (fun sorted => headRaw :: sorted))
                ((OfficialRuleMajorKey.insert? keyLoc tailLoc).map (fun sorted => headLoc :: sorted))
              exact OptionCorresponds.map (List.Forall₂ (@ConstitutionalKeyCorresponds V))
                (List.Forall₂ (@ConstitutionalKeyCorresponds V))
                (fun sorted => headRaw :: sorted) (fun sorted => headLoc :: sorted)
                (fun x y hxy => List.Forall₂.cons hCorr hxy)
                (RawMolecule.insertCanonicalKey? keyRaw tailRaw)
                (OfficialRuleMajorKey.insert? keyLoc tailLoc)
                (insertCanonicalKey?_corresponds keyRaw keyLoc tailRaw tailLoc keyCorr tCorr)

/-- Structural descending sort transports the correspondence. -/
theorem sortCanonicalKeys?_corresponds {V : Type*} :
    ∀ (keysRaw : List RawMolecule.CanonicalBranchKey) (keysLoc : List (OfficialRuleMajorKey V)),
      List.Forall₂ (@ConstitutionalKeyCorresponds V) keysRaw keysLoc →
        OptionCorresponds (List.Forall₂ (@ConstitutionalKeyCorresponds V))
          (RawMolecule.sortCanonicalKeys? keysRaw)
          (OfficialRuleMajorKey.sort? keysLoc)
  | [], [], List.Forall₂.nil => by
      simp [RawMolecule.sortCanonicalKeys?, OfficialRuleMajorKey.sort?, OptionCorresponds]
  | keyRaw :: keysRaw, keyLoc :: keysLoc, List.Forall₂.cons hCorr tCorr => by
      simp only [RawMolecule.sortCanonicalKeys?, OfficialRuleMajorKey.sort?]
      exact OptionCorresponds.bind (List.Forall₂ (@ConstitutionalKeyCorresponds V))
        (List.Forall₂ (@ConstitutionalKeyCorresponds V))
        (fun sorted => RawMolecule.insertCanonicalKey? keyRaw sorted)
        (fun sorted => OfficialRuleMajorKey.insert? keyLoc sorted)
        (fun x y hxy => insertCanonicalKey?_corresponds keyRaw keyLoc x y hCorr hxy)
        (sortCanonicalKeys?_corresponds keysRaw keysLoc tCorr)

/-! ## Child-layer merge transport -/

/-- The canonical and official natural-number child-layer merges agree after the actual child
constructor relation on the natural layers. -/
theorem mergeCanonicalNatChildren_eq_mergeChildren_of_forall₂ {V : Type*}
    (rawList : List RawMolecule.CanonicalBranchKey) (locList : List (OfficialRuleMajorKey V))
    (rawLayers : RawMolecule.CanonicalBranchKey → List (List RawMolecule.CanonicalNatEntry))
    (locLayers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry ℕ)))
    (corr : List.Forall₂ (fun raw loc => rawLayers raw = locLayers loc) rawList locList) :
    RawMolecule.mergeCanonicalNatChildren rawLayers rawList =
      OfficialRuleMajorKey.mergeChildren locList locLayers := by
  unfold RawMolecule.mergeCanonicalNatChildren OfficialRuleMajorKey.mergeChildren
    RawMolecule.canonicalChildLayerCount OfficialRuleMajorKey.childLayerCount
  rw [foldl_max_length_eq_of_forall₂ rawLayers locLayers (fun a b h => congrArg List.length h) 0
    rawList locList corr]
  apply List.map_congr_left
  intro depth _present
  exact flatMap_zipIdx_eq_of_forall₂
    (fun a slot => RawMolecule.prefixCanonicalNatLayer slot ((rawLayers a).getD depth []))
    (fun b slot => OfficialRuleMajorKey.prefixLayer slot ((locLayers b).getD depth []))
    (fun a b h slot => by rw [h])
    rawList locList corr 0

/-- The canonical Rule-1a numerator projection of the atomic child-layer merge equals the official
Rule-1a child-layer merge. -/
theorem plainRule1aProjection_mergeCanonicalAtomicChildren_eq_mergeChildren_of_forall₂ {V : Type*}
    (rawList : List RawMolecule.CanonicalBranchKey) (locList : List (OfficialRuleMajorKey V))
    (corr : List.Forall₂ (fun raw loc => plainRule1aProjection raw.rule1a = loc.rule1a) rawList locList) :
    plainRule1aProjection (RawMolecule.mergeCanonicalAtomicChildren rawList) =
      OfficialRuleMajorKey.mergeChildren locList OfficialRuleMajorKey.rule1a := by
  unfold RawMolecule.mergeCanonicalAtomicChildren OfficialRuleMajorKey.mergeChildren
    RawMolecule.canonicalChildLayerCount OfficialRuleMajorKey.childLayerCount
    plainRule1aProjection
  rw [foldl_max_length_eq_of_forall₂ (fun raw => raw.rule1a) (fun loc => loc.rule1a)
    (fun a b h => by
      have hlen := congrArg List.length h
      simpa [plainRule1aProjection] using hlen)
    0 rawList locList corr]
  rw [List.map_map]
  apply List.map_congr_left
  intro depth _present
  simp only [Function.comp_apply]
  rw [List.map_flatMap]
  exact flatMap_zipIdx_eq_of_forall₂
    (fun a slot => plainRule1aLayer (RawMolecule.prefixCanonicalAtomicLayer slot (a.rule1a.getD depth [])))
    (fun b slot => OfficialRuleMajorKey.prefixLayer slot (b.rule1a.getD depth []))
    (fun a b h slot => by
      rw [plainRule1aLayer_prefix, plainRule1aProjection_getD, h])
    rawList locList corr 0

/-! ## Assemble transport -/

/-- The assemble step transports the correspondence, with the nonterminal `complete` asymmetry
resolved by an explicit `completeEq` hypothesis. -/
theorem assembleCanonicalBranchKey_corresponds {V : Type*}
    (rootRaw : RawMolecule.CanonicalBranchKey) (rootLoc : OfficialRuleMajorKey V)
    (sortedRaw : List RawMolecule.CanonicalBranchKey) (sortedLoc : List (OfficialRuleMajorKey V))
    (rootCorr : ObservedKeyCorresponds rootRaw rootLoc)
    (childrenCorr : List.Forall₂ (@ConstitutionalKeyCorresponds V) sortedRaw sortedLoc)
    (completeEq : rootRaw.complete = sortedLoc.all OfficialRuleMajorKey.complete) :
    ConstitutionalKeyCorresponds (RawMolecule.assembleCanonicalBranchKey rootRaw sortedRaw)
      (OfficialRuleMajorKey.assemble rootLoc sortedLoc) := by
  refine ⟨?plain, ?rule1a, ?rule1b, ?rule2, ?complete⟩
  · simp only [RawMolecule.assembleCanonicalBranchKey]
    intro e he
    rw [List.flatten_append, List.mem_append] at he
    rcases he with hroot | hmerged
    · exact rootCorr.plain e hroot
    · exact mergeCanonicalAtomicChildren_plain_of_forall₂ sortedRaw sortedLoc childrenCorr e hmerged
  · simp only [RawMolecule.assembleCanonicalBranchKey, OfficialRuleMajorKey.assemble]
    rw [plainRule1aProjection_append, rootCorr.rule1a]
    congr 1
    exact plainRule1aProjection_mergeCanonicalAtomicChildren_eq_mergeChildren_of_forall₂
      sortedRaw sortedLoc (List.Forall₂.imp (fun raw loc h => h.rule1a) childrenCorr)
  · simp only [RawMolecule.assembleCanonicalBranchKey, OfficialRuleMajorKey.assemble]
    rw [rootCorr.rule1b]
    congr 1
    exact mergeCanonicalNatChildren_eq_mergeChildren_of_forall₂ sortedRaw sortedLoc
      (fun child => child.rule1b) OfficialRuleMajorKey.rule1b
      (List.Forall₂.imp (fun raw loc h => h.rule1b) childrenCorr)
  · simp only [RawMolecule.assembleCanonicalBranchKey, OfficialRuleMajorKey.assemble]
    rw [rootCorr.rule2]
    congr 1
    exact mergeCanonicalNatChildren_eq_mergeChildren_of_forall₂ sortedRaw sortedLoc
      (fun child => child.rule2) OfficialRuleMajorKey.rule2
      (List.Forall₂.imp (fun raw loc h => h.rule2) childrenCorr)
  · exact completeEq

/-! ## Root key transport -/

/-- The observation-parameterized canonical root key and the official root key correspond on the
constitutional projection (ignoring `complete`). -/
private theorem rootKey_observed_corresponds {V : Type*} [Fintype V] [DecidableEq V]
    (mol : RawMolecule) (m : MoleculeGraph V) (observeLoc : OfficialCIPNode V → ℕ)
    (onode : OfficialCIPNode V) (node : RawMolecule.CanonicalBranchNode)
    (completeRaw : Bool) (completeLoc : Bool)
    (label : RawMolecule.CIPAtomicLabel) (distance : ℕ)
    (hlabel : label = { numerator := (ofLex (m.officialNodeAtomLabel onode)).1, denominator := 1 })
    (hdistance : distance = observeLoc onode)
    (hmass : canonicalRootRule2Mass mol node = (ofLex (m.officialNodeAtomLabel onode)).2) :
    ObservedKeyCorresponds (canonicalRootKeyWith mol node completeRaw label distance)
      (MoleculeGraph.officialRuleMajorRootKeyWith observeLoc m onode completeLoc) := by
  refine ⟨?plain, ?rule1a, ?rule1b, ?rule2⟩
  · intro e he
    simp [canonicalRootKeyWith] at he
    rcases he with rfl
    rw [hlabel]
    rfl
  · simp [plainRule1aProjection, canonicalRootKeyWith,
      MoleculeGraph.officialRuleMajorRootKeyWith, hlabel]
  · simp [canonicalRootKeyWith, MoleculeGraph.officialRuleMajorRootKeyWith, hdistance]
  · simp [canonicalRootKeyWith, MoleculeGraph.officialRuleMajorRootKeyWith, hmass]

/-- The observation-parameterized canonical root key builder is transported to the official root
key builder, with equal observations. -/
theorem canonicalRootKeyAuthoritativeWithRule1b?_corresponds {V : Type*} [Fintype V] [DecidableEq V]
    (mol : RawMolecule) (m : MoleculeGraph V)
    (observeRaw : RawMolecule.CanonicalBranchNode → Option ℕ)
    (observeLoc : OfficialCIPNode V → ℕ)
    (R : RawMolecule.CanonicalBranchNode → OfficialCIPNode V → Prop)
    (observeAgree : ∀ onode node, R node onode → observeRaw node = some (observeLoc onode))
    (rule1aAgree : ∀ onode node, R node onode →
      mol.canonicalRule1aLabelAuthoritative? node =
        some { numerator := (ofLex (m.officialNodeAtomLabel onode)).1, denominator := 1 })
    (rule2Agree : ∀ onode node, R node onode →
      canonicalRootRule2Mass mol node = (ofLex (m.officialNodeAtomLabel onode)).2)
    (onode : OfficialCIPNode V) (node : RawMolecule.CanonicalBranchNode) (rel : R node onode)
    (complete : Bool) :
    OptionCorresponds (@ConstitutionalKeyCorresponds V)
      (mol.canonicalRootKeyAuthoritativeWithRule1b? observeRaw node complete)
      (some (MoleculeGraph.officialRuleMajorRootKeyWith observeLoc m onode complete)) := by
  exact OptionCorresponds.map (@ObservedKeyCorresponds V) (@ConstitutionalKeyCorresponds V)
    (fun key => key) (fun key => key) (fun h => h.toConstitutional rfl)
    (by
      simp [canonicalRootKeyAuthoritativeWithRule1b?, officialRuleMajorRootKeyWith,
        OptionCorresponds, rule1aAgree onode node rel, observeAgree onode node rel,
        rootKey_observed_corresponds mol m observeLoc onode node complete complete
          { numerator := (ofLex (m.officialNodeAtomLabel onode)).1, denominator := 1 }
          (observeLoc onode) rfl rfl (rule2Agree onode node rel)])

/-! ## Headline: recursive observed-key transport -/

/-- The full observation-parameterized canonical branch key compiler is transported to the official
rule-major key compiler, under a positionwise child relation and a canonical width-cap side
condition.  No source is assumed aligned with the other; the correspondence is derived from the
node relation plus equal observations. -/
theorem buildCanonicalBranchKeyAuthoritativeWithRule1b_corresponds {V : Type*}
    [Fintype V] [DecidableEq V]
    (mol : RawMolecule) (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V))
    (observeRaw : RawMolecule.CanonicalBranchNode → Option ℕ)
    (observeLoc : OfficialCIPNode V → ℕ)
    (R : RawMolecule.CanonicalBranchNode → OfficialCIPNode V → Prop)
    (observeAgree : ∀ onode node, R node onode → observeRaw node = some (observeLoc onode))
    (rule1aAgree : ∀ onode node, R node onode →
      mol.canonicalRule1aLabelAuthoritative? node =
        some { numerator := (ofLex (m.officialNodeAtomLabel onode)).1, denominator := 1 })
    (rule2Agree : ∀ onode node, R node onode →
      canonicalRootRule2Mass mol node = (ofLex (m.officialNodeAtomLabel onode)).2)
    (terminalAgree : ∀ onode node, R node onode →
      mol.canonicalTerminal node = (children onode).isEmpty)
    (widthOk : ∀ onode node, R node onode →
      ¬ RawMolecule.authoritativeChildSlots < (mol.canonicalChildren node).length)
    (childrenCorr : ∀ onode node, R node onode →
      List.Forall₂ R (mol.canonicalChildren node) (children onode)) :
    ∀ (fuel : ℕ) (onode : OfficialCIPNode V) (node : RawMolecule.CanonicalBranchNode),
      R node onode →
        OptionCorresponds (@ConstitutionalKeyCorresponds V)
          (mol.buildCanonicalBranchKeyAuthoritativeWithRule1b observeRaw fuel node)
          (MoleculeGraph.buildOfficialRuleMajorKeyWith observeLoc m children fuel onode)
  | 0, onode, node, rel => by
      rw [terminalAgree onode node rel]
      exact canonicalRootKeyAuthoritativeWithRule1b?_corresponds mol m observeRaw observeLoc R
        observeAgree rule1aAgree rule2Agree onode node rel (children onode).isEmpty
  | fuel + 1, onode, node, rel => by
      unfold buildCanonicalBranchKeyAuthoritativeWithRule1b buildOfficialRuleMajorKeyWith
      by_cases terminal : mol.canonicalTerminal node = true
      · have hterminalOfficial : (children onode).isEmpty = true := by
          simpa [terminalAgree onode node rel] using terminal
        simp [terminal, hterminalOfficial]
        exact canonicalRootKeyAuthoritativeWithRule1b?_corresponds mol m observeRaw observeLoc R
          observeAgree rule1aAgree rule2Agree onode node rel true
      · have hnotOfficial : ¬ (children onode).isEmpty = true := by
          intro h
          apply terminal
          simpa [terminalAgree onode node rel] using h
        simp only [if_neg terminal, if_neg hnotOfficial]
        by_cases tooWide : RawMolecule.authoritativeChildSlots < (mol.canonicalChildren node).length
        · exfalso
          exact (widthOk onode node rel) tooWide
        · simp only [if_neg tooWide]
          exact OptionCorresponds.bind (List.Forall₂ (@ConstitutionalKeyCorresponds V))
            (@ConstitutionalKeyCorresponds V)
            (fun childKeysRaw =>
              (RawMolecule.sortCanonicalKeys? childKeysRaw).bind (fun sorted =>
                (mol.canonicalRootKeyAuthoritativeWithRule1b? observeRaw node
                  (sorted.all fun child => child.complete)).bind (fun root =>
                  some (RawMolecule.assembleCanonicalBranchKey root sorted))))
            (fun childKeysLoc =>
              (OfficialRuleMajorKey.sort? childKeysLoc).bind (fun sorted =>
                some (OfficialRuleMajorKey.assemble
                  (MoleculeGraph.officialRuleMajorRootKeyWith observeLoc m onode false) sorted)))
            (fun childKeysRaw childKeysLoc hchildKeys =>
              OptionCorresponds.bind (List.Forall₂ (@ConstitutionalKeyCorresponds V))
                (@ConstitutionalKeyCorresponds V)
                (fun sortedRaw =>
                  (mol.canonicalRootKeyAuthoritativeWithRule1b? observeRaw node
                    (sortedRaw.all fun child => child.complete)).bind (fun root =>
                    some (RawMolecule.assembleCanonicalBranchKey root sortedRaw)))
                (fun sortedLoc =>
                  some (OfficialRuleMajorKey.assemble
                    (MoleculeGraph.officialRuleMajorRootKeyWith observeLoc m onode false) sortedLoc))
                (fun sortedRaw sortedLoc hsorted => by
                  have hrootSome : mol.canonicalRootKeyAuthoritativeWithRule1b? observeRaw node
                      (sortedRaw.all fun child => child.complete) =
                      some (canonicalRootKeyWith mol node (sortedRaw.all fun child => child.complete)
                        { numerator := (ofLex (m.officialNodeAtomLabel onode)).1, denominator := 1 }
                        (observeLoc onode)) := by
                    simp [canonicalRootKeyAuthoritativeWithRule1b?, rule1aAgree onode node rel,
                      observeAgree onode node rel]
                  rw [hrootSome]
                  change OptionCorresponds (@ConstitutionalKeyCorresponds V)
                    (some (RawMolecule.assembleCanonicalBranchKey
                      (canonicalRootKeyWith mol node (sortedRaw.all fun child => child.complete)
                        { numerator := (ofLex (m.officialNodeAtomLabel onode)).1, denominator := 1 }
                        (observeLoc onode)) sortedRaw))
                    (some (OfficialRuleMajorKey.assemble
                      (MoleculeGraph.officialRuleMajorRootKeyWith observeLoc m onode false) sortedLoc))
                  exact OptionCorresponds.some (@ConstitutionalKeyCorresponds V)
                    (assembleCanonicalBranchKey_corresponds
                      (canonicalRootKeyWith mol node (sortedRaw.all fun child => child.complete)
                        { numerator := (ofLex (m.officialNodeAtomLabel onode)).1, denominator := 1 }
                        (observeLoc onode))
                      (MoleculeGraph.officialRuleMajorRootKeyWith observeLoc m onode false)
                      sortedRaw sortedLoc
                      (rootKey_observed_corresponds mol m observeLoc onode node
                        (sortedRaw.all fun child => child.complete) false
                        { numerator := (ofLex (m.officialNodeAtomLabel onode)).1, denominator := 1 }
                        (observeLoc onode) rfl rfl (rule2Agree onode node rel))
                      hsorted
                      (by
                        rw [show (canonicalRootKeyWith mol node
                            (sortedRaw.all fun child => child.complete)
                            { numerator := (ofLex (m.officialNodeAtomLabel onode)).1, denominator := 1 }
                            (observeLoc onode)).complete =
                            sortedRaw.all (fun child => child.complete) from rfl,
                          Forall₂.all_eq (fun child => child.complete) OfficialRuleMajorKey.complete
                            (fun a b h => h.complete) sortedRaw sortedLoc hsorted])))
                (sortCanonicalKeys?_corresponds childKeysRaw childKeysLoc hchildKeys))
            (mapM_corresponds R (@ConstitutionalKeyCorresponds V)
              (fun child => mol.buildCanonicalBranchKeyAuthoritativeWithRule1b observeRaw fuel child)
              (fun child => MoleculeGraph.buildOfficialRuleMajorKeyWith observeLoc m children fuel child)
              (fun child onode' hrel =>
                buildCanonicalBranchKeyAuthoritativeWithRule1b_corresponds mol m children observeRaw
                  observeLoc R observeAgree rule1aAgree rule2Agree terminalAgree widthOk childrenCorr
                  fuel onode' child hrel)
              (mol.canonicalChildren node) (children onode) (childrenCorr onode node rel))

end TetraStereo.OneCenter.RawOfficialObservedKeyTransport

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.RawOfficialObservedKeyTransport.compareCanonicalBranchKeys?_corresponds
assert_kernel_only TetraStereo.OneCenter.RawOfficialObservedKeyTransport.insertCanonicalKey?_corresponds
assert_kernel_only TetraStereo.OneCenter.RawOfficialObservedKeyTransport.sortCanonicalKeys?_corresponds
assert_kernel_only TetraStereo.OneCenter.RawOfficialObservedKeyTransport.mergeCanonicalNatChildren_eq_mergeChildren_of_forall₂
assert_kernel_only TetraStereo.OneCenter.RawOfficialObservedKeyTransport.plainRule1aProjection_mergeCanonicalAtomicChildren_eq_mergeChildren_of_forall₂
assert_kernel_only TetraStereo.OneCenter.RawOfficialObservedKeyTransport.assembleCanonicalBranchKey_corresponds
assert_kernel_only TetraStereo.OneCenter.RawOfficialObservedKeyTransport.canonicalRootKeyAuthoritativeWithRule1b?_corresponds
assert_kernel_only TetraStereo.OneCenter.RawOfficialObservedKeyTransport.buildCanonicalBranchKeyAuthoritativeWithRule1b_corresponds
