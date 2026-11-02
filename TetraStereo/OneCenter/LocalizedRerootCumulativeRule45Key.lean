import TetraStereo.OneCenter.LocalizedRerootRuleMajorKey

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Cumulative Rules-4a--5 keys over occurrence reroot cursors

A later sequence rule may refine only a tie under every earlier rule.  Therefore a recursive
Rule-4c key cannot sort siblings by `r/s` alone: its node observations must retain Rule 4a and the
selected Rule-4b reading ahead of Rule 4c.  Likewise a Rule-5 reading retains Rules 4a--4c ahead
of its senior/junior bit.

This module encodes that requirement as a cumulative observation vector and recursively compiles
it over exact reroot cursors.  Each parent sorts complete child keys lexicographically by the full
constitutional key and then by the cumulative descriptor projection.  Only after this lawful
sorting are final sibling-slot addresses assigned and descendant spheres merged.

The Rule-4c constructor currently takes one proved Rule-4b reference.  The two-reference
alternative required by P-92.5.2.1(c) remains a compound-key layer above this unary reading; it is
not collapsed or guessed here.
-/

namespace CertifiedLocalizedCIPInput

/-- Cumulative descriptor reading.  Every constructor includes all earlier Rule-4 stages. -/
inductive LocalizedCumulativeRule45Stage where
  | rule4a
  | rule4b (reference : RS)
  | rule4cNoReference
  | rule4c (rule4bReference : RS)
  | rule5NoRule4bReference (rule5Reference : RS)
  | rule5 (rule4bReference : RS) (rule5Reference : RS)
  deriving DecidableEq, Repr

/-- Rule-4a unit-kind priority carried by one occurrence label. -/
def localizedRule4aPriority : Option LocalizedAuxiliaryLabel → Nat
  | none => 0
  | some (.pseudoasymmetric _) => 1
  | some (.chiral _) => 2

/-- Like/unlike bit for an uppercase label under one Rule-4b reference. -/
def localizedRule4bPriority (reference : RS) : Option LocalizedAuxiliaryLabel → Nat
  | some (.chiral descriptor) => if descriptor == reference then 1 else 0
  | none | some (.pseudoasymmetric _) => 0

/-- Rule-4c rank for the current tetrahedral lowercase family. -/
def localizedRule4cPriority : Option LocalizedAuxiliaryLabel → Nat
  | some (.pseudoasymmetric .r) => 1
  | none | some (.chiral _) | some (.pseudoasymmetric .s) => 0

/-- Senior/junior Rule-5 bit under one common reference. -/
def localizedRule5Priority (reference : RS) : Option LocalizedAuxiliaryLabel → Nat
  | some (.chiral descriptor) => if descriptor == reference then 1 else 0
  | none | some (.pseudoasymmetric _) => 0

/-- Full cumulative node vector for the selected stage. -/
def localizedCumulativeRule45Priority
    (stage : LocalizedCumulativeRule45Stage)
    (label : Option LocalizedAuxiliaryLabel) : List Nat :=
  match stage with
  | .rule4a => [localizedRule4aPriority label]
  | .rule4b reference =>
      [localizedRule4aPriority label, localizedRule4bPriority reference label]
  | .rule4cNoReference =>
      [localizedRule4aPriority label, localizedRule4cPriority label]
  | .rule4c reference =>
      [localizedRule4aPriority label, localizedRule4bPriority reference label,
        localizedRule4cPriority label]
  | .rule5NoRule4bReference rule5Reference =>
      [localizedRule4aPriority label,
        localizedRule4cPriority label,
        localizedRule5Priority rule5Reference label]
  | .rule5 rule4bReference rule5Reference =>
      [localizedRule4aPriority label,
        localizedRule4bPriority rule4bReference label,
        localizedRule4cPriority label,
        localizedRule5Priority rule5Reference label]

/-! ## Rule-4b reference populations -/

/-- Uppercase chiral descriptors at exactly one hierarchy-rank path.  Multiplicity is retained
because P-92.5.2.1(b) selects the descriptor occurring most often among equivalent highest-ranked
nodes. -/
def localizedChiralDescriptorsAtRank
    (rank : List Nat) :
    List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)) → List RS
  | [] => []
  | (observedRank, label) :: observations =>
      let tail := localizedChiralDescriptorsAtRank rank observations
      if observedRank = rank then
        match label with
        | some (.chiral descriptor) => descriptor :: tail
        | none | some (.pseudoasymmetric _) => tail
      else tail

/-- Population attached to the first uppercase chiral rank class in one already hierarchy-ordered
sphere.  Pseudoasymmetric and unlabeled nodes do not choose a Rule-4b reference. -/
def localizedFirstChiralRankPopulationInLayer :
    List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)) → Option (List RS)
  | [] => none
  | (rank, label) :: observations =>
      match label with
      | some (.chiral descriptor) =>
          some (descriptor :: localizedChiralDescriptorsAtRank rank observations)
      | none | some (.pseudoasymmetric _) =>
          localizedFirstChiralRankPopulationInLayer observations

/-- Descriptor population at the first sphere containing an uppercase chiral rank class. -/
def localizedFirstChiralRankPopulation :
    List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) → List RS
  | [] => []
  | layer :: layers =>
      match localizedFirstChiralRankPopulationInLayer layer with
      | some descriptors => descriptors
      | none => localizedFirstChiralRankPopulation layers

/-- P-92.5.2.1 reference choice from the equivalent highest-ranked descriptor population. -/
def localizedRule4bReferencesFromPopulation (descriptors : List RS) : List RS :=
  if descriptors.isEmpty then []
  else
    let rCount := (descriptors.filter fun descriptor => descriptor == RS.R).length
    let sCount := (descriptors.filter fun descriptor => descriptor == RS.S).length
    if sCount < rCount then [RS.R]
    else if rCount < sCount then [RS.S]
    else [RS.R, RS.S]

/-- Complete Rule-4b reference selection from hierarchy-rank-addressed exact labels. -/
def localizedRule4bReferencesFromRankedLabels
    (layers : List (List
      (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) : List RS :=
  localizedRule4bReferencesFromPopulation
    (localizedFirstChiralRankPopulation layers)

/-! ### Reflection of the Rules-4a--4c observation language -/

/-- Mirror only uppercase auxiliary descriptors.  Lowercase pseudoasymmetric observations are
reflection-invariant at the Rule-4b/4c boundary. -/
def reflectUppercaseAuxiliaryLabel : LocalizedAuxiliaryLabel → LocalizedAuxiliaryLabel
  | .chiral descriptor => .chiral (RS.swap descriptor)
  | .pseudoasymmetric descriptor => .pseudoasymmetric descriptor

def reflectUppercaseOptionalLabel :
    Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel :=
  Option.map reflectUppercaseAuxiliaryLabel

def reflectUppercaseRankedEntry
    (entry : OfficialSparseEntry (Option LocalizedAuxiliaryLabel)) :
    OfficialSparseEntry (Option LocalizedAuxiliaryLabel) :=
  (entry.1, reflectUppercaseOptionalLabel entry.2)

def reflectUppercaseRankedLabels
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :=
  layers.map (List.map reflectUppercaseRankedEntry)

@[simp] theorem localizedRule4aPriority_reflectUppercase
    (label : Option LocalizedAuxiliaryLabel) :
    localizedRule4aPriority (reflectUppercaseOptionalLabel label) =
      localizedRule4aPriority label := by
  cases label with
  | none => rfl
  | some label => cases label <;> rfl

@[simp] theorem localizedRule4bPriority_reflectUppercase
    (reference : RS) (label : Option LocalizedAuxiliaryLabel) :
    localizedRule4bPriority (RS.swap reference)
        (reflectUppercaseOptionalLabel label) =
      localizedRule4bPriority reference label := by
  cases reference <;> cases label with
  | none => rfl
  | some label =>
      cases label with
      | pseudoasymmetric descriptor => rfl
      | chiral descriptor => cases descriptor <;> rfl

@[simp] theorem localizedRule4cPriority_reflectUppercase
    (label : Option LocalizedAuxiliaryLabel) :
    localizedRule4cPriority (reflectUppercaseOptionalLabel label) =
      localizedRule4cPriority label := by
  cases label with
  | none => rfl
  | some label => cases label <;> rfl

@[simp] theorem localizedCumulativeRule45Priority_rule4b_reflectUppercase
    (reference : RS) (label : Option LocalizedAuxiliaryLabel) :
    localizedCumulativeRule45Priority (.rule4b (RS.swap reference))
        (reflectUppercaseOptionalLabel label) =
      localizedCumulativeRule45Priority (.rule4b reference) label := by
  simp [localizedCumulativeRule45Priority]

@[simp] theorem localizedCumulativeRule45Priority_rule4c_reflectUppercase
    (reference : RS) (label : Option LocalizedAuxiliaryLabel) :
    localizedCumulativeRule45Priority (.rule4c (RS.swap reference))
        (reflectUppercaseOptionalLabel label) =
      localizedCumulativeRule45Priority (.rule4c reference) label := by
  simp [localizedCumulativeRule45Priority]

theorem localizedChiralDescriptorsAtRank_reflectUppercase
    (rank : List Nat) : ∀ observations,
    localizedChiralDescriptorsAtRank rank
        (observations.map reflectUppercaseRankedEntry) =
      (localizedChiralDescriptorsAtRank rank observations).map RS.swap
  | [] => rfl
  | (observedRank, label) :: observations => by
      cases label with
      | none =>
          simp [localizedChiralDescriptorsAtRank, reflectUppercaseRankedEntry,
            reflectUppercaseOptionalLabel,
            localizedChiralDescriptorsAtRank_reflectUppercase rank observations]
      | some label =>
          cases label with
          | pseudoasymmetric descriptor =>
              simp [localizedChiralDescriptorsAtRank, reflectUppercaseRankedEntry,
                reflectUppercaseOptionalLabel, reflectUppercaseAuxiliaryLabel,
                localizedChiralDescriptorsAtRank_reflectUppercase rank observations]
          | chiral descriptor =>
              by_cases sameRank : observedRank = rank <;>
                simp [localizedChiralDescriptorsAtRank, reflectUppercaseRankedEntry,
                  reflectUppercaseOptionalLabel, reflectUppercaseAuxiliaryLabel,
                  localizedChiralDescriptorsAtRank_reflectUppercase rank observations,
                  sameRank]

theorem localizedFirstChiralRankPopulationInLayer_reflectUppercase : ∀ observations,
    localizedFirstChiralRankPopulationInLayer
        (observations.map reflectUppercaseRankedEntry) =
      (localizedFirstChiralRankPopulationInLayer observations).map (List.map RS.swap)
  | [] => rfl
  | (rank, label) :: observations => by
      cases label with
      | none =>
          simpa [localizedFirstChiralRankPopulationInLayer,
            reflectUppercaseRankedEntry, reflectUppercaseOptionalLabel] using
            localizedFirstChiralRankPopulationInLayer_reflectUppercase observations
      | some label =>
          cases label with
          | pseudoasymmetric descriptor =>
              simpa [localizedFirstChiralRankPopulationInLayer,
                reflectUppercaseRankedEntry, reflectUppercaseOptionalLabel,
                reflectUppercaseAuxiliaryLabel] using
                localizedFirstChiralRankPopulationInLayer_reflectUppercase observations
          | chiral descriptor =>
              simp [localizedFirstChiralRankPopulationInLayer,
                reflectUppercaseRankedEntry, reflectUppercaseOptionalLabel,
                reflectUppercaseAuxiliaryLabel,
                localizedChiralDescriptorsAtRank_reflectUppercase]

theorem localizedFirstChiralRankPopulation_reflectUppercase : ∀ layers,
    localizedFirstChiralRankPopulation (reflectUppercaseRankedLabels layers) =
      (localizedFirstChiralRankPopulation layers).map RS.swap
  | [] => rfl
  | layer :: layers => by
      simp only [reflectUppercaseRankedLabels, List.map_cons]
      unfold localizedFirstChiralRankPopulation
      rw [localizedFirstChiralRankPopulationInLayer_reflectUppercase]
      cases observed : localizedFirstChiralRankPopulationInLayer layer with
      | none =>
          simpa [observed, reflectUppercaseRankedLabels] using
            localizedFirstChiralRankPopulation_reflectUppercase layers
      | some population => simp

/-- Canonical reflection of a Rule-4b selector output.  The tied output stays in its normative
`[R,S]` order; a unique reference is mirrored. -/
def reflectSelectedRule4bReferences : List RS → List RS
  | [] => []
  | [reference] => [RS.swap reference]
  | _ => [RS.R, RS.S]

private theorem filter_swap_eq_R_length (descriptors : List RS) :
    ((descriptors.map RS.swap).filter fun descriptor => descriptor == RS.R).length =
      (descriptors.filter fun descriptor => descriptor == RS.S).length := by
  induction descriptors with
  | nil => rfl
  | cons descriptor descriptors inductionHypothesis =>
      cases descriptor <;> simp [RS.swap, inductionHypothesis]

private theorem filter_swap_eq_S_length (descriptors : List RS) :
    ((descriptors.map RS.swap).filter fun descriptor => descriptor == RS.S).length =
      (descriptors.filter fun descriptor => descriptor == RS.R).length := by
  induction descriptors with
  | nil => rfl
  | cons descriptor descriptors inductionHypothesis =>
      cases descriptor <;> simp [RS.swap, inductionHypothesis]

theorem localizedRule4bReferencesFromPopulation_reflectUppercase
    (descriptors : List RS) :
    localizedRule4bReferencesFromPopulation (descriptors.map RS.swap) =
      reflectSelectedRule4bReferences
        (localizedRule4bReferencesFromPopulation descriptors) := by
  by_cases empty : descriptors = []
  · subst descriptors
    rfl
  · have mappedNonempty : (descriptors.map RS.swap).isEmpty = false := by
      simpa [List.isEmpty_iff] using empty
    have originalNonempty : descriptors.isEmpty = false := by
      simpa [List.isEmpty_iff] using empty
    rw [localizedRule4bReferencesFromPopulation]
    simp only [mappedNonempty, Bool.false_eq_true, ↓reduceIte,
      filter_swap_eq_R_length, filter_swap_eq_S_length]
    rw [localizedRule4bReferencesFromPopulation]
    simp only [originalNonempty, Bool.false_eq_true, ↓reduceIte]
    by_cases rMajor :
        (descriptors.filter fun descriptor => descriptor == RS.S).length <
          (descriptors.filter fun descriptor => descriptor == RS.R).length
    · have notSMajor : ¬
          (descriptors.filter fun descriptor => descriptor == RS.R).length <
            (descriptors.filter fun descriptor => descriptor == RS.S).length :=
        Nat.not_lt_of_ge (Nat.le_of_lt rMajor)
      simp [rMajor, notSMajor, reflectSelectedRule4bReferences, RS.swap]
    · by_cases sMajor :
          (descriptors.filter fun descriptor => descriptor == RS.R).length <
            (descriptors.filter fun descriptor => descriptor == RS.S).length
      · simp [rMajor, sMajor, reflectSelectedRule4bReferences, RS.swap]
      · have tied :
            (descriptors.filter fun descriptor => descriptor == RS.R).length =
              (descriptors.filter fun descriptor => descriptor == RS.S).length :=
          Nat.le_antisymm (Nat.le_of_not_gt rMajor) (Nat.le_of_not_gt sMajor)
        simp [tied, reflectSelectedRule4bReferences]

theorem localizedRule4bReferencesFromRankedLabels_reflectUppercase
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    localizedRule4bReferencesFromRankedLabels (reflectUppercaseRankedLabels layers) =
      reflectSelectedRule4bReferences
        (localizedRule4bReferencesFromRankedLabels layers) := by
  unfold localizedRule4bReferencesFromRankedLabels
  rw [localizedFirstChiralRankPopulation_reflectUppercase,
    localizedRule4bReferencesFromPopulation_reflectUppercase]

theorem constitutionalRule4bReferenceCountPriority_reflectUppercase
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    constitutionalRule4bReferenceCountPriority
        (localizedRule4bReferencesFromRankedLabels
          (reflectUppercaseRankedLabels layers)) =
      constitutionalRule4bReferenceCountPriority
        (localizedRule4bReferencesFromRankedLabels layers) := by
  rw [localizedRule4bReferencesFromRankedLabels_reflectUppercase]
  unfold localizedRule4bReferencesFromRankedLabels
    localizedRule4bReferencesFromPopulation
  split
  · rfl
  · dsimp only
    split
    · rfl
    · split <;> rfl

/-! ### Independent reference-selection derivation -/

/-- Independent structural reading of all uppercase descriptors at one exact rank path. -/
def DeclarativeLocalizedChiralDescriptorsAtRank
    (rank : List Nat) :
    List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)) → List RS → Prop
  | [], descriptors => descriptors = []
  | (observedRank, label) :: observations, descriptors =>
      if observedRank = rank then
        match label with
        | some (.chiral descriptor) =>
            ∃ tail, descriptors = descriptor :: tail ∧
              DeclarativeLocalizedChiralDescriptorsAtRank rank observations tail
        | none | some (.pseudoasymmetric _) =>
            DeclarativeLocalizedChiralDescriptorsAtRank rank observations descriptors
      else DeclarativeLocalizedChiralDescriptorsAtRank rank observations descriptors

/-- Independent first-uppercase-rank reading within one hierarchy-ordered sphere. -/
def DeclarativeLocalizedFirstChiralRankPopulationInLayer :
    List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)) →
      Option (List RS) → Prop
  | [], population => population = none
  | (rank, label) :: observations, population =>
      match label with
      | some (.chiral descriptor) =>
          ∃ tail,
            DeclarativeLocalizedChiralDescriptorsAtRank rank observations tail ∧
            population = some (descriptor :: tail)
      | none | some (.pseudoasymmetric _) =>
          DeclarativeLocalizedFirstChiralRankPopulationInLayer observations population

/-- Independent first-applicable-sphere reading. -/
def DeclarativeLocalizedFirstChiralRankPopulation :
    List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) →
      List RS → Prop
  | [], descriptors => descriptors = []
  | layer :: layers, descriptors =>
      (∃ population,
        DeclarativeLocalizedFirstChiralRankPopulationInLayer layer (some population) ∧
        descriptors = population) ∨
      (DeclarativeLocalizedFirstChiralRankPopulationInLayer layer none ∧
        DeclarativeLocalizedFirstChiralRankPopulation layers descriptors)

/-- Independent majority/tie cases of P-92.5.2.1(a)--(c). -/
def DeclarativeLocalizedRule4bReferencesFromPopulation
    (descriptors references : List RS) : Prop :=
  (descriptors = [] ∧ references = []) ∨
    (descriptors ≠ [] ∧
      (((descriptors.filter fun descriptor => descriptor == RS.S).length <
          (descriptors.filter fun descriptor => descriptor == RS.R).length ∧
          references = [RS.R]) ∨
       ((descriptors.filter fun descriptor => descriptor == RS.R).length <
          (descriptors.filter fun descriptor => descriptor == RS.S).length ∧
          references = [RS.S]) ∨
       ((descriptors.filter fun descriptor => descriptor == RS.R).length =
          (descriptors.filter fun descriptor => descriptor == RS.S).length ∧
          references = [RS.R, RS.S])))

/-- Independent complete meaning of Rule-4b reference selection from ranked exact labels. -/
def DeclarativeLocalizedRule4bReferenceSelection
    (layers : List (List
      (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (references : List RS) : Prop :=
  ∃ population,
    DeclarativeLocalizedFirstChiralRankPopulation layers population ∧
    DeclarativeLocalizedRule4bReferencesFromPopulation population references

theorem localizedChiralDescriptorsAtRank_eq_iff
    (rank : List Nat) :
    ∀ observations descriptors,
      localizedChiralDescriptorsAtRank rank observations = descriptors ↔
        DeclarativeLocalizedChiralDescriptorsAtRank rank observations descriptors
  | [], descriptors => by
      simp [localizedChiralDescriptorsAtRank,
        DeclarativeLocalizedChiralDescriptorsAtRank]
  | (observedRank, label) :: observations, descriptors => by
      cases label with
      | none =>
          simp only [localizedChiralDescriptorsAtRank,
            DeclarativeLocalizedChiralDescriptorsAtRank]
          split <;> exact localizedChiralDescriptorsAtRank_eq_iff
            rank observations descriptors
      | some label =>
          cases label with
          | pseudoasymmetric pseudo =>
              simp only [localizedChiralDescriptorsAtRank,
                DeclarativeLocalizedChiralDescriptorsAtRank]
              split <;> exact localizedChiralDescriptorsAtRank_eq_iff
                rank observations descriptors
          | chiral descriptor =>
              simp only [localizedChiralDescriptorsAtRank,
                DeclarativeLocalizedChiralDescriptorsAtRank]
              split
              · constructor
                · intro computed
                  exact ⟨localizedChiralDescriptorsAtRank rank observations,
                    computed.symm,
                    (localizedChiralDescriptorsAtRank_eq_iff rank observations _).mp rfl⟩
                · rintro ⟨tail, rfl, derived⟩
                  exact congrArg (List.cons descriptor)
                    ((localizedChiralDescriptorsAtRank_eq_iff
                      rank observations tail).mpr derived)
              · exact localizedChiralDescriptorsAtRank_eq_iff
                  rank observations descriptors

theorem localizedFirstChiralRankPopulationInLayer_eq_iff :
    ∀ observations population,
      localizedFirstChiralRankPopulationInLayer observations = population ↔
        DeclarativeLocalizedFirstChiralRankPopulationInLayer observations population
  | [], population => by
      constructor <;> intro identity <;> exact identity.symm
  | (rank, label) :: observations, population => by
      cases label with
      | none =>
          exact localizedFirstChiralRankPopulationInLayer_eq_iff observations population
      | some label =>
          cases label with
          | pseudoasymmetric pseudo =>
              exact localizedFirstChiralRankPopulationInLayer_eq_iff observations population
          | chiral descriptor =>
              constructor
              · intro computed
                have identity : population = some
                    (descriptor :: localizedChiralDescriptorsAtRank rank observations) :=
                  computed.symm
                subst population
                exact ⟨localizedChiralDescriptorsAtRank rank observations,
                  (localizedChiralDescriptorsAtRank_eq_iff rank observations _).mp rfl,
                  rfl⟩
              · rintro ⟨tail, derived, rfl⟩
                have tailIdentity :=
                  (localizedChiralDescriptorsAtRank_eq_iff rank observations tail).mpr derived
                simp only [localizedFirstChiralRankPopulationInLayer,
                  Option.some.injEq, List.cons.injEq, true_and]
                exact tailIdentity

theorem localizedFirstChiralRankPopulation_eq_iff :
    ∀ layers descriptors,
      localizedFirstChiralRankPopulation layers = descriptors ↔
        DeclarativeLocalizedFirstChiralRankPopulation layers descriptors
  | [], descriptors => by
      simp [localizedFirstChiralRankPopulation,
        DeclarativeLocalizedFirstChiralRankPopulation]
  | layer :: layers, descriptors => by
      unfold localizedFirstChiralRankPopulation
        DeclarativeLocalizedFirstChiralRankPopulation
      cases observed : localizedFirstChiralRankPopulationInLayer layer with
      | none =>
          constructor
          · intro computed
            exact Or.inr
              ⟨(localizedFirstChiralRankPopulationInLayer_eq_iff layer none).mp observed,
                (localizedFirstChiralRankPopulation_eq_iff layers descriptors).mp computed⟩
          · rintro (⟨population, impossible, _⟩ | ⟨_empty, derived⟩)
            · have := (localizedFirstChiralRankPopulationInLayer_eq_iff
                layer (some population)).mpr impossible
              simp [observed] at this
            · exact (localizedFirstChiralRankPopulation_eq_iff layers descriptors).mpr derived
      | some population =>
          constructor
          · intro computed
            exact Or.inl ⟨population,
              (localizedFirstChiralRankPopulationInLayer_eq_iff
                layer (some population)).mp observed,
              computed.symm⟩
          · rintro (⟨other, derived, outputIdentity⟩ | ⟨impossible, _⟩)
            · have identity := (localizedFirstChiralRankPopulationInLayer_eq_iff
                layer (some other)).mpr derived
              rw [observed] at identity
              exact (Option.some.inj identity).trans outputIdentity.symm
            · have := (localizedFirstChiralRankPopulationInLayer_eq_iff
                layer none).mpr impossible
              simp [observed] at this

theorem localizedRule4bReferencesFromPopulation_eq_iff
    (descriptors references : List RS) :
    localizedRule4bReferencesFromPopulation descriptors = references ↔
      DeclarativeLocalizedRule4bReferencesFromPopulation descriptors references := by
  unfold localizedRule4bReferencesFromPopulation
    DeclarativeLocalizedRule4bReferencesFromPopulation
  by_cases empty : descriptors = []
  · subst descriptors
    simp
  · have notIsEmpty : descriptors.isEmpty = false := by
      simpa [List.isEmpty_iff] using empty
    simp only [notIsEmpty, Bool.false_eq_true, ↓reduceIte]
    by_cases rMajor :
        (descriptors.filter fun descriptor => descriptor == RS.S).length <
          (descriptors.filter fun descriptor => descriptor == RS.R).length
    · have notSMajor : ¬
          (descriptors.filter fun descriptor => descriptor == RS.R).length <
            (descriptors.filter fun descriptor => descriptor == RS.S).length :=
        Nat.not_lt_of_ge (Nat.le_of_lt rMajor)
      have notTied :
          (descriptors.filter fun descriptor => descriptor == RS.R).length ≠
            (descriptors.filter fun descriptor => descriptor == RS.S).length :=
        Nat.ne_of_gt rMajor
      simp [empty, rMajor, notSMajor, notTied, eq_comm]
    · by_cases sMajor :
          (descriptors.filter fun descriptor => descriptor == RS.R).length <
            (descriptors.filter fun descriptor => descriptor == RS.S).length
      · have notTied :
            (descriptors.filter fun descriptor => descriptor == RS.R).length ≠
              (descriptors.filter fun descriptor => descriptor == RS.S).length :=
          Nat.ne_of_lt sMajor
        simp [empty, rMajor, sMajor, notTied, eq_comm]
      · have tied :
            (descriptors.filter fun descriptor => descriptor == RS.R).length =
              (descriptors.filter fun descriptor => descriptor == RS.S).length :=
          Nat.le_antisymm (Nat.le_of_not_gt rMajor) (Nat.le_of_not_gt sMajor)
        simp [empty, tied, eq_comm]

/-- The executable Rule-4b selector has exactly the independent structural/majority meaning. -/
theorem localizedRule4bReferencesFromRankedLabels_eq_iff
    (layers : List (List
      (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (references : List RS) :
    localizedRule4bReferencesFromRankedLabels layers = references ↔
      DeclarativeLocalizedRule4bReferenceSelection layers references := by
  unfold localizedRule4bReferencesFromRankedLabels
    DeclarativeLocalizedRule4bReferenceSelection
  constructor
  · intro computed
    exact ⟨localizedFirstChiralRankPopulation layers,
      (localizedFirstChiralRankPopulation_eq_iff _ _).mp rfl,
      (localizedRule4bReferencesFromPopulation_eq_iff _ _).mp computed⟩
  · rintro ⟨population, populationDerived, referencesDerived⟩
    have populationIdentity :=
      (localizedFirstChiralRankPopulation_eq_iff layers population).mpr populationDerived
    rw [populationIdentity]
    exact (localizedRule4bReferencesFromPopulation_eq_iff
      population references).mpr referencesDerived

/-- Comparison used for cumulative node vectors. -/
def compareLocalizedCumulativeRule45Priority : List Nat → List Nat → Ordering :=
  List.compareLex OfficialRuleMajorKey.compareNat

/-- Under a Rule-4c reading, Rule 4a still makes every chiral source senior to every
pseudoasymmetric source, regardless of the later `r/s` component. -/
@[simp] theorem cumulativeRule4c_chiral_over_pseudoasymmetric
    (reference descriptor : RS) (pseudo : PseudoRS) :
    compareLocalizedCumulativeRule45Priority
      (localizedCumulativeRule45Priority (.rule4c reference)
        (some (.chiral descriptor)))
      (localizedCumulativeRule45Priority (.rule4c reference)
        (some (.pseudoasymmetric pseudo))) = Ordering.gt := by
  cases reference <;> cases descriptor <;> cases pseudo <;> rfl

/-- Under a Rule-4c reading, the selected Rule-4b like value is compared before Rule 4c. -/
@[simp] theorem cumulativeRule4c_rule4b_like_over_unlike
    (reference : RS) :
    compareLocalizedCumulativeRule45Priority
      (localizedCumulativeRule45Priority (.rule4c reference)
        (some (.chiral reference)))
      (localizedCumulativeRule45Priority (.rule4c reference)
        (some (.chiral (match reference with | .R => .S | .S => .R)))) = Ordering.gt := by
  cases reference <;> rfl

/-- Only after equal earlier components does the cumulative Rule-4c vector implement `r > s`. -/
@[simp] theorem cumulativeRule4c_r_over_s (reference : RS) :
    compareLocalizedCumulativeRule45Priority
      (localizedCumulativeRule45Priority (.rule4c reference)
        (some (.pseudoasymmetric .r)))
      (localizedCumulativeRule45Priority (.rule4c reference)
        (some (.pseudoasymmetric .s))) = Ordering.gt := by
  cases reference <;> rfl

/-- Rule 4c also applies when a ligand contains no uppercase chiral descriptor from which Rule 4b
could select a reference. -/
@[simp] theorem cumulativeRule4cNoReference_r_over_s :
    compareLocalizedCumulativeRule45Priority
      (localizedCumulativeRule45Priority .rule4cNoReference
        (some (.pseudoasymmetric .r)))
      (localizedCumulativeRule45Priority .rule4cNoReference
        (some (.pseudoasymmetric .s))) = Ordering.gt := by
  rfl

/-- Read one cursor coordinate only when it is a strict dependency of the descriptor target. -/
def localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel) : Option LocalizedAuxiliaryLabel :=
  if dependency : input.LocalizedDepthDependency cursor.occurrence target then
    view cursor.occurrence dependency
  else none

/-- Independent complete reading of a cursor coordinate from a restricted state view. -/
def DeclarativeLocalizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel)
    (label : Option LocalizedAuxiliaryLabel) : Prop :=
  (¬ input.LocalizedDepthDependency cursor.occurrence target ∧ label = none) ∨
    ∃ dependency : input.LocalizedDepthDependency cursor.occurrence target,
      view cursor.occurrence dependency = label

/-- Executable dependency reading is sound and complete for the independent relation. -/
theorem localizedDependencyLabel_eq_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel)
    (label : Option LocalizedAuxiliaryLabel) :
    input.localizedDependencyLabel target view cursor = label ↔
      input.DeclarativeLocalizedDependencyLabel target view cursor label := by
  unfold localizedDependencyLabel DeclarativeLocalizedDependencyLabel
  split
  · rename_i dependency
    constructor
    · intro computed
      exact Or.inr ⟨dependency, computed⟩
    · rintro (notDependency | ⟨otherDependency, observed⟩)
      · exact (notDependency.1 dependency).elim
      · have proofIdentity : otherDependency = dependency := Subsingleton.elim _ _
        subst otherDependency
        exact observed
  · rename_i notDependency
    constructor
    · intro computed
      exact Or.inl ⟨notDependency, computed.symm⟩
    · rintro (⟨_notDependency, rfl⟩ | ⟨dependency, _observed⟩)
      · rfl
      · exact (notDependency dependency).elim

/-- Recursively canonical cumulative key. -/
structure LocalizedRerootCumulativeRule45Key
    (input : CertifiedLocalizedCIPInput) where
  constitutional : OfficialRuleMajorKey input.Atom
  descriptor : List (List (OfficialSparseEntry (List Nat)))
  labels : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))
  /-- Exact labels addressed by hierarchy-equivalence rank rather than unique sibling slot.
  Equal rank paths denote nodes equivalent under the constitutional and cumulative stages already
  applied by this key. -/
  rankedLabels : List (List
    (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))

/-- Complete constitutional-then-cumulative-descriptor comparison. -/
def compareLocalizedRerootCumulativeRule45Keys
    (input : CertifiedLocalizedCIPInput) :
    input.LocalizedRerootCumulativeRule45Key →
      input.LocalizedRerootCumulativeRule45Key → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.constitutional) OfficialRuleMajorKey.compare)
    (Ordering.byKey (fun key => key.descriptor)
      (OfficialRuleMajorKey.compareSparseLayers
        compareLocalizedCumulativeRule45Priority))

/-- The cumulative recursive-key comparator is oriented and transitive. -/
theorem compareLocalizedRerootCumulativeRule45Keys_transCmp
    (input : CertifiedLocalizedCIPInput) :
    Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys := by
  letI : Std.TransCmp (@OfficialRuleMajorKey.compare input.Atom) :=
    OfficialRuleMajorKey.compare_transCmp
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  unfold compareLocalizedRerootCumulativeRule45Keys
    compareLocalizedCumulativeRule45Priority
    OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer
    OfficialRuleMajorKey.compareSparseEntry
  infer_instance

/-- Structural descending insertion of cumulative keys. -/
def insertLocalizedRerootCumulativeRule45Key
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    List input.LocalizedRerootCumulativeRule45Key →
      List input.LocalizedRerootCumulativeRule45Key
  | [] => [key]
  | head :: tail =>
      match input.compareLocalizedRerootCumulativeRule45Keys key head with
      | .lt => head :: input.insertLocalizedRerootCumulativeRule45Key key tail
      | .eq | .gt => key :: head :: tail

/-- Structural descending sort at every reroot parent. -/
def sortLocalizedRerootCumulativeRule45Keys
    (input : CertifiedLocalizedCIPInput) :
    List input.LocalizedRerootCumulativeRule45Key →
      List input.LocalizedRerootCumulativeRule45Key
  | [] => []
  | key :: keys =>
      input.insertLocalizedRerootCumulativeRule45Key key
        (input.sortLocalizedRerootCumulativeRule45Keys keys)

theorem insertLocalizedRerootCumulativeRule45Key_perm
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    ∀ keys,
      (input.insertLocalizedRerootCumulativeRule45Key key keys).Perm (key :: keys)
  | [] => List.Perm.refl _
  | head :: tail => by
      unfold insertLocalizedRerootCumulativeRule45Key
      cases comparison : input.compareLocalizedRerootCumulativeRule45Keys key head with
      | eq => exact List.Perm.refl _
      | gt => exact List.Perm.refl _
      | lt =>
          exact (List.Perm.cons head
            (input.insertLocalizedRerootCumulativeRule45Key_perm key tail)).trans
              (List.Perm.swap key head tail)

theorem sortLocalizedRerootCumulativeRule45Keys_perm
    (input : CertifiedLocalizedCIPInput) :
    ∀ keys,
      (input.sortLocalizedRerootCumulativeRule45Keys keys).Perm keys
  | [] => List.Perm.refl []
  | key :: keys =>
      (input.insertLocalizedRerootCumulativeRule45Key_perm key
        (input.sortLocalizedRerootCumulativeRule45Keys keys)).trans
          (List.Perm.cons key
            (input.sortLocalizedRerootCumulativeRule45Keys_perm keys))

/-- Descending cumulative sibling priority. -/
def LocalizedRerootCumulativeRule45KeysDescending
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootCumulativeRule45Key) : Prop :=
  keys.Pairwise fun left right =>
    input.compareLocalizedRerootCumulativeRule45Keys left right ≠ Ordering.lt

theorem insertLocalizedRerootCumulativeRule45Key_descending
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    ∀ keys,
      input.LocalizedRerootCumulativeRule45KeysDescending keys →
      input.LocalizedRerootCumulativeRule45KeysDescending
        (input.insertLocalizedRerootCumulativeRule45Key key keys)
  | [], _ => by
      simp [insertLocalizedRerootCumulativeRule45Key,
        LocalizedRerootCumulativeRule45KeysDescending]
  | head :: tail, sorted => by
      letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
        input.compareLocalizedRerootCumulativeRule45Keys_transCmp
      have headOverTail : ∀ observed ∈ tail,
          input.compareLocalizedRerootCumulativeRule45Keys head observed ≠ Ordering.lt :=
        (List.pairwise_cons.mp sorted).1
      have tailSorted : input.LocalizedRerootCumulativeRule45KeysDescending tail :=
        (List.pairwise_cons.mp sorted).2
      unfold insertLocalizedRerootCumulativeRule45Key
      cases comparison : input.compareLocalizedRerootCumulativeRule45Keys key head with
      | gt =>
          rw [LocalizedRerootCumulativeRule45KeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | eq =>
          rw [LocalizedRerootCumulativeRule45KeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | lt =>
          have insertedSorted :=
            input.insertLocalizedRerootCumulativeRule45Key_descending key tail tailSorted
          rw [LocalizedRerootCumulativeRule45KeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            have permutation :=
              input.insertLocalizedRerootCumulativeRule45Key_perm key tail
            have sourcePresent : observed ∈ key :: tail :=
              (permutation.mem_iff).mp present
            rcases List.mem_cons.mp sourcePresent with same | tailPresent
            · subst observed
              have reverse :
                  input.compareLocalizedRerootCumulativeRule45Keys head key =
                    Ordering.gt := by
                rw [Std.OrientedCmp.gt_iff_lt]
                exact comparison
              exact by simp [reverse]
            · exact headOverTail observed tailPresent
          · exact insertedSorted

theorem sortLocalizedRerootCumulativeRule45Keys_descending
    (input : CertifiedLocalizedCIPInput) :
    ∀ keys,
      input.LocalizedRerootCumulativeRule45KeysDescending
        (input.sortLocalizedRerootCumulativeRule45Keys keys)
  | [] => by
      simp [sortLocalizedRerootCumulativeRule45Keys,
        LocalizedRerootCumulativeRule45KeysDescending]
  | key :: keys =>
      input.insertLocalizedRerootCumulativeRule45Key_descending key
        (input.sortLocalizedRerootCumulativeRule45Keys keys)
        (input.sortLocalizedRerootCumulativeRule45Keys_descending keys)

/-- Maximum cumulative descriptor sphere count among child keys. -/
def localizedRerootDescriptorChildLayerCount
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) : Nat :=
  children.foldl (fun longest child => max longest child.descriptor.length) 0

/-- Merge cumulative descriptor spheres beneath their final cumulative sibling slots. -/
def mergeLocalizedRerootDescriptorChildren
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    List (List (OfficialSparseEntry (List Nat))) :=
  let count := input.localizedRerootDescriptorChildLayerCount children
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2
        (child.1.descriptor.getD depth [])

/-- Maximum exact-label sphere count among child keys. -/
def localizedRerootLabelChildLayerCount
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) : Nat :=
  children.foldl (fun longest child => max longest child.labels.length) 0

/-- Merge exact state-label observations beneath the same final cumulative sibling slots. -/
def mergeLocalizedRerootLabelChildren
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :=
  let count := input.localizedRerootLabelChildLayerCount children
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2
        (child.1.labels.getD depth [])

/-- Continue hierarchy-equivalence ranks through a descending sibling list. -/
def localizedRerootRankedChildTail
    (input : CertifiedLocalizedCIPInput)
    (previous : input.LocalizedRerootCumulativeRule45Key) (rank : Nat) :
    List input.LocalizedRerootCumulativeRule45Key →
      List (input.LocalizedRerootCumulativeRule45Key × Nat)
  | [] => []
  | child :: children =>
      let childRank :=
        if input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq then
          rank
        else rank + 1
      (child, childRank) ::
        input.localizedRerootRankedChildTail child childRank children

/-- Assign the same rank number precisely to adjacent comparator-equivalent children.  The input
is the descending child list produced by the cumulative key sort. -/
def localizedRerootRankedChildren
    (input : CertifiedLocalizedCIPInput) :
    List input.LocalizedRerootCumulativeRule45Key →
      List (input.LocalizedRerootCumulativeRule45Key × Nat)
  | [] => []
  | child :: children =>
      (child, 0) :: input.localizedRerootRankedChildTail child 0 children

/-- Maximum hierarchy-rank-addressed label sphere count among child keys. -/
def localizedRerootRankedLabelChildLayerCount
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) : Nat :=
  children.foldl (fun longest child => max longest child.rankedLabels.length) 0

/-- Merge exact labels beneath hierarchy-equivalence ranks.  Unlike `labels`, equivalent siblings
receive the same prefix, which exposes exactly the population used by P-92.5.2.1(b). -/
def mergeLocalizedRerootRankedLabelChildren
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :=
  let count := input.localizedRerootRankedLabelChildLayerCount children
  let ranked := input.localizedRerootRankedChildren children
  (List.range count).map fun depth =>
    ranked.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2
        (child.1.rankedLabels.getD depth [])

/-- Compile a complete cumulative key over the occurrence zipper. -/
noncomputable def buildLocalizedRerootCumulativeRule45Key?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Nat → input.LocalizedRerootCursor carrierFuel →
      Option input.LocalizedRerootCumulativeRule45Key
  | 0, cursor => do
      let children ← input.localizedRerootChildren? cursor
      if children = [] then
        let label := input.localizedDependencyLabel target view cursor
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
      else none
  | fuel + 1, cursor => do
      let children ← input.localizedRerootChildren? cursor
      let label := input.localizedDependencyLabel target view cursor
      if children = [] then
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
      else
        let childKeys ← children.mapM
          (input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel)
        let sorted := input.sortLocalizedRerootCumulativeRule45Keys childKeys
        some
          { constitutional := OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            descriptor :=
              [[([], localizedCumulativeRule45Priority stage label)]] ++
                input.mergeLocalizedRerootDescriptorChildren sorted
            labels := [[([], label)]] ++
              input.mergeLocalizedRerootLabelChildren sorted
            rankedLabels := [[([], label)]] ++
              input.mergeLocalizedRerootRankedLabelChildren sorted }

private theorem mapM_buildLocalizedRerootCumulativeRule45Key?_member
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List input.LocalizedRerootCumulativeRule45Key),
      cursors.mapM (input.buildLocalizedRerootCumulativeRule45Key?
        stage target view fuel) = some keys →
      ∀ key, key ∈ keys →
        ∃ cursor, cursor ∈ cursors ∧
          input.buildLocalizedRerootCumulativeRule45Key?
            stage target view fuel cursor = some key
  | [], keys, computed, key, present => by
      simp at computed
      subst keys
      simp at present
  | cursor :: cursors, keys, computed, key, present => by
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildLocalizedRerootCumulativeRule45Key?
          stage target view fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (input.buildLocalizedRerootCumulativeRule45Key?
                stage target view fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              rcases List.mem_cons.mp present with rfl | tailPresent
              · exact ⟨cursor, by simp, headComputed⟩
              · rcases input.mapM_buildLocalizedRerootCumulativeRule45Key?_member
                    stage target view cursors tail tailComputed key tailPresent with
                  ⟨source, sourcePresent, sourceComputed⟩
                exact ⟨source, List.mem_cons_of_mem cursor sourcePresent, sourceComputed⟩

/-- The constitutional component of every successful cumulative key is complete. -/
theorem buildLocalizedRerootCumulativeRule45Key?_constitutional_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel cursor key,
      input.buildLocalizedRerootCumulativeRule45Key?
        stage target view fuel cursor = some key →
      key.constitutional.complete = true
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            rfl
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            rfl
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedRerootCumulativeRule45Key?
                  stage target view fuel) with
            | none => simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
                subst key
                unfold OfficialRuleMajorKey.assemble
                rw [List.all_eq_true]
                intro childConstitutional childPresent
                rw [List.mem_map] at childPresent
                rcases childPresent with ⟨child, childSortedPresent, rfl⟩
                have childSourcePresent : child ∈ childKeys :=
                  (input.sortLocalizedRerootCumulativeRule45Keys_perm
                    childKeys).mem_iff.mp childSortedPresent
                rcases input.mapM_buildLocalizedRerootCumulativeRule45Key?_member
                    stage target view children childKeys childKeysComputed
                    child childSourcePresent with
                  ⟨childCursor, _cursorPresent, childComputed⟩
                exact input.buildLocalizedRerootCumulativeRule45Key?_constitutional_complete
                  stage target view fuel childCursor child childComputed

/-- The constitutional component of every successful cumulative key is a fresh exact projection
of its provenance-bearing source nodes. -/
theorem buildLocalizedRerootCumulativeRule45Key?_constitutional_sourceAligned
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel cursor key,
      input.buildLocalizedRerootCumulativeRule45Key?
        stage target view fuel cursor = some key →
      OfficialRuleMajorKey.SourceAligned input.moleculeGraph key.constitutional
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            exact input.moleculeGraph.officialRuleMajorRootKey_sourceAligned
              cursor.occurrence.1.node true
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            exact input.moleculeGraph.officialRuleMajorRootKey_sourceAligned
              cursor.occurrence.1.node true
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedRerootCumulativeRule45Key?
                  stage target view fuel) with
            | none => simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
                subst key
                apply OfficialRuleMajorKey.SourceAligned.assemble
                · exact input.moleculeGraph.officialRuleMajorRootKey_sourceAligned
                    cursor.occurrence.1.node false
                · intro childConstitutional childPresent
                  rw [List.mem_map] at childPresent
                  rcases childPresent with ⟨child, childSortedPresent, rfl⟩
                  have childSourcePresent : child ∈ childKeys :=
                    (input.sortLocalizedRerootCumulativeRule45Keys_perm
                      childKeys).mem_iff.mp childSortedPresent
                  rcases input.mapM_buildLocalizedRerootCumulativeRule45Key?_member
                      stage target view children childKeys childKeysComputed
                      child childSourcePresent with
                    ⟨childCursor, _cursorPresent, childComputed⟩
                  exact input.buildLocalizedRerootCumulativeRule45Key?_constitutional_sourceAligned
                    stage target view fuel childCursor child childComputed

/-! ## Independent recursive derivation -/

mutual
  /-- Proof-relevant derivation for one cumulative reroot key. -/
  inductive DeclarativeLocalizedRerootCumulativeRule45Key
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (stage : LocalizedCumulativeRule45Stage)
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → input.LocalizedRerootCursor carrierFuel →
        input.LocalizedRerootCumulativeRule45Key → Prop
    | terminal {fuel cursor children label}
        (frame : input.DeclarativeLocalizedRerootChildren cursor children)
        (empty : children = [])
        (observed : input.DeclarativeLocalizedDependencyLabel
          target view cursor label) :
        DeclarativeLocalizedRerootCumulativeRule45Key input stage target view fuel cursor
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
    | branch {fuel cursor children label childKeys sorted}
        (frame : input.DeclarativeLocalizedRerootChildren cursor children)
        (nonempty : children ≠ [])
        (observed : input.DeclarativeLocalizedDependencyLabel
          target view cursor label)
        (childDerivations : DeclarativeLocalizedRerootCumulativeRule45KeyList
          input stage target view fuel children childKeys)
        (ranking : sorted.Perm childKeys)
        (descending : input.LocalizedRerootCumulativeRule45KeysDescending sorted) :
        DeclarativeLocalizedRerootCumulativeRule45Key input stage target view
          (fuel + 1) cursor
          { constitutional := OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            descriptor :=
              [[([], localizedCumulativeRule45Priority stage label)]] ++
                input.mergeLocalizedRerootDescriptorChildren sorted
            labels := [[([], label)]] ++
              input.mergeLocalizedRerootLabelChildren sorted
            rankedLabels := [[([], label)]] ++
              input.mergeLocalizedRerootRankedLabelChildren sorted }

  /-- Pointwise derivations for every exact reroot child. -/
  inductive DeclarativeLocalizedRerootCumulativeRule45KeyList
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (stage : LocalizedCumulativeRule45Stage)
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List (input.LocalizedRerootCursor carrierFuel) →
        List input.LocalizedRerootCumulativeRule45Key → Prop
    | nil (fuel : Nat) :
        DeclarativeLocalizedRerootCumulativeRule45KeyList
          input stage target view fuel [] []
    | cons {fuel cursor cursors key keys}
        (head : DeclarativeLocalizedRerootCumulativeRule45Key
          input stage target view fuel cursor key)
        (tail : DeclarativeLocalizedRerootCumulativeRule45KeyList
          input stage target view fuel cursors keys) :
        DeclarativeLocalizedRerootCumulativeRule45KeyList
          input stage target view fuel (cursor :: cursors) (key :: keys)
end

private theorem mapM_buildLocalizedRerootCumulativeRule45Key?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (sound : ∀ cursor key,
      input.buildLocalizedRerootCumulativeRule45Key?
        stage target view fuel cursor = some key →
      input.DeclarativeLocalizedRerootCumulativeRule45Key
        stage target view fuel cursor key) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List input.LocalizedRerootCumulativeRule45Key),
      cursors.mapM (input.buildLocalizedRerootCumulativeRule45Key?
        stage target view fuel) = some keys →
      input.DeclarativeLocalizedRerootCumulativeRule45KeyList
        stage target view fuel cursors keys
  | [], keys, computed => by
      simp at computed
      subst keys
      exact DeclarativeLocalizedRerootCumulativeRule45KeyList.nil fuel
  | cursor :: cursors, keys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildLocalizedRerootCumulativeRule45Key?
          stage target view fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (input.buildLocalizedRerootCumulativeRule45Key?
                stage target view fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact DeclarativeLocalizedRerootCumulativeRule45KeyList.cons
                (sound cursor head headComputed)
                (input.mapM_buildLocalizedRerootCumulativeRule45Key?_sound
                  stage target view sound cursors tail tailComputed)

/-- Successful cumulative compilation covers the exact reroot frame, exact restricted-state
observation at every cursor, every recursive child, and a descending permutation at every parent. -/
theorem buildLocalizedRerootCumulativeRule45Key?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel cursor key,
      input.buildLocalizedRerootCumulativeRule45Key?
        stage target view fuel cursor = some key →
      input.DeclarativeLocalizedRerootCumulativeRule45Key
        stage target view fuel cursor key
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            exact DeclarativeLocalizedRerootCumulativeRule45Key.terminal
              (input.localizedRerootChildren?_sound
                cursor children childrenComputed)
              terminal
              ((input.localizedDependencyLabel_eq_iff
                target view cursor _).mp rfl)
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            exact DeclarativeLocalizedRerootCumulativeRule45Key.terminal
              (input.localizedRerootChildren?_sound
                cursor children childrenComputed)
              terminal
              ((input.localizedDependencyLabel_eq_iff
                target view cursor _).mp rfl)
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedRerootCumulativeRule45Key?
                  stage target view fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
                subst key
                exact DeclarativeLocalizedRerootCumulativeRule45Key.branch
                  (input.localizedRerootChildren?_sound
                    cursor children childrenComputed)
                  terminal
                  ((input.localizedDependencyLabel_eq_iff
                    target view cursor _).mp rfl)
                  (input.mapM_buildLocalizedRerootCumulativeRule45Key?_sound
                    stage target view
                    (fun child childKey childComputed =>
                      input.buildLocalizedRerootCumulativeRule45Key?_sound
                        stage target view fuel child childKey childComputed)
                    children childKeys childKeysComputed)
                  (input.sortLocalizedRerootCumulativeRule45Keys_perm childKeys)
                  (input.sortLocalizedRerootCumulativeRule45Keys_descending childKeys)

/-! ## Fail-closed unique-reference Rule-4c wrapper -/

/-- A unary Rule-4c key retains the prior Rule-4a hierarchy from which its unique Rule-4b
reference was selected and the independently rebuilt cumulative Rule-4c hierarchy under that
reference. -/
structure LocalizedRerootUniqueReferenceRule4cKey
    (input : CertifiedLocalizedCIPInput) where
  rule4aKey : input.LocalizedRerootCumulativeRule45Key
  reference : RS
  rule4cKey : input.LocalizedRerootCumulativeRule45Key

/-- Compile Rule 4a, select the P-92.5.2.1 reference from its hierarchy-equivalence labels, and
recompile cumulatively through Rule 4c.  Empty and two-reference populations fail closed. -/
noncomputable def buildLocalizedRerootUniqueReferenceRule4cKey?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootUniqueReferenceRule4cKey := do
  let rule4aKey ← input.buildLocalizedRerootCumulativeRule45Key?
    .rule4a target view fuel cursor
  match localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels with
  | [reference] =>
      let rule4cKey ← input.buildLocalizedRerootCumulativeRule45Key?
        (.rule4c reference) target view fuel cursor
      some { rule4aKey := rule4aKey, reference := reference, rule4cKey := rule4cKey }
  | _ => none

/-- Independent meaning of a successful unique-reference Rule-4c compilation. -/
def DeclarativeLocalizedRerootUniqueReferenceRule4cKey
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootUniqueReferenceRule4cKey) : Prop :=
  input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor key.rule4aKey ∧
    DeclarativeLocalizedRule4bReferenceSelection
      key.rule4aKey.rankedLabels [key.reference] ∧
    input.DeclarativeLocalizedRerootCumulativeRule45Key
      (.rule4c key.reference) target view fuel cursor key.rule4cKey

/-- Success proves both recursive hierarchy derivations and the independent unique-reference
selection relation. -/
theorem buildLocalizedRerootUniqueReferenceRule4cKey?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootUniqueReferenceRule4cKey)
    (computed : input.buildLocalizedRerootUniqueReferenceRule4cKey?
      target view fuel cursor = some key) :
    input.DeclarativeLocalizedRerootUniqueReferenceRule4cKey
      target view fuel cursor key := by
  unfold buildLocalizedRerootUniqueReferenceRule4cKey? at computed
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45Key?
      .rule4a target view fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      cases referencesComputed :
          localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels with
      | nil => simp [rule4aComputed, referencesComputed] at computed
      | cons reference references =>
          cases references with
          | nil =>
              cases rule4cComputed :
                  input.buildLocalizedRerootCumulativeRule45Key?
                    (.rule4c reference) target view fuel cursor with
              | none =>
                  simp [rule4aComputed, referencesComputed, rule4cComputed] at computed
              | some rule4cKey =>
                  simp [rule4aComputed, referencesComputed, rule4cComputed] at computed
                  subst key
                  exact ⟨
                    input.buildLocalizedRerootCumulativeRule45Key?_sound
                      .rule4a target view fuel cursor rule4aKey rule4aComputed,
                    (localizedRule4bReferencesFromRankedLabels_eq_iff
                      rule4aKey.rankedLabels [reference]).mp referencesComputed,
                    input.buildLocalizedRerootCumulativeRule45Key?_sound
                      (.rule4c reference) target view fuel cursor
                      rule4cKey rule4cComputed⟩
          | cons second rest =>
              simp [rule4aComputed, referencesComputed] at computed

/-- The two-reference case is not silently coerced to either unary reading. -/
theorem buildLocalizedRerootUniqueReferenceRule4cKey?_eq_none_of_twoReferences
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (rule4aKey : input.LocalizedRerootCumulativeRule45Key)
    (rule4aComputed : input.buildLocalizedRerootCumulativeRule45Key?
      .rule4a target view fuel cursor = some rule4aKey)
    (twoReferences : localizedRule4bReferencesFromRankedLabels
      rule4aKey.rankedLabels = [RS.R, RS.S]) :
    input.buildLocalizedRerootUniqueReferenceRule4cKey?
      target view fuel cursor = none := by
  simp [buildLocalizedRerootUniqueReferenceRule4cKey?, rule4aComputed, twoReferences]

/-- Compare the complete recursively re-ranked Rule-4c projections after the caller has already
established a tie under the constitutional rules and Rule 4a.  Each ligand carries its own proved
unique Rule-4b reference. -/
def compareLocalizedRerootUniqueReferenceRule4cKeys
    (input : CertifiedLocalizedCIPInput) :
    input.LocalizedRerootUniqueReferenceRule4cKey →
      input.LocalizedRerootUniqueReferenceRule4cKey → Ordering :=
  Ordering.byKey (fun key => key.rule4cKey.descriptor)
    (OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority)

/-- The unique-reference Rule-4c projection comparator is oriented and transitive. -/
theorem compareLocalizedRerootUniqueReferenceRule4cKeys_transCmp
    (input : CertifiedLocalizedCIPInput) :
    Std.TransCmp input.compareLocalizedRerootUniqueReferenceRule4cKeys := by
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  unfold compareLocalizedRerootUniqueReferenceRule4cKeys
    compareLocalizedCumulativeRule45Priority
    OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer
    OfficialRuleMajorKey.compareSparseEntry
  infer_instance

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
