import TetraStereo.OneCenter.IUPACPeriodicGroupValenceConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# General finite Lewis endpoint inventory, including vacancies

The closed-valence module fixes `vacancies = 0`, which makes the position and electron equations
functional.  Here we remove that premise.  The same independent equations can then have no
solution, exactly one solution, or multiple solutions.  We enumerate the complete finite solution
set, return an inventory only in the unique case, and prove that refusal means precisely
impossibility or mathematical underdetermination.  No chemical state is guessed to break a tie.
-/

/-- General localized main-group Lewis meaning.  Unlike the closed-valence relation, vacancies
participate in the two-position equation and are not fixed in advance. -/
def MainGroupLewisGeneralEndpointInventory
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) : Prop :=
  source.CanonicalAromaticCanonicalRule3EndpointElectronicInventory
      endpoint partner inventory ∧
    ∃ valenceElectrons,
      mainGroupValenceElectronCount? (source.molecule.atoms.get endpoint).element =
          some valenceElectrons ∧
        source.MainGroupLewisElectronBalance endpoint valenceElectrons inventory

/-- The previous closed-valence relation is exactly the general relation plus zero vacancies. -/
theorem mainGroupClosedValenceLewisEndpointInventory_iff_general_and_noVacancy
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) :
    source.MainGroupClosedValenceLewisEndpointInventory endpoint partner inventory ↔
      source.MainGroupLewisGeneralEndpointInventory endpoint partner inventory ∧
        inventory.vacancies = 0 := by
  constructor
  · rintro ⟨canonical, noVacancy, electronBalance⟩
    exact ⟨⟨canonical, electronBalance⟩, noVacancy⟩
  · rintro ⟨⟨canonical, electronBalance⟩, noVacancy⟩
    exact ⟨canonical, noVacancy, electronBalance⟩

/-- All 27 possible assignments to the three unknown two-position counts.  The radical count is
copied from the semantic atom and the canonical equation removes the impossible candidates. -/
def mainGroupLewisGeneralEndpointInventoryCandidates
    (unpairedElectrons : ℕ) :
    List AromaticCanonicalRule3EndpointElectronicInventory :=
  (List.range 3).flatMap fun implicitProtia =>
    (List.range 3).flatMap fun lonePairs =>
      (List.range 3).map fun vacancies =>
        { implicitProtia := implicitProtia
          lonePairs := lonePairs
          vacancies := vacancies
          unpairedElectronPositions := unpairedElectrons }

/-- Every general Lewis solution occurs in the 27-candidate enumeration. -/
theorem mem_mainGroupLewisGeneralEndpointInventoryCandidates_of_lewis
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory)
    (lewis : source.MainGroupLewisGeneralEndpointInventory endpoint partner inventory) :
    inventory ∈ mainGroupLewisGeneralEndpointInventoryCandidates
      (source.molecule.atoms.get endpoint).unpairedElectrons := by
  rcases inventory with ⟨implicitProtia, lonePairs, vacancies, radicals⟩
  rcases lewis with ⟨canonical, _electronBalance⟩
  unfold CanonicalAromaticCanonicalRule3EndpointElectronicInventory at canonical
  unfold AromaticCanonicalRule3EndpointElectronicInventory.totalNonrepresentedPositions at canonical
  simp only at canonical
  apply List.mem_flatMap.mpr
  refine ⟨implicitProtia, List.mem_range.mpr (by omega), ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨lonePairs, List.mem_range.mpr (by omega), ?_⟩
  apply List.mem_map.mpr
  refine ⟨vacancies, List.mem_range.mpr (by omega), ?_⟩
  simp only [canonical.2]

/-- Complete duplicate-free finite solution set of the general Lewis equations. -/
noncomputable def mainGroupLewisGeneralEndpointSolutions
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    List AromaticCanonicalRule3EndpointElectronicInventory := by
  classical
  exact ((mainGroupLewisGeneralEndpointInventoryCandidates
    (source.molecule.atoms.get endpoint).unpairedElectrons).filter fun inventory =>
      decide (source.MainGroupLewisGeneralEndpointInventory
        endpoint partner inventory)).dedup

@[simp] theorem mem_mainGroupLewisGeneralEndpointSolutions_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) :
    inventory ∈ source.mainGroupLewisGeneralEndpointSolutions endpoint partner ↔
      source.MainGroupLewisGeneralEndpointInventory endpoint partner inventory := by
  classical
  unfold mainGroupLewisGeneralEndpointSolutions
  rw [List.mem_dedup, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro lewis
    exact ⟨source.mem_mainGroupLewisGeneralEndpointInventoryCandidates_of_lewis
      endpoint partner inventory lewis, lewis⟩

theorem mainGroupLewisGeneralEndpointSolutions_nodup
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    (source.mainGroupLewisGeneralEndpointSolutions endpoint partner).Nodup := by
  classical
  exact List.nodup_dedup _

/-- Return a general inventory only when the complete solution set is a singleton. -/
noncomputable def mainGroupLewisUniqueGeneralEndpointInventory?
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    Option AromaticCanonicalRule3EndpointElectronicInventory :=
  match source.mainGroupLewisGeneralEndpointSolutions endpoint partner with
  | [inventory] => some inventory
  | _ => none

/-- Exact positive meaning: the returned inventory satisfies the general equations and is their
only solution. -/
theorem mainGroupLewisUniqueGeneralEndpointInventory?_eq_some_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) :
    source.mainGroupLewisUniqueGeneralEndpointInventory? endpoint partner = some inventory ↔
      source.MainGroupLewisGeneralEndpointInventory endpoint partner inventory ∧
        ∀ other,
          source.MainGroupLewisGeneralEndpointInventory endpoint partner other →
            other = inventory := by
  classical
  constructor
  · intro computed
    unfold mainGroupLewisUniqueGeneralEndpointInventory? at computed
    cases solutionsObserved : source.mainGroupLewisGeneralEndpointSolutions endpoint partner with
    | nil => simp [solutionsObserved] at computed
    | cons first rest =>
        cases rest with
        | nil =>
            simp [solutionsObserved] at computed
            subst first
            constructor
            · apply (source.mem_mainGroupLewisGeneralEndpointSolutions_iff
                endpoint partner inventory).mp
              simp [solutionsObserved]
            · intro other otherLewis
              have otherPresent :=
                (source.mem_mainGroupLewisGeneralEndpointSolutions_iff
                  endpoint partner other).mpr otherLewis
              simpa [solutionsObserved] using otherPresent
        | cons second tail => simp [solutionsObserved] at computed
  · rintro ⟨lewis, unique⟩
    have inventoryPresent :=
      (source.mem_mainGroupLewisGeneralEndpointSolutions_iff
        endpoint partner inventory).mpr lewis
    cases solutionsObserved : source.mainGroupLewisGeneralEndpointSolutions endpoint partner with
    | nil => simp [solutionsObserved] at inventoryPresent
    | cons first rest =>
        have firstLewis : source.MainGroupLewisGeneralEndpointInventory endpoint partner first :=
          (source.mem_mainGroupLewisGeneralEndpointSolutions_iff
            endpoint partner first).mp (by simp [solutionsObserved])
        have firstIdentity := unique first firstLewis
        subst first
        cases rest with
        | nil => simp [mainGroupLewisUniqueGeneralEndpointInventory?, solutionsObserved]
        | cons second tail =>
            have secondLewis : source.MainGroupLewisGeneralEndpointInventory
                endpoint partner second :=
              (source.mem_mainGroupLewisGeneralEndpointSolutions_iff
                endpoint partner second).mp (by simp [solutionsObserved])
            have secondIdentity := unique second secondLewis
            subst second
            have nodup := source.mainGroupLewisGeneralEndpointSolutions_nodup endpoint partner
            rw [solutionsObserved] at nodup
            simp at nodup

/-- Exact positive refusal: the equations have no solution or have at least two distinct
solutions. -/
def MainGroupLewisGeneralEndpointRefusal
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) : Prop :=
  (¬ ∃ inventory,
    source.MainGroupLewisGeneralEndpointInventory endpoint partner inventory) ∨
  (∃ left right,
    source.MainGroupLewisGeneralEndpointInventory endpoint partner left ∧
      source.MainGroupLewisGeneralEndpointInventory endpoint partner right ∧
        left ≠ right)

/-- The unique general classifier refuses exactly impossibility or underdetermination. -/
theorem mainGroupLewisUniqueGeneralEndpointInventory?_eq_none_iff_refusal
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    source.mainGroupLewisUniqueGeneralEndpointInventory? endpoint partner = none ↔
      source.MainGroupLewisGeneralEndpointRefusal endpoint partner := by
  classical
  constructor
  · intro absent
    by_cases existsSolution : ∃ inventory,
        source.MainGroupLewisGeneralEndpointInventory endpoint partner inventory
    · rcases existsSolution with ⟨inventory, lewis⟩
      right
      by_contra noAmbiguity
      push_neg at noAmbiguity
      have unique : ∀ other,
          source.MainGroupLewisGeneralEndpointInventory endpoint partner other →
            other = inventory := by
        intro other otherLewis
        by_contra different
        exact different (noAmbiguity inventory other lewis otherLewis).symm
      have present :=
        (source.mainGroupLewisUniqueGeneralEndpointInventory?_eq_some_iff
          endpoint partner inventory).mpr ⟨lewis, unique⟩
      rw [absent] at present
      contradiction
    · exact Or.inl existsSolution
  · intro refusal
    cases observed : source.mainGroupLewisUniqueGeneralEndpointInventory? endpoint partner with
    | none => rfl
    | some inventory =>
        obtain ⟨lewis, unique⟩ :=
          (source.mainGroupLewisUniqueGeneralEndpointInventory?_eq_some_iff
            endpoint partner inventory).mp observed
        rcases refusal with impossible | ambiguous
        · exact False.elim (impossible ⟨inventory, lewis⟩)
        · rcases ambiguous with ⟨left, right, leftLewis, rightLewis, different⟩
          exact False.elim (different ((unique left leftLewis).trans
            (unique right rightLewis).symm))

/-- Mathematical exhaustiveness of the generalized ledger, independent of the executable
classifier: every endpoint is impossible, uniquely determined, or genuinely ambiguous. -/
theorem mainGroupLewisGeneralEndpoint_trichotomy
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    (¬ ∃ inventory,
      source.MainGroupLewisGeneralEndpointInventory endpoint partner inventory) ∨
    (∃ inventory,
      source.MainGroupLewisGeneralEndpointInventory endpoint partner inventory ∧
        ∀ other,
          source.MainGroupLewisGeneralEndpointInventory endpoint partner other →
            other = inventory) ∨
    (∃ left right,
      source.MainGroupLewisGeneralEndpointInventory endpoint partner left ∧
        source.MainGroupLewisGeneralEndpointInventory endpoint partner right ∧
          left ≠ right) := by
  classical
  by_cases existsSolution : ∃ inventory,
      source.MainGroupLewisGeneralEndpointInventory endpoint partner inventory
  · rcases existsSolution with ⟨inventory, lewis⟩
    by_cases unique : ∀ other,
        source.MainGroupLewisGeneralEndpointInventory endpoint partner other →
          other = inventory
    · exact Or.inr (Or.inl ⟨inventory, lewis, unique⟩)
    · push_neg at unique
      rcases unique with ⟨other, otherLewis, different⟩
      exact Or.inr (Or.inr ⟨inventory, other, lewis, otherLewis, different.symm⟩)
  · exact Or.inl existsSolution

/-- The two-hydrogen solution of the only potentially ambiguous two-position/electron-count
system. -/
def mainGroupLewisHydrogenPairInventory :
    AromaticCanonicalRule3EndpointElectronicInventory where
  implicitProtia := 2
  lonePairs := 0
  vacancies := 0
  unpairedElectronPositions := 0

/-- The electron-isoelectronic alternative: one lone pair and one vacant position. -/
def mainGroupLewisLonePairVacancyInventory :
    AromaticCanonicalRule3EndpointElectronicInventory where
  implicitProtia := 0
  lonePairs := 1
  vacancies := 1
  unpairedElectronPositions := 0

private theorem exactCollision_of_twoPositionElectronEquations
    (leftImplicit leftLonePairs leftVacancies leftRadicals : ℕ)
    (rightImplicit rightLonePairs rightVacancies rightRadicals : ℕ)
    (representedPositions : ℕ)
    (leftPosition :
      representedPositions +
        (leftImplicit + leftLonePairs + leftVacancies + leftRadicals) = 2)
    (rightPosition :
      representedPositions +
        (rightImplicit + rightLonePairs + rightVacancies + rightRadicals) = 2)
    (electronCountsEqual :
      leftImplicit + 2 * leftLonePairs + leftRadicals =
        rightImplicit + 2 * rightLonePairs + rightRadicals)
    (radicalsEqual : leftRadicals = rightRadicals)
    (fieldDifferent :
      leftImplicit ≠ rightImplicit ∨ leftLonePairs ≠ rightLonePairs ∨
        leftVacancies ≠ rightVacancies ∨ leftRadicals ≠ rightRadicals) :
    ((leftImplicit = 2 ∧ leftLonePairs = 0 ∧ leftVacancies = 0 ∧ leftRadicals = 0) ∧
      (rightImplicit = 0 ∧ rightLonePairs = 1 ∧ rightVacancies = 1 ∧
        rightRadicals = 0)) ∨
    ((rightImplicit = 2 ∧ rightLonePairs = 0 ∧ rightVacancies = 0 ∧ rightRadicals = 0) ∧
      (leftImplicit = 0 ∧ leftLonePairs = 1 ∧ leftVacancies = 1 ∧
        leftRadicals = 0)) := by
  subst rightRadicals
  have leftLonePairsAtMostTwo : leftLonePairs ≤ 2 := by omega
  have rightLonePairsAtMostTwo : rightLonePairs ≤ 2 := by omega
  interval_cases leftLonePairs <;> interval_cases rightLonePairs <;>
    rcases fieldDifferent with different | different | different | different <;> omega

/-- Any two distinct solutions have the exact two-H and lone-pair-plus-vacancy shapes, in one
order or the other.  This is stronger than merely proving that the canonical collision exists:
it excludes a third inventory from the same position/electron system. -/
theorem mainGroupLewisGeneralEndpoint_distinct_solutions_exact_shapes
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (left right : AromaticCanonicalRule3EndpointElectronicInventory)
    (leftLewis :
      source.MainGroupLewisGeneralEndpointInventory endpoint partner left)
    (rightLewis :
      source.MainGroupLewisGeneralEndpointInventory endpoint partner right)
    (different : left ≠ right) :
    (left = mainGroupLewisHydrogenPairInventory ∧
      right = mainGroupLewisLonePairVacancyInventory) ∨
    (right = mainGroupLewisHydrogenPairInventory ∧
      left = mainGroupLewisLonePairVacancyInventory) := by
  rcases leftLewis with ⟨leftCanonical,
    leftValence, leftElement, leftBalance⟩
  rcases rightLewis with ⟨rightCanonical,
    rightValence, rightElement, rightBalance⟩
  have valenceEqual : leftValence = rightValence := by
    rw [leftElement] at rightElement
    exact Option.some.inj rightElement
  subst rightValence
  rcases left with ⟨leftImplicit, leftLonePairs, leftVacancies, leftRadicals⟩
  rcases right with ⟨rightImplicit, rightLonePairs, rightVacancies, rightRadicals⟩
  unfold CanonicalAromaticCanonicalRule3EndpointElectronicInventory at leftCanonical rightCanonical
  unfold AromaticCanonicalRule3EndpointElectronicInventory.totalNonrepresentedPositions at leftCanonical rightCanonical
  unfold MainGroupLewisElectronBalance at leftBalance rightBalance
  simp only at leftCanonical rightCanonical leftBalance rightBalance
  have fieldDifferent :
      leftImplicit ≠ rightImplicit ∨ leftLonePairs ≠ rightLonePairs ∨
        leftVacancies ≠ rightVacancies ∨ leftRadicals ≠ rightRadicals := by
    by_contra allEqual
    push_neg at allEqual
    rcases allEqual with ⟨implicitEqual, lonePairEqual, vacancyEqual, radicalEqual⟩
    exact different (by simp [implicitEqual, lonePairEqual, vacancyEqual, radicalEqual])
  have electronCountsEqual :
      leftImplicit + 2 * leftLonePairs + leftRadicals =
        rightImplicit + 2 * rightLonePairs + rightRadicals := by
    omega
  have radicalsEqual : leftRadicals = rightRadicals :=
    leftCanonical.2.trans rightCanonical.2.symm
  have shapes := exactCollision_of_twoPositionElectronEquations
    leftImplicit leftLonePairs leftVacancies leftRadicals
    rightImplicit rightLonePairs rightVacancies rightRadicals
    (source.aromaticCanonicalRule3Substituents endpoint partner).length
    leftCanonical.1 rightCanonical.1 electronCountsEqual radicalsEqual fieldDifferent
  rcases shapes with ⟨leftShape, rightShape⟩ | ⟨rightShape, leftShape⟩
  · rcases leftShape with ⟨rfl, rfl, rfl, rfl⟩
    rcases rightShape with ⟨rfl, rfl, rfl, rfl⟩
    exact Or.inl ⟨rfl, rfl⟩
  · rcases rightShape with ⟨rfl, rfl, rfl, rfl⟩
    rcases leftShape with ⟨rfl, rfl, rfl, rfl⟩
    exact Or.inr ⟨rfl, rfl⟩

/-- Exact algebraic ambiguity classification.  The position and electron equations can have two
distinct solutions if and only if both the two-hydrogen inventory and the lone-pair-plus-vacancy
inventory solve them.  Thus no other vacancy ambiguity is hidden by the classifier. -/
theorem mainGroupLewisGeneralEndpoint_ambiguous_iff_hydrogenPair_and_lonePairVacancy
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    (∃ left right,
      source.MainGroupLewisGeneralEndpointInventory endpoint partner left ∧
        source.MainGroupLewisGeneralEndpointInventory endpoint partner right ∧
          left ≠ right) ↔
      source.MainGroupLewisGeneralEndpointInventory endpoint partner
          mainGroupLewisHydrogenPairInventory ∧
        source.MainGroupLewisGeneralEndpointInventory endpoint partner
          mainGroupLewisLonePairVacancyInventory := by
  constructor
  · rintro ⟨left, right, leftLewis, rightLewis, different⟩
    rcases leftLewis with ⟨leftCanonical,
      leftValence, leftElement, leftBalance⟩
    rcases rightLewis with ⟨rightCanonical,
      rightValence, rightElement, rightBalance⟩
    have valenceEqual : leftValence = rightValence := by
      rw [leftElement] at rightElement
      exact Option.some.inj rightElement
    subst rightValence
    rcases left with ⟨leftImplicit, leftLonePairs, leftVacancies, leftRadicals⟩
    rcases right with ⟨rightImplicit, rightLonePairs, rightVacancies, rightRadicals⟩
    unfold CanonicalAromaticCanonicalRule3EndpointElectronicInventory at leftCanonical rightCanonical
    unfold AromaticCanonicalRule3EndpointElectronicInventory.totalNonrepresentedPositions at leftCanonical rightCanonical
    unfold MainGroupLewisElectronBalance at leftBalance rightBalance
    simp only at leftCanonical rightCanonical leftBalance rightBalance
    have fieldDifferent :
        leftImplicit ≠ rightImplicit ∨ leftLonePairs ≠ rightLonePairs ∨
          leftVacancies ≠ rightVacancies ∨ leftRadicals ≠ rightRadicals := by
      by_contra allEqual
      push_neg at allEqual
      rcases allEqual with ⟨implicitEqual, lonePairEqual, vacancyEqual, radicalEqual⟩
      exact different (by simp [implicitEqual, lonePairEqual, vacancyEqual, radicalEqual])
    have electronCountsEqual :
        leftImplicit + 2 * leftLonePairs + leftRadicals =
          rightImplicit + 2 * rightLonePairs + rightRadicals := by
      omega
    have radicalsEqual : leftRadicals = rightRadicals :=
      leftCanonical.2.trans rightCanonical.2.symm
    have shapes := exactCollision_of_twoPositionElectronEquations
      leftImplicit leftLonePairs leftVacancies leftRadicals
      rightImplicit rightLonePairs rightVacancies rightRadicals
      (source.aromaticCanonicalRule3Substituents endpoint partner).length
      leftCanonical.1 rightCanonical.1 electronCountsEqual radicalsEqual fieldDifferent
    rcases shapes with ⟨leftShape, rightShape⟩ | ⟨rightShape, leftShape⟩
    · rcases leftShape with ⟨rfl, rfl, rfl, rfl⟩
      rcases rightShape with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨⟨leftCanonical, leftValence, leftElement, leftBalance⟩,
        ⟨rightCanonical, leftValence, rightElement, rightBalance⟩⟩
    · rcases rightShape with ⟨rfl, rfl, rfl, rfl⟩
      rcases leftShape with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨⟨rightCanonical, leftValence, rightElement, rightBalance⟩,
        ⟨leftCanonical, leftValence, leftElement, leftBalance⟩⟩
  · rintro ⟨hydrogenPair, lonePairVacancy⟩
    exact ⟨mainGroupLewisHydrogenPairInventory,
      mainGroupLewisLonePairVacancyInventory,
      hydrogenPair, lonePairVacancy, by decide⟩

/-- Fully explicit refusal normal form: no general Lewis solution exists, or the unique possible
isoelectronic collision does. -/
theorem mainGroupLewisUniqueGeneralEndpointInventory?_eq_none_iff_noSolution_or_exactCollision
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    source.mainGroupLewisUniqueGeneralEndpointInventory? endpoint partner = none ↔
      (¬ ∃ inventory,
        source.MainGroupLewisGeneralEndpointInventory endpoint partner inventory) ∨
      (source.MainGroupLewisGeneralEndpointInventory endpoint partner
          mainGroupLewisHydrogenPairInventory ∧
        source.MainGroupLewisGeneralEndpointInventory endpoint partner
          mainGroupLewisLonePairVacancyInventory) := by
  rw [source.mainGroupLewisUniqueGeneralEndpointInventory?_eq_none_iff_refusal]
  unfold MainGroupLewisGeneralEndpointRefusal
  rw [source.mainGroupLewisGeneralEndpoint_ambiguous_iff_hydrogenPair_and_lonePairVacancy]

/-- The general relation, like the closed-valence specialization, is independent of which retained
double-bond partner is erased at a fixed atom. -/
theorem mainGroupLewisGeneralEndpointInventory_partner_independent
    (source : AuthoritativeChemicalInput)
    (atom firstPartner secondPartner : source.AromaticCanonicalAtom)
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory)
    (firstDirected :
      source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint atom firstPartner)
    (firstLewis : source.MainGroupLewisGeneralEndpointInventory atom firstPartner inventory)
    (secondDirected :
      source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint atom secondPartner) :
    source.MainGroupLewisGeneralEndpointInventory atom secondPartner inventory := by
  rcases firstLewis with ⟨firstCanonical, electronLedger⟩
  have firstOrdinary := source.aromaticCanonicalOrdinaryDoubleBond_of_directedEndpoint firstDirected
  have secondOrdinary := source.aromaticCanonicalOrdinaryDoubleBond_of_directedEndpoint secondDirected
  have firstPresent : firstPartner ∈ source.aromaticCanonicalNeighborFinset atom :=
    (source.mem_aromaticCanonicalNeighborFinset_iff atom firstPartner).mpr firstOrdinary.1
  have secondPresent : secondPartner ∈ source.aromaticCanonicalNeighborFinset atom :=
    (source.mem_aromaticCanonicalNeighborFinset_iff atom secondPartner).mpr secondOrdinary.1
  have representedLengthEqual :
      (source.aromaticCanonicalRule3Substituents atom firstPartner).length =
        (source.aromaticCanonicalRule3Substituents atom secondPartner).length := by
    simp [aromaticCanonicalRule3Substituents,
      Finset.card_erase_of_mem firstPresent,
      Finset.card_erase_of_mem secondPresent]
  refine ⟨?_, electronLedger⟩
  unfold CanonicalAromaticCanonicalRule3EndpointElectronicInventory at firstCanonical ⊢
  exact ⟨by simpa [representedLengthEqual] using firstCanonical.1, firstCanonical.2⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
