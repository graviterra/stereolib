import TetraStereo.OneCenter.LocalizedOccurrenceCarrier

set_option autoImplicit false

/-!
# Executable finite carrier and strict dependency list for localized CIP occurrences

`TetraStereo.OneCenter.LocalizedOccurrenceCarrier` defines the proof-relevant subtype
`LocalizedCIPOccurrence input fuel` of occurrence frames lying in the molecule-wide enumeration
`localizedOccurrences input fuel`, and proves that the enumeration is extensionally exact, duplicate
free, and uniformly depth-graded, with a well-founded strict dependency relation
`LocalizedDepthDependency`.

This module turns that body of theory into a small, *computable* list surface:

* `localizedOccurrenceCarrier` is the executable list of all proof-relevant occurrences, obtained by
  attaching the membership certificates to the underlying enumeration;
* `localizedDependencyList target` is the executable list of occurrences on which `target` strictly
  depends, obtained by filtering the carrier with the decidable predicate
  `LocalizedDepthDependency · target`.

The main results are the standard list facts one expects of such a surface (completeness,
duplicate-freeness, projection back to the raw enumeration, exact membership characterizations,
sublist/coverage and length bounds) plus the strict causal measure
`source.remaining < target.remaining` for every listed dependency, and a `DecidablePred` instance
for the declarative occurrence relation derived from the existing membership equivalence.

Everything here is a thin wrapper: no new mathematical content is introduced, and the executable
definitions use only `List.attach`, `List.filter` and `decide`, hence no axiom of choice.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## The executable occurrence carrier -/

/-- Computable list of the proof-relevant occurrences of `input` at expansion bound `fuel`.  This is
the underlying enumeration `localizedOccurrences` with its membership certificates attached, so the
result is a list in the same subtype `LocalizedCIPOccurrence input fuel`. -/
def localizedOccurrenceCarrier (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    List (input.LocalizedCIPOccurrence fuel) :=
  (input.localizedOccurrences fuel).attach

/-- Enumeration completeness: every proof-relevant occurrence appears in the executable carrier. -/
theorem localizedOccurrenceCarrier_complete
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence ∈ input.localizedOccurrenceCarrier fuel :=
  List.mem_attach (input.localizedOccurrences fuel) occurrence

/-- The executable carrier is duplicate free, inherited from the enumeration. -/
theorem localizedOccurrenceCarrier_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.localizedOccurrenceCarrier fuel).Nodup :=
  List.Nodup.attach (input.localizedOccurrences_nodup fuel)

/-- Projecting the carrier back to frames recovers the underlying enumeration exactly. -/
theorem localizedOccurrenceCarrier_map_val
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.localizedOccurrenceCarrier fuel).map Subtype.val =
      input.localizedOccurrences fuel :=
  List.attach_map_subtype_val (input.localizedOccurrences fuel)

/-- Carrier length agrees with the length of the underlying occurrence enumeration. -/
theorem localizedOccurrenceCarrier_length
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.localizedOccurrenceCarrier fuel).length =
      (input.localizedOccurrences fuel).length :=
  List.length_attach

/-- Carrier membership of a proof-relevant occurrence is exactly the declarative occurrence
relation on its underlying frame. -/
theorem localizedOccurrenceCarrier_mem_iff_declarative
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence ∈ input.localizedOccurrenceCarrier fuel ↔
      input.DeclarativeLocalizedOccurrence fuel occurrence.1 :=
  ⟨fun _ => (input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2,
    fun _ => input.localizedOccurrenceCarrier_complete fuel occurrence⟩

/-! ## The executable strict dependency list -/

/-- Computable list of occurrences on which `target` strictly depends, obtained by filtering the
carrier with the decidable strict-depth predicate `LocalizedDepthDependency · target`. -/
def localizedDependencyList (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (target : input.LocalizedCIPOccurrence fuel) :
    List (input.LocalizedCIPOccurrence fuel) :=
  (input.localizedOccurrenceCarrier fuel).filter fun source =>
    decide (input.LocalizedDepthDependency source target)

/-- Exactness: the dependency list consists of precisely the carrier entries that strictly depend on
the target. -/
theorem mem_localizedDependencyList_iff_carrier
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (target source : input.LocalizedCIPOccurrence fuel) :
    source ∈ input.localizedDependencyList fuel target ↔
      source ∈ input.localizedOccurrenceCarrier fuel ∧
        input.LocalizedDepthDependency source target := by
  unfold localizedDependencyList
  rw [List.mem_filter]
  constructor
  · rintro ⟨carried, decided⟩
    exact ⟨carried, by simpa only [decide_eq_true_iff] using decided⟩
  · rintro ⟨carried, dependency⟩
    exact ⟨carried, by simpa only [decide_eq_true_iff] using dependency⟩

/-- Membership in the dependency list is exactly the strict depth dependency. -/
theorem mem_localizedDependencyList_iff
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (target source : input.LocalizedCIPOccurrence fuel) :
    source ∈ input.localizedDependencyList fuel target ↔
      input.LocalizedDepthDependency source target := by
  rw [input.mem_localizedDependencyList_iff_carrier fuel target source]
  exact ⟨fun h => h.2,
    fun h => ⟨input.localizedOccurrenceCarrier_complete fuel source, h⟩⟩

/-- The dependency list is duplicate free, inherited from the carrier. -/
theorem localizedDependencyList_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (target : input.LocalizedCIPOccurrence fuel) :
    (input.localizedDependencyList fuel target).Nodup := by
  rw [localizedDependencyList]
  exact List.Nodup.filter _ (input.localizedOccurrenceCarrier_nodup fuel)

/-- The dependency list is a sublist of the carrier. -/
theorem localizedDependencyList_sublist_carrier
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (target : input.LocalizedCIPOccurrence fuel) :
    (input.localizedDependencyList fuel target).Sublist
      (input.localizedOccurrenceCarrier fuel) := by
  rw [localizedDependencyList]
  exact List.filter_sublist

/-- Coverage: every listed dependency is a carrier entry. -/
theorem localizedDependencyList_mem_carrier
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (target source : input.LocalizedCIPOccurrence fuel)
    (present : source ∈ input.localizedDependencyList fuel target) :
    source ∈ input.localizedOccurrenceCarrier fuel :=
  ((input.mem_localizedDependencyList_iff_carrier fuel target source).mp present).1

/-- Coverage in subset form. -/
theorem localizedDependencyList_subset_carrier
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (target : input.LocalizedCIPOccurrence fuel) :
    (input.localizedDependencyList fuel target) ⊆
      (input.localizedOccurrenceCarrier fuel) :=
  (input.localizedDependencyList_sublist_carrier fuel target).subset

/-- Length bound against the carrier. -/
theorem localizedDependencyList_length_le_carrier
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (target : input.LocalizedCIPOccurrence fuel) :
    (input.localizedDependencyList fuel target).length ≤
      (input.localizedOccurrenceCarrier fuel).length :=
  (input.localizedDependencyList_sublist_carrier fuel target).length_le

/-- Length bound against the raw occurrence enumeration. -/
theorem localizedDependencyList_length_le_occurrences
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (target : input.LocalizedCIPOccurrence fuel) :
    (input.localizedDependencyList fuel target).length ≤
      (input.localizedOccurrences fuel).length := by
  rw [← input.localizedOccurrenceCarrier_length fuel]
  exact input.localizedDependencyList_length_le_carrier fuel target

/-! ## The strict causal measure -/

/-- Every carried occurrence has remaining expansion depth at most `fuel + 1`, the exact bound
forced by the common depth grading. -/
theorem localizedCIPOccurrence_remaining_le_fuel_add_one
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence.1.remaining ≤ fuel + 1 := by
  have grade := input.localizedCIPOccurrence_depthGrade occurrence
  omega

/-- A permitted dependency strictly lowers the remaining expansion depth (hypothesis form). -/
theorem localizedDependencyList_remaining_lt
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    {target source : input.LocalizedCIPOccurrence fuel}
    (dependency : input.LocalizedDepthDependency source target) :
    source.1.remaining < target.1.remaining :=
  input.localizedDepthDependency_remaining_lt dependency

/-- A permitted dependency strictly lowers the remaining expansion depth (membership form). -/
theorem mem_localizedDependencyList_remaining_lt
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (target source : input.LocalizedCIPOccurrence fuel)
    (present : source ∈ input.localizedDependencyList fuel target) :
    source.1.remaining < target.1.remaining :=
  input.localizedDepthDependency_remaining_lt
    ((input.mem_localizedDependencyList_iff fuel target source).mp present)

/-- Every listed dependency lies below the same final root as its target. -/
theorem mem_localizedDependencyList_root_eq
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (target source : input.LocalizedCIPOccurrence fuel)
    (present : source ∈ input.localizedDependencyList fuel target) :
    source.1.root = target.1.root :=
  ((input.mem_localizedDependencyList_iff fuel target source).mp present).1

/-- Strict dependency is irreflexive, so a target is never listed as its own dependency. -/
theorem target_notMem_localizedDependencyList
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (target : input.LocalizedCIPOccurrence fuel) :
    target ∉ input.localizedDependencyList fuel target := by
  intro present
  exact input.localizedDepthDependency_irrefl target
    ((input.mem_localizedDependencyList_iff fuel target target).mp present)

/-! ## Constructive decidability from the membership equivalence -/

/-- The declarative occurrence relation is decidable, transported along the existing membership
equivalence `mem_localizedOccurrences_iff` from the computable membership test on the underlying
occurrence enumeration.  The equivalence is used only as a proof-irrelevant transport, so the
resulting decision procedure is a plain `List` membership test. -/
instance declarativeLocalizedOccurrenceDecidable
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    DecidablePred (input.DeclarativeLocalizedOccurrence fuel) := fun occurrence =>
  decidable_of_iff (occurrence ∈ input.localizedOccurrences fuel)
    (input.mem_localizedOccurrences_iff fuel occurrence)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
