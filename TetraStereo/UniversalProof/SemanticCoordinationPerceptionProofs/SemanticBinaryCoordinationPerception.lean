import TetraStereo.OneCenter.AuthoritativeChemicalInput

set_option autoImplicit false

namespace TetraStereo.UniversalProof
namespace SemanticCoordinationPerceptionProofs

open TetraStereo.OneCenter





























/-- Literal finite Boolean equality of two Bools from equality of their `= true` propositions. -/
theorem bool_eq_of_iff (first second : Bool) (same : first = true ↔ second = true) :
    first = second := by
  cases first <;> cases second <;> simp_all

/-- The independent undirected binary coordination-neighbour relation.  `center` and `donor` are
distinct atoms joined by one actual `coordinate` interaction whose participant list is exactly the
unordered pair `{center, donor}` (recorded in either order). -/
def BinaryCoordinateDonor (source : AuthoritativeChemicalInput) (center donor : ℕ) : Prop :=
  center ≠ donor ∧
    ∃ interaction ∈ source.molecule.interactions,
      interaction.kind = SemanticInteractionKind.coordinate ∧
        (interaction.participants = [center, donor] ∨
          interaction.participants = [donor, center])

/-- The `∃ i ∈ l, …` scan of the relation is symmetric in its two endpoints: recording the same
binary coordination in the opposite order denotes the same neighbour. -/
theorem BinaryCoordinateDonor.symm {source : AuthoritativeChemicalInput} {center donor : ℕ}
    (relation : BinaryCoordinateDonor source center donor) :
    BinaryCoordinateDonor source donor center := by
  rcases relation with ⟨distinct, interaction, member, kindEq, order⟩
  rcases order with forward | reverse
  · exact ⟨distinct.symm, interaction, member, kindEq, Or.inr forward⟩
  · exact ⟨distinct.symm, interaction, member, kindEq, Or.inl reverse⟩

/-- Literal finite interaction-list scan for the undirected binary coordination neighbour. -/
def binaryCoordinateDonor? (source : AuthoritativeChemicalInput) (center donor : ℕ) : Bool :=
  decide (center ≠ donor) &&
    source.molecule.interactions.any fun interaction =>
      decide (interaction.kind = SemanticInteractionKind.coordinate ∧
        (interaction.participants = [center, donor] ∨
          interaction.participants = [donor, center]))

/-- The literal finite scan realizes exactly the independent relation. -/
@[simp] theorem binaryCoordinateDonor?_eq_true_iff (source : AuthoritativeChemicalInput)
    (center donor : ℕ) :
    binaryCoordinateDonor? source center donor = true ↔
      BinaryCoordinateDonor source center donor := by
  simp only [binaryCoordinateDonor?, BinaryCoordinateDonor, Bool.and_eq_true,
    decide_eq_true_eq, List.any_eq_true]

/-- The scan is symmetric in its endpoints. -/
theorem binaryCoordinateDonor?_comm (source : AuthoritativeChemicalInput) (center donor : ℕ) :
    binaryCoordinateDonor? source center donor = binaryCoordinateDonor? source donor center := by
  apply bool_eq_of_iff
  simp only [binaryCoordinateDonor?_eq_true_iff]
  exact ⟨BinaryCoordinateDonor.symm, BinaryCoordinateDonor.symm⟩

/-! ## Canonical donor list -/

/-- The canonical donor list at a centre: the bounded atom universe filtered by the relation.  No
externally given neighbour list participates. -/
def canonicalDonors (source : AuthoritativeChemicalInput) (center : ℕ) : List ℕ :=
  (List.range source.molecule.atomCount).filter fun donor =>
    binaryCoordinateDonor? source center donor

/-- Membership in the canonical donor list is exactly a bound together with the relation. -/
theorem mem_canonicalDonors_iff (source : AuthoritativeChemicalInput) (center donor : ℕ) :
    donor ∈ canonicalDonors source center ↔
      donor < source.molecule.atomCount ∧ BinaryCoordinateDonor source center donor := by
  simp only [canonicalDonors, List.mem_filter, List.mem_range, binaryCoordinateDonor?_eq_true_iff]

/-- Every canonical donor lies in the parsed atom range. -/
theorem canonicalDonors_bounded (source : AuthoritativeChemicalInput) (center donor : ℕ)
    (member : donor ∈ canonicalDonors source center) :
    donor < source.molecule.atomCount :=
  ((mem_canonicalDonors_iff source center donor).mp member).1

/-- The canonical donor list is duplicate-free: the same neighbour recorded twice, or in both
orders, still occupies one site. -/
theorem canonicalDonors_nodup (source : AuthoritativeChemicalInput) (center : ℕ) :
    (canonicalDonors source center).Nodup :=
  List.nodup_range.filter _

/-! ## Interaction-list invariance (permutations, duplicated records) -/

/-- Replace the semantic interaction list while keeping every other source field. -/
def withInteractions (source : AuthoritativeChemicalInput)
    (interactions : List SemanticInteraction) : AuthoritativeChemicalInput :=
  { source with molecule := { source.molecule with interactions := interactions } }

@[simp] theorem withInteractions_molecule_interactions (source : AuthoritativeChemicalInput)
    (interactions : List SemanticInteraction) :
    (withInteractions source interactions).molecule.interactions = interactions :=
  rfl

@[simp] theorem withInteractions_atomCount (source : AuthoritativeChemicalInput)
    (interactions : List SemanticInteraction) :
    (withInteractions source interactions).molecule.atomCount = source.molecule.atomCount :=
  rfl

@[simp] theorem withInteractions_spatial? (source : AuthoritativeChemicalInput)
    (interactions : List SemanticInteraction) :
    (withInteractions source interactions).spatial? = source.spatial? :=
  rfl

/-- The neighbour scan depends on the interaction list only through its membership. -/
theorem binaryCoordinateDonor?_congr (left right : AuthoritativeChemicalInput)
    (memberIff : ∀ interaction,
      interaction ∈ left.molecule.interactions ↔ interaction ∈ right.molecule.interactions)
    (center donor : ℕ) :
    binaryCoordinateDonor? left center donor = binaryCoordinateDonor? right center donor := by
  apply bool_eq_of_iff
  simp only [binaryCoordinateDonor?_eq_true_iff, BinaryCoordinateDonor]
  constructor
  · rintro ⟨distinct, interaction, member, kind, order⟩
    exact ⟨distinct, interaction, (memberIff interaction).mp member, kind, order⟩
  · rintro ⟨distinct, interaction, member, kind, order⟩
    exact ⟨distinct, interaction, (memberIff interaction).mpr member, kind, order⟩

/-- Permuting the interaction list preserves the neighbour scan pointwise. -/
theorem binaryCoordinateDonor?_withInteractions_perm (source : AuthoritativeChemicalInput)
    (interactions : List SemanticInteraction)
    (perm : source.molecule.interactions.Perm interactions) (center donor : ℕ) :
    binaryCoordinateDonor? (withInteractions source interactions) center donor =
      binaryCoordinateDonor? source center donor :=
  binaryCoordinateDonor?_congr (withInteractions source interactions) source
    (fun interaction => by
      rw [withInteractions_molecule_interactions]
      exact perm.mem_iff.symm)
    center donor

/-- If two sources share the atom count and the neighbour scan agrees pointwise, their canonical
donor lists agree. -/
theorem canonicalDonors_congr (left right : AuthoritativeChemicalInput) (center : ℕ)
    (atomCounts : left.molecule.atomCount = right.molecule.atomCount)
    (predicates : ∀ donor, binaryCoordinateDonor? left center donor =
      binaryCoordinateDonor? right center donor) :
    canonicalDonors left center = canonicalDonors right center := by
  unfold canonicalDonors
  rw [atomCounts]
  apply List.filter_congr
  intro donor _
  exact predicates donor

/-- Permuting the interaction list preserves the canonical donor list. -/
theorem perm_canonicalDonors (source : AuthoritativeChemicalInput)
    (interactions : List SemanticInteraction)
    (perm : source.molecule.interactions.Perm interactions) (center : ℕ) :
    canonicalDonors (withInteractions source interactions) center =
      canonicalDonors source center :=
  canonicalDonors_congr (withInteractions source interactions) source center
    (withInteractions_atomCount source interactions)
    (fun donor =>
      binaryCoordinateDonor?_withInteractions_perm source interactions perm center donor)

/-- Duplicating the full interaction list cannot duplicate or change a canonical donor site. -/
theorem duplicate_canonicalDonors (source : AuthoritativeChemicalInput) (center : ℕ) :
    canonicalDonors (withInteractions source
      (source.molecule.interactions ++ source.molecule.interactions)) center =
      canonicalDonors source center := by
  apply canonicalDonors_congr (withInteractions source
    (source.molecule.interactions ++ source.molecule.interactions)) source center rfl
  intro donor
  apply binaryCoordinateDonor?_congr
  intro interaction
  simp only [withInteractions_molecule_interactions, List.mem_append, or_self]

/-! ## Bounded centre scan at arbitrary coordination number -/

/-- Centres of the bounded atom universe having exactly `coordinationNumber` canonical neighbours. -/
def canonicalCoordinationCenters (source : AuthoritativeChemicalInput)
    (coordinationNumber : ℕ) : List ℕ :=
  (List.range source.molecule.atomCount).filter fun center =>
    (canonicalDonors source center).length == coordinationNumber

/-- Membership in the centre scan is exactly a bound together with the exact canonical-neighbour
count. -/
theorem mem_canonicalCoordinationCenters_iff (source : AuthoritativeChemicalInput)
    (coordinationNumber center : ℕ) :
    center ∈ canonicalCoordinationCenters source coordinationNumber ↔
      center < source.molecule.atomCount ∧
        (canonicalDonors source center).length = coordinationNumber := by
  simp only [canonicalCoordinationCenters, List.mem_filter, List.mem_range, beq_iff_eq]

/-- The centre scan is duplicate-free. -/
theorem canonicalCoordinationCenters_nodup (source : AuthoritativeChemicalInput)
    (coordinationNumber : ℕ) :
    (canonicalCoordinationCenters source coordinationNumber).Nodup :=
  List.nodup_range.filter _

/-- Every scheduled centre occurs exactly once: the bounded universe contributes each atom at most
once and the filter preserves that. -/
theorem canonicalCoordinationCenters_count_one (source : AuthoritativeChemicalInput)
    (coordinationNumber center : ℕ)
    (member : center ∈ canonicalCoordinationCenters source coordinationNumber) :
    (canonicalCoordinationCenters source coordinationNumber).count center = 1 :=
  List.count_eq_one_of_mem (canonicalCoordinationCenters_nodup source coordinationNumber) member

/-- Permuting the interaction list preserves centre membership at every coordination number. -/
theorem perm_mem_canonicalCoordinationCenters (source : AuthoritativeChemicalInput)
    (interactions : List SemanticInteraction)
    (perm : source.molecule.interactions.Perm interactions)
    (coordinationNumber center : ℕ) :
    center ∈ canonicalCoordinationCenters (withInteractions source interactions) coordinationNumber ↔
      center ∈ canonicalCoordinationCenters source coordinationNumber := by
  simp only [mem_canonicalCoordinationCenters_iff,
    perm_canonicalDonors source interactions perm center, withInteractions_atomCount]

/-! ## Indexed records -/

/-- One scheduled coordination centre together with its canonical donor list. -/
structure SemanticCoordinationRecord where
  center : ℕ
  donors : List ℕ
  deriving DecidableEq, Repr

/-- The indexed records at one coordination number. -/
def canonicalCoordinationRecords (source : AuthoritativeChemicalInput)
    (coordinationNumber : ℕ) : List SemanticCoordinationRecord :=
  (canonicalCoordinationCenters source coordinationNumber).map fun center =>
    { center := center, donors := canonicalDonors source center }

/-- The indexed record list is duplicate-free. -/
theorem canonicalCoordinationRecords_nodup (source : AuthoritativeChemicalInput)
    (coordinationNumber : ℕ) :
    (canonicalCoordinationRecords source coordinationNumber).Nodup := by
  unfold canonicalCoordinationRecords
  apply List.Nodup.map
  · intro first second same
    exact congrArg SemanticCoordinationRecord.center same
  · exact canonicalCoordinationCenters_nodup source coordinationNumber

end SemanticCoordinationPerceptionProofs
end TetraStereo.UniversalProof
