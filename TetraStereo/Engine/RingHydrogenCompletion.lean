import TetraStereo.OneCenter.ExplicitHydrogens
import TetraStereo.OneCenter.AuthoritativeLocalizedTetrahedralDescriptor
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Materialize missing hydrogen vertices while retaining original atom indices, bonds,
written neighbour order and coordinates. Added positions carry a physical hand only when
three explicit neighbour positions determine it. Convention frames for equivalent hydrogens
supply geometry without distinguishing their chemical identities. -/
namespace TetraStereo.Engine.RingHydrogenCompletion

open OneCenter

/-! ## Exact vector arithmetic -/

abbrev Point := CartesianPoint3

def vadd (a b : Point) : Point := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def vsub (a b : Point) : Point := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

def vcross (a b : Point) : Point :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩

def vdot (a b : Point) : ℚ := a.x * b.x + a.y * b.y + a.z * b.z

def normSq (a : Point) : ℚ := vdot a a

def zeroVector : Point := ⟨0, 0, 0⟩

/-- Reflection through the plane `x = 0`; the same map as `CartesianPoint3.reflectX`. -/
def mirrorX (p : Point) : Point := ⟨-p.x, p.y, p.z⟩

/-- A deterministic vector perpendicular to `a`, nonzero when `a` is nonzero. It is not covariant
and is used only where the choice is a rotation of identical hydrogens about an axis. -/
def perp (a : Point) : Point :=
  if vcross a ⟨1, 0, 0⟩ = zeroVector then
    if vcross a ⟨0, 1, 0⟩ = zeroVector then ⟨1, 0, 0⟩ else vcross a ⟨0, 1, 0⟩
  else vcross a ⟨1, 0, 0⟩

/-! ## One missing hydrogen -/

/-- The centre plus, for every neighbour, the vector from that neighbour to the centre. -/
def opposite (c : Point) (ps : List Point) : Point :=
  ps.foldl (fun h p => vadd h (vsub c p)) c

/-- Keep the inferred position in the affine span of the existing bond vectors. In
particular two explicit ligands cannot determine a pyramidal phosphorus hand. -/
def single (c : Point) (ps : List Point) : Point := opposite c ps

theorem single_three (c p1 p2 p3 : Point) :
    single c [p1, p2, p3] = opposite c [p1, p2, p3] := rfl

/-- The frame of an inferred hydrogen is four times the frame of the centre against its three
neighbours: the same sign, and zero exactly when the centre is coplanar with them. -/
theorem orientedVolume_opposite (c p1 p2 p3 : Point) :
    CartesianPoint3.orientedVolume p1 p2 p3 (opposite c [p1, p2, p3]) =
      4 * CartesianPoint3.orientedVolume p1 p2 p3 c := by
  simp only [CartesianPoint3.orientedVolume, opposite, List.foldl_cons, List.foldl_nil, vadd, vsub]
  ring

theorem orientedVolume_single_three (c p1 p2 p3 : Point) :
    CartesianPoint3.orientedVolume p1 p2 p3 (single c [p1, p2, p3]) =
      4 * CartesianPoint3.orientedVolume p1 p2 p3 c := by
  rw [single_three]
  exact orientedVolume_opposite c p1 p2 p3

/-- Reflecting the centre and its three neighbours reflects the inferred hydrogen. -/
theorem opposite_mirrorX (c p1 p2 p3 : Point) :
    opposite (mirrorX c) [mirrorX p1, mirrorX p2, mirrorX p3] =
      mirrorX (opposite c [p1, p2, p3]) := by
  simp only [opposite, List.foldl_cons, List.foldl_nil, vadd, vsub, mirrorX]
  congr 1; ring

/-! ## Two or more missing hydrogens: convention frames -/

def pairPlus (c p1 p2 : Point) : Point :=
  vadd (vsub (vsub c (vsub p1 c)) (vsub p2 c)) (vcross (vsub p1 c) (vsub p2 c))

def pairMinus (c p1 p2 : Point) : Point :=
  vsub (vsub (vsub c (vsub p1 c)) (vsub p2 c)) (vcross (vsub p1 c) (vsub p2 c))

/-- Generic `CH2`: the labelled frame is six times a square, whatever the geometry. -/
theorem orientedVolume_pair (c p1 p2 : Point) :
    CartesianPoint3.orientedVolume p1 p2 (pairPlus c p1 p2) (pairMinus c p1 p2) =
      6 * normSq (vcross (vsub p1 c) (vsub p2 c)) := by
  simp only [CartesianPoint3.orientedVolume, pairPlus, pairMinus, normSq, vdot, vadd, vsub, vcross]
  ring

def skewFirst (c a u : Point) : Point := vsub (vadd c u) (vcross a u)

def skewSecond (c a u : Point) : Point := vadd (vadd c u) (vcross a u)

/-- `CH2` whose two neighbours are collinear with the centre. The second term vanishes in that
case, because the cross product of the two neighbour vectors is zero. -/
theorem orientedVolume_skew (c p1 p2 u : Point) :
    CartesianPoint3.orientedVolume p1 p2
        (skewFirst c (vsub p1 p2) u) (skewSecond c (vsub p1 p2) u) =
      2 * normSq (vcross (vsub p1 p2) u) -
        2 * vdot (vcross (vsub p1 c) (vsub p2 c)) (vcross (vsub p1 p2) u) := by
  simp only [CartesianPoint3.orientedVolume, skewFirst, skewSecond, normSq, vdot, vadd, vsub,
    vcross]
  ring

def tripodFirst (c p u : Point) : Point := vadd (vsub c (vsub p c)) u

def tripodSecond (c p u : Point) : Point := vadd (vsub c (vsub p c)) (vcross (vsub p c) u)

def tripodThird (c p u : Point) : Point :=
  vsub (vsub c (vsub p c)) (vadd u (vcross (vsub p c) u))

/-- Methyl: the labelled frame is six times a square for every auxiliary direction `u`. -/
theorem orientedVolume_tripod (c p u : Point) :
    CartesianPoint3.orientedVolume p (tripodFirst c p u) (tripodSecond c p u)
        (tripodThird c p u) =
      6 * normSq (vcross (vsub p c) u) := by
  simp only [CartesianPoint3.orientedVolume, tripodFirst, tripodSecond, tripodThird, normSq, vdot,
    vadd, vsub, vcross]
  ring

/-- Isolated `XH4`: a fixed tetrahedron about the centre. -/
theorem orientedVolume_tetra (c : Point) :
    CartesianPoint3.orientedVolume (vadd c ⟨1, 1, 1⟩) (vadd c ⟨1, -1, -1⟩)
        (vadd c ⟨-1, 1, -1⟩) (vadd c ⟨-1, -1, 1⟩) = 16 := by
  simp only [CartesianPoint3.orientedVolume, vadd]
  ring

def pair (c p1 p2 : Point) : List Point :=
  if vcross (vsub p1 c) (vsub p2 c) = zeroVector then
    if vsub p1 p2 = zeroVector then [vadd c ⟨1, 0, 0⟩, vadd c ⟨0, 1, 0⟩]
    else
      [skewFirst c (vsub p1 p2) (perp (vsub p1 p2)), skewSecond c (vsub p1 p2) (perp (vsub p1 p2))]
  else [pairPlus c p1 p2, pairMinus c p1 p2]

def tripod (c p : Point) : List Point :=
  if vsub p c = zeroVector then [vadd c ⟨0, 1, 0⟩, vadd c ⟨1, 0, 0⟩, vadd c ⟨0, 0, 1⟩]
  else
    [tripodFirst c p (perp (vsub p c)), tripodSecond c p (perp (vsub p c)),
      tripodThird c p (perp (vsub p c))]

def tetra (c : Point) : List Point :=
  [vadd c ⟨1, 1, 1⟩, vadd c ⟨1, -1, -1⟩, vadd c ⟨-1, 1, -1⟩, vadd c ⟨-1, -1, 1⟩]

/-- Designed placements, by number of missing hydrogens and existing neighbour positions. -/
def place (c : Point) (ps : List Point) (k : Nat) : List Point :=
  match k, ps with
  | 1, _ => [single c ps]
  | 2, [p1, p2] => pair c p1 p2
  | 2, [p] =>
      [vadd (vsub c (vsub p c)) (perp (vsub p c)), vsub (vsub c (vsub p c)) (perp (vsub p c))]
  | 3, [p] => tripod c p
  | 4, [] => tetra c
  | _, _ => []

/-- Distinct points on a moment curve for combinations without a tetrahedral frame. -/
def fallback (c : Point) (k : Nat) : List Point :=
  (List.range k).map (fun (t : Nat) =>
    vadd c ⟨(t : ℚ) + 1, ((t : ℚ) + 1) * ((t : ℚ) + 1),
      ((t : ℚ) + 1) * ((t : ℚ) + 1) * ((t : ℚ) + 1)⟩)

/-- Exactly `k` positions for `k` missing hydrogens. -/
def placed (c : Point) (ps : List Point) (k : Nat) : List Point :=
  (place c ps k ++ fallback c k).take k

theorem placed_length (c : Point) (ps : List Point) (k : Nat) : (placed c ps k).length = k := by
  have f : (fallback c k).length = k := by
    unfold fallback
    rw [List.length_map, List.length_range]
  unfold placed
  rw [List.length_take, List.length_append, f]
  exact Nat.min_eq_left (Nat.le_add_left k _)



/-- Everything about an atom except its inline hydrogen policy. -/
def heavyCore (a : AtomSpec) : AtomSpec := { a with explicitHydrogens? := none }

/-- A hydrogen vertex never receives hydrogens. -/
def closeAtom (a : AtomSpec) : AtomSpec :=
  if a.element = Element.H then { a with explicitHydrogens? := some 0 } else a

def closeHydrogenVertices (m : RawMolecule) : RawMolecule :=
  { m with atoms := m.atoms.map closeAtom }

/-- Number of hydrogens that are attached to atom `i` but are not graph vertices. -/
def missing (m : RawMolecule) (i : Nat) : Nat := (closeHydrogenVertices m).hydrogenCountAt i

/-- Atoms that receive hydrogens, ascending, each with its count. -/
def plan (m : RawMolecule) : List (Nat × Nat) :=
  (List.range m.atomCount).filterMap fun i =>
    if missing m i = 0 then none else some (i, missing m i)

/-- Parent of each added hydrogen, in the order of the new atom indices. -/
def addedParents (m : RawMolecule) : List Nat :=
  (plan m).flatMap fun e => List.replicate e.2 e.1

/-- Existing neighbours in ascending index, independent of the written order. -/
def neighbors (m : RawMolecule) (i : Nat) : List Nat :=
  (List.range m.atomCount).filter fun j => decide (j ∈ m.writtenNeighbors i)

/-- Untagged hydrogen and explicit protium have the same ordinary hydrogen identity. -/
def ordinaryHydrogenVertex (m : RawMolecule) (j : Nat) : Bool :=
  match m.atoms[j]? with
  | some a => decide (a.element = Element.H ∧ (a.isotope? = none ∨ a.isotope? = some 1) ∧
      a.charge = 0 ∧ (m.writtenNeighbors j).length = 1)
  | none => false

/-- A normal can complete a coplanar frame when an existing equivalent hydrogen makes
its orientation chemically irrelevant. It never resolves an undetermined CH hand. -/
def equivalentHydrogenPosition (c p1 p2 p3 : Point) : Point :=
  let normal := vcross (vsub p2 p1) (vsub p3 p1)
  vadd (opposite c [p1,p2,p3]) normal

/-- The normal contributes a squared area, so a noncollinear equivalent-H frame is
nondegenerate even when its original three positions and centre are coplanar. -/
theorem orientedVolume_equivalentHydrogenPosition (c p1 p2 p3 : Point) :
    CartesianPoint3.orientedVolume p1 p2 p3 (equivalentHydrogenPosition c p1 p2 p3) =
      4 * CartesianPoint3.orientedVolume p1 p2 p3 c -
        normSq (vcross (vsub p2 p1) (vsub p3 p1)) := by
  simp only [CartesianPoint3.orientedVolume, equivalentHydrogenPosition, opposite,
    List.foldl_cons, List.foldl_nil, normSq, vdot, vadd, vsub, vcross]
  ring

def placeAt? (m : RawMolecule) (xyz : SpatialConfiguration) (e : Nat × Nat) :
    Option (List Point) := do
  let c ← xyz.positions[e.1]?
  let ps ← (neighbors m e.1).mapM fun j => xyz.positions[j]?
  if e.2 = 1 && (m.writtenNeighbors e.1).any (ordinaryHydrogenVertex m) then
    match ps with
    | [p1,p2,p3] =>
      if CartesianPoint3.orientedVolume p1 p2 p3 c = 0 then
        pure [equivalentHydrogenPosition c p1 p2 p3]
      else pure (placed c ps e.2)
    | _ => pure (placed c ps e.2)
  else pure (placed c ps e.2)

def addedPositions? (m : RawMolecule) (xyz : SpatialConfiguration) : Option (List Point) :=
  ((plan m).mapM (placeAt? m xyz)).map List.flatten

/-! ## Executed certificate -/

def originalBond (m : RawMolecule) (b : RawBond) : Bool :=
  decide (b.source < m.atomCount ∧ b.target < m.atomCount)

def addedBond (m : RawMolecule) (b : RawBond) : Bool :=
  decide (b.kind = ParsedBondKind.single ∧ b.source < m.atomCount ∧ m.atomCount ≤ b.target)

/-- Everything `prepare?` guarantees about its output, as one decidable statement. -/
def Certified (m : RawMolecule) (xyz : SpatialConfiguration) (out : RawMolecule)
    (pos : SpatialConfiguration) : Prop :=
  m.stereochemicalAdmissible? = true ∧
  xyz.positions.length = m.atomCount ∧
  out.stereochemicalAdmissible? = true ∧
  m.atomCount ≤ out.atomCount ∧
  pos.positions.length = out.atomCount ∧
  pos.positions.take m.atomCount = xyz.positions ∧
  (out.atoms.take m.atomCount).map heavyCore = m.atoms.map heavyCore ∧
  out.atoms.drop m.atomCount =
    List.replicate (out.atomCount - m.atomCount) (AtomSpec.aliphatic Element.H) ∧
  out.bonds.filter (originalBond m) = m.bonds ∧
  (out.bonds.filter fun b => !originalBond m b).all (addedBond m) = true ∧
  (List.range m.atomCount).all (fun i =>
    decide ((out.writtenNeighbors i).filter (fun j => decide (j < m.atomCount)) =
      m.writtenNeighbors i)) = true ∧
  (List.range (out.atomCount - m.atomCount)).map
      (fun t => out.writtenNeighbors (m.atomCount + t)) =
    (addedParents m).map (fun p => [p]) ∧
  (addedParents m).all (fun p => decide (p < m.atomCount)) = true ∧
  out.introductionPredecessors = m.introductionPredecessors

instance (m : RawMolecule) (xyz : SpatialConfiguration) (out : RawMolecule)
    (pos : SpatialConfiguration) : Decidable (Certified m xyz out pos) := by
  unfold Certified
  infer_instance

/-! ## Construction -/

def candidate? (m : RawMolecule) (xyz : SpatialConfiguration) :
    Option (RawMolecule × SpatialConfiguration) :=
  if (plan m).isEmpty then some (m, xyz)
  else
    (addedPositions? m xyz).map fun extra =>
      ((closeHydrogenVertices m).withExplicitHydrogens,
        ({ positions := xyz.positions ++ extra } : SpatialConfiguration))

def gate (m : RawMolecule) (xyz : SpatialConfiguration)
    (r : RawMolecule × SpatialConfiguration) : Option (RawMolecule × SpatialConfiguration) :=
  if Certified m xyz r.1 r.2 then some r else none

/-- Complete the molecular graph and check its structural provenance. -/
def complete? (m : RawMolecule) (xyz : SpatialConfiguration) :
    Option (RawMolecule × SpatialConfiguration) :=
  (candidate? m xyz).bind (gate m xyz)

/-- Public hydrogen completion; coordinate admission is checked downstream. -/
abbrev prepare? := complete?

/-! ## Reading the result -/

theorem gate_eq_some {m : RawMolecule} {xyz : SpatialConfiguration}
    {r r' : RawMolecule × SpatialConfiguration} (h : gate m xyz r = some r') :
    r' = r ∧ Certified m xyz r.1 r.2 := by
  unfold gate at h
  by_cases c : Certified m xyz r.1 r.2
  · rw [if_pos c] at h
    exact ⟨(Option.some.inj h).symm, c⟩
  · rw [if_neg c] at h
    cases h

theorem complete?_certified {m : RawMolecule} {xyz : SpatialConfiguration}
    {r : RawMolecule × SpatialConfiguration} (h : complete? m xyz = some r) :
    Certified m xyz r.1 r.2 := by
  unfold complete? at h
  cases c : candidate? m xyz with
  | none =>
      rw [c] at h
      exact absurd h (by simp)
  | some r0 =>
      rw [c] at h
      have passed : gate m xyz r0 = some r := h
      obtain ⟨same, certified⟩ := gate_eq_some passed
      rw [same]
      exact certified

theorem prepare?_eq_some_iff (m : RawMolecule) (xyz : SpatialConfiguration)
    (r : RawMolecule × SpatialConfiguration) :
    prepare? m xyz = some r ↔ complete? m xyz = some r := Iff.rfl

theorem prepare?_certified {m : RawMolecule} {xyz : SpatialConfiguration}
    {r : RawMolecule × SpatialConfiguration} (h : prepare? m xyz = some r) :
    Certified m xyz r.1 r.2 := complete?_certified h

/-- A molecule with nothing missing is returned unchanged, given its own certificate. -/
theorem prepare?_of_complete (m : RawMolecule) (xyz : SpatialConfiguration)
    (none_missing : plan m = []) (ok : Certified m xyz m xyz) :
    prepare? m xyz = some (m, xyz) := by
  have c : candidate? m xyz = some (m, xyz) := by simp [candidate?, none_missing]
  unfold prepare? complete?
  rw [c]
  show gate m xyz (m, xyz) = some (m, xyz)
  unfold gate
  exact if_pos ok

theorem listGet?_eq_getElem? {α : Type} (list : List α) (index : Nat) :
    listGet? list index = list[index]? := by
  induction list generalizing index with
  | nil => cases index <;> rfl
  | cons head tail ih =>
      cases index with
      | zero => rfl
      | succ index => exact ih index

theorem atomAt?_eq_getElem? (m : RawMolecule) (i : Nat) : m.atomAt? i = m.atoms[i]? := by
  unfold RawMolecule.atomAt?
  exact listGet?_eq_getElem? m.atoms i

namespace Certified

variable {m out : RawMolecule} {xyz pos : SpatialConfiguration}

theorem input_admissible (h : Certified m xyz out pos) : m.StereochemicalAdmissible :=
  m.stereochemicalAdmissible?_eq_true_iff.mp h.1

theorem input_positions (h : Certified m xyz out pos) : xyz.positions.length = m.atomCount :=
  h.2.1

theorem output_admissible (h : Certified m xyz out pos) : out.StereochemicalAdmissible :=
  out.stereochemicalAdmissible?_eq_true_iff.mp h.2.2.1

theorem atomCount_le (h : Certified m xyz out pos) : m.atomCount ≤ out.atomCount :=
  h.2.2.2.1

theorem positions_length (h : Certified m xyz out pos) : pos.positions.length = out.atomCount :=
  h.2.2.2.2.1

theorem positions_take (h : Certified m xyz out pos) :
    pos.positions.take m.atomCount = xyz.positions :=
  h.2.2.2.2.2.1

theorem atoms_take (h : Certified m xyz out pos) :
    (out.atoms.take m.atomCount).map heavyCore = m.atoms.map heavyCore :=
  h.2.2.2.2.2.2.1

theorem atoms_drop (h : Certified m xyz out pos) :
    out.atoms.drop m.atomCount =
      List.replicate (out.atomCount - m.atomCount) (AtomSpec.aliphatic Element.H) :=
  h.2.2.2.2.2.2.2.1

theorem bonds_original (h : Certified m xyz out pos) :
    out.bonds.filter (originalBond m) = m.bonds :=
  h.2.2.2.2.2.2.2.2.1

theorem bonds_added (h : Certified m xyz out pos) :
    (out.bonds.filter fun b => !originalBond m b).all (addedBond m) = true :=
  h.2.2.2.2.2.2.2.2.2.1

theorem writtenNeighbors_original (h : Certified m xyz out pos) :
    (List.range m.atomCount).all (fun i =>
      decide ((out.writtenNeighbors i).filter (fun j => decide (j < m.atomCount)) =
        m.writtenNeighbors i)) = true :=
  h.2.2.2.2.2.2.2.2.2.2.1

theorem added_rows (h : Certified m xyz out pos) :
    (List.range (out.atomCount - m.atomCount)).map
        (fun t => out.writtenNeighbors (m.atomCount + t)) =
      (addedParents m).map (fun p => [p]) :=
  h.2.2.2.2.2.2.2.2.2.2.2.1

theorem parents_bounded (h : Certified m xyz out pos) :
    (addedParents m).all (fun p => decide (p < m.atomCount)) = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem introductionPredecessors_eq (h : Certified m xyz out pos) :
    out.introductionPredecessors = m.introductionPredecessors :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Original atom indices keep their coordinates. -/
theorem positions_getElem? (h : Certified m xyz out pos) {i : Nat} (hi : i < m.atomCount) :
    pos.positions[i]? = xyz.positions[i]? := by
  rw [← h.positions_take, List.getElem?_take_of_lt hi]

/-- Original atom indices keep their atom, up to the inline hydrogen policy. -/
theorem atom_core (h : Certified m xyz out pos) {i : Nat} (hi : i < m.atomCount) :
    (out.atoms[i]?).map heavyCore = (m.atoms[i]?).map heavyCore := by
  have e : ((out.atoms.take m.atomCount).map heavyCore)[i]? = (m.atoms.map heavyCore)[i]? := by
    rw [h.atoms_take]
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_take_of_lt hi] at e
  exact e

theorem atom_fields (h : Certified m xyz out pos) {i : Nat} (hi : i < m.atomCount)
    {a b : AtomSpec} (ha : m.atoms[i]? = some a) (hb : out.atoms[i]? = some b) :
    b.element = a.element ∧ b.isotope? = a.isotope? ∧ b.charge = a.charge ∧
      b.aromatic = a.aromatic ∧ b.tetrahedral? = a.tetrahedral? := by
  have e := h.atom_core hi
  rw [ha, hb, Option.map_some, Option.map_some] at e
  have core : heavyCore b = heavyCore a := Option.some.inj e
  exact ⟨by simpa [heavyCore] using congrArg AtomSpec.element core, by simpa [heavyCore] using congrArg AtomSpec.isotope? core,
    by simpa [heavyCore] using congrArg AtomSpec.charge core, by simpa [heavyCore] using congrArg AtomSpec.aromatic core,
    by simpa [heavyCore] using congrArg AtomSpec.tetrahedral? core⟩

/-- Every index past the original atoms is an ordinary hydrogen. -/
theorem fresh_atom (h : Certified m xyz out pos) {i : Nat} (hle : m.atomCount ≤ i)
    (hlt : i < out.atomCount) : out.atoms[i]? = some (AtomSpec.aliphatic Element.H) := by
  have ht : i - m.atomCount < out.atomCount - m.atomCount := by omega
  have e : (out.atoms.drop m.atomCount)[i - m.atomCount]? = out.atoms[i]? := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hle]
  rw [← e, h.atoms_drop, List.getElem?_replicate, if_pos ht]

/-- Every added hydrogen has exactly one written neighbour, its planned parent. -/
theorem fresh_row (h : Certified m xyz out pos) {i : Nat} (hle : m.atomCount ≤ i)
    (hlt : i < out.atomCount) :
    ∃ p, (addedParents m)[i - m.atomCount]? = some p ∧ out.writtenNeighbors i = [p] := by
  have ht : i - m.atomCount < out.atomCount - m.atomCount := by omega
  have row : ((List.range (out.atomCount - m.atomCount)).map
      (fun t => out.writtenNeighbors (m.atomCount + t)))[i - m.atomCount]? =
        some (out.writtenNeighbors i) := by
    simp only [List.getElem?_map, List.getElem?_range ht, Option.map_some]
    rw [Nat.add_sub_of_le hle]
  have planned : ((addedParents m).map (fun p => [p]))[i - m.atomCount]? =
      some (out.writtenNeighbors i) := by
    rw [← h.added_rows]
    exact row
  rw [List.getElem?_map] at planned
  cases found : (addedParents m)[i - m.atomCount]? with
  | none =>
      rw [found] at planned
      exact absurd planned (by simp)
  | some p =>
      rw [found, Option.map_some] at planned
      exact ⟨p, rfl, (Option.some.inj planned).symm⟩

/-- The parent of an added hydrogen is an original atom. -/
theorem fresh_parent_lt (h : Certified m xyz out pos) {t p : Nat}
    (found : (addedParents m)[t]? = some p) : p < m.atomCount :=
  of_decide_eq_true (List.all_eq_true.mp h.parents_bounded p (List.mem_of_getElem? found))

end Certified

end TetraStereo.Engine.RingHydrogenCompletion

assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.prepare?
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.complete?
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.orientedVolume_single_three
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.opposite_mirrorX
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.orientedVolume_pair
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.orientedVolume_skew
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.orientedVolume_tripod
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.orientedVolume_tetra
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.placed_length
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.prepare?_eq_some_iff
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.prepare?_certified
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.prepare?_of_complete
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.Certified.positions_getElem?
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.Certified.atom_fields
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.Certified.fresh_atom
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.Certified.fresh_row
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.Certified.fresh_parent_lt

assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.orientedVolume_equivalentHydrogenPosition
