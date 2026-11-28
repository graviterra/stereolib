import TetraStereo.Engine.RingFullPathKeyTransport
import TetraStereo.Engine.RingFullPathTrialReadings

/-! Ordinary priority and the Rule 6 mark have different observable inputs.
They may therefore be certified by different correspondences of the ligand arms. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingSplitLigandTie
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Labels Reader consistent unit)
open RingGeometryExchange (Carrier Frozen Marked)
open RingStereoSiblingPass (Branch)
open RingRetainedStereoRefinement (Derives)
open RingFullPathEligibility (Key Reads)
open RingFullPathTrialReadings (trialKey)
attribute [local instance] lexOrd

/-- For marking, retain absence, unit type, and lowercase stereochemistry.
Uppercase hands share one consistent original–mirror representative. -/
def normalize : Labels → Labels
  | (.chiral _,.chiral _) => (.chiral .R,.chiral .S)
  | other => other

def markingReader {i : Input} (read : Reader i) : Reader i := fun q =>
  (read q).map (Option.map normalize)

private theorem valid {v : Option Labels} (ok : v.all consistent = true) :
    (v.map normalize).all consistent = true := by
  rcases v with _ | ⟨(_ | _),(_ | _)⟩ <;> first | exact ok | rfl

private theorem unit_eq (v : Option Labels) (rev : Bool) :
    unit ((v.map normalize).map (fun p => if rev then p.2 else p.1)) =
    unit (v.map (fun p => if rev then p.2 else p.1)) := by
  cases rev <;> rcases v with _ | ⟨(_ | _),(_ | _)⟩ <;> rfl

private theorem lower_eq (v : Option Labels) (rev : Bool) :
    RingRetainedStereoRefinement.Observation.lowercase.value (v.map normalize) rev =
    RingRetainedStereoRefinement.Observation.lowercase.value v rev := by
  cases rev <;> rcases v with _ | ⟨(_ | _),(_ | _)⟩ <;> rfl

private theorem normalized_unit {i : Input} {r : Reader i} {rev q b}
    (h : RingRetainedUnitPass.Reading i r rev q b) :
    RingRetainedUnitPass.Reading i (markingReader r) rev q b := by
  induction h with
  | @node q k v cs sh de key seen phy lookup complete below first deep ih =>
    rw [← unit_eq v rev]
    exact .node key (by simp [markingReader,seen])
      ⟨valid phy.1,fun empty => by simp [phy.2 empty]⟩ lookup complete ih first deep

private theorem normalized_lower {i : Input} {r : Reader i} {rev q b}
    (h : Derives i r rev [.lowercase] q b) :
    Derives i (markingReader r) rev [.lowercase] q b := by
  change RingRetainedStereoRefinement.Pass _ _ _ _ _ _ _ at h ⊢
  induction h with
  | @node q p v cs sh de before seen lookup complete below first deep ih =>
    rw [← lower_eq v rev]
    exact .node (normalized_unit before) (by simp [markingReader,seen]) lookup complete ih first deep

theorem normalized_mark {i : Input} {r : Reader i} {rev atom q b}
    (h : RingGroupedMark.OnGeometry i r rev atom q b) :
    RingGroupedMark.OnGeometry i (markingReader r) rev atom q b := by
  induction h with
  | node before lookup complete below first deep ih =>
    exact .node (normalized_lower before) lookup complete ih first deep

/-- The full trial ties if one correspondence preserves ordinary stereopriorities
and another preserves the marked atom, constitutions and lowercase observations.
Neither witness needs to satisfy the requirements of the other. -/
theorem tie_of_two_matches {i j : Input} {l : Reader i} {r : Reader j}
    {p : Arm i} {q : Arm j} {rev a b} {x y : Key} {u v : Branch}
    (ordinary marked : Carrier i j)
    (start : ordinary.domain p) (toRight : ordinary.image p = q) (hands : Frozen ordinary l r)
    (markedStart : marked.domain p) (markedRight : marked.image p = q)
    (types : Frozen marked (markingReader l) (markingReader r)) (bits : Marked marked a b)
    (left : Reads i l rev p x) (right : Reads j r rev q y)
    (ml : RingGroupedMark.OnGeometry i l rev a p u) (mr : RingGroupedMark.OnGeometry j r rev b q v) :
    compare (trialKey x u.word) (trialKey y v.word) = .eq := by
  have keys := RingFullPathKeyTransport.reads_transport ordinary hands rev start left (toRight.symm ▸ right)
  have marks := marked.mark types bits markedStart (normalized_mark ml) (markedRight.symm ▸ normalized_mark mr)
  rw [keys,marks]
  exact Std.ReflCmp.compare_self

end TetraStereo.Engine.RingSplitLigandTie
assert_kernel_only TetraStereo.Engine.RingSplitLigandTie.normalized_mark
assert_kernel_only TetraStereo.Engine.RingSplitLigandTie.tie_of_two_matches
