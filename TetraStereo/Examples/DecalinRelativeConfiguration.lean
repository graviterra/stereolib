import TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation
import TetraStereo.KernelOnly

/-! The two unlabeled four-carbon routes around decalin are consistently named
A and B at both fusion atoms. The reference frames use (other fusion atom,
route A, route B, H). Orienting the shared edge from opposite ends reverses
the local traversal, so opposite frame signs encode cis and matching signs
encode trans. P-93.5.4.1 gives cis-(4as,8as) and trans-(4ar,8ar).
https://iupac.qmul.ac.uk/BlueBook/P9.html#P-93.5.4.1

This is a coordinate specification of the relative fusion configuration.
Its source calibration is independent of any frozen ring reader. -/
set_option autoImplicit false
namespace TetraStereo.Examples.DecalinRelativeConfiguration
open OneCenter CartesianPoint3 CertifiedLocalizedCIPInput

structure Frame (α : Type) where
  other : α
  routeA : α
  routeB : α
  hydrogen : α

def Frame.map {α β : Type} (f : α → β) (v : Frame α) : Frame β :=
  ⟨f v.other,f v.routeA,f v.routeB,f v.hydrogen⟩

def Frame.exchange {α : Type} (v : Frame α) : Frame α :=
  ⟨v.other,v.routeB,v.routeA,v.hydrogen⟩

def Frame.volume (f : Frame CartesianPoint3) : ℚ :=
  orientedVolume f.other f.routeA f.routeB f.hydrogen

theorem volume_exchange (f : Frame CartesianPoint3) : f.exchange.volume = -f.volume := by
  simp only [Frame.volume,Frame.exchange,orientedVolume]
  ring

def relative (a b : Frame CartesianPoint3) : Option PseudoRS :=
  if a.volume * b.volume < 0 then some .s
  else if 0 < a.volume * b.volume then some .r else none

theorem relative_none (a b : Frame CartesianPoint3) :
    relative a b = none ↔ a.volume = 0 ∨ b.volume = 0 := by
  unfold relative
  split_ifs with neg pos
  · simpa using mt (mul_eq_zero.mpr : a.volume = 0 ∨ b.volume = 0 → a.volume*b.volume = 0)
      (ne_of_lt neg)
  · simpa using mt (mul_eq_zero.mpr : a.volume = 0 ∨ b.volume = 0 → a.volume*b.volume = 0)
      (ne_of_gt pos)
  · simp [mul_eq_zero.mp (le_antisymm (not_lt.mp pos) (not_lt.mp neg))]

theorem relative_exchange_routes (a b : Frame CartesianPoint3) :
    relative a.exchange b.exchange = relative a b := by simp [relative,volume_exchange]

theorem relative_exchange_junctions (a b : Frame CartesianPoint3) :
    relative b a = relative a b := by simp only [relative,mul_comm b.volume a.volume]

theorem relative_reflect (a b : Frame CartesianPoint3) :
    relative (a.map reflectX) (b.map reflectX) = relative a b := by
  simp [relative,Frame.map,Frame.volume,orientedVolume_reflectX]

/-- A local read with remote R keeps the route order; with remote S it
exchanges the two routes. Thus the conventional local reference reading
changes along with the remote one on reflection. -/
def localReading (here other : Frame CartesianPoint3) : Option PseudoRS := do
  let remote ← descriptorOfOrientedVolume? other.volume
  let ordered := match remote with | .R => here | .S => here.exchange
  return pseudoRSOfRS (← descriptorOfOrientedVolume? ordered.volume)

theorem localReading_eq_relative (here other : Frame CartesianPoint3) :
    localReading here other = relative here other := by
  by_cases hn : here.volume < 0 <;> by_cases hp : 0 < here.volume <;>
    by_cases on_ : other.volume < 0 <;> by_cases op : 0 < other.volume <;>
    first | exfalso; linarith | simp [localReading,relative,descriptorOfOrientedVolume?,
      pseudoRSOfRS,volume_exchange,mul_neg_iff,mul_pos_iff,hn,hp,on_,op]


theorem both_junctions (a b : Frame CartesianPoint3) :
    localReading a b = relative a b ∧ localReading b a = relative a b :=
  ⟨localReading_eq_relative ..,(localReading_eq_relative ..).trans (relative_exchange_junctions ..)⟩

/-- Atom renumbering transports both frames and all coordinates together. -/
theorem relative_reindex {α β : Type} (e : α ≃ β) (p : α → CartesianPoint3) (a b : Frame α) :
    relative ((a.map e).map (p ∘ e.symm)) ((b.map e).map (p ∘ e.symm)) =
      relative (a.map p) (b.map p) := by simp [Frame.map]

/-- Raw atom IDs in the two pinned 3D SDF records (zero-based). -/
def junctions : Frame Nat × Frame Nat := (⟨1,2,6,10⟩,⟨0,3,8,11⟩)

/-- Only the eight frame coordinates enter the test. Values are the VS211
and VS212 SDF coordinates scaled by 10000, as in DecalinJunctions.lean. -/
def vs211 : Nat → CartesianPoint3
  | 0 => ⟨23063,-12280,-1137⟩
  | 1 => ⟨23059,-27931,-1330⟩
  | 2 => ⟨10648,-5513,-7002⟩
  | 3 => ⟨10171,-35138,-6320⟩
  | 6 => ⟨35478,-5521,-7009⟩
  | 8 => ⟨35946,-35144,-6314⟩
  | 10 => ⟨23067,-9565,9538⟩
  | 11 => ⟨23056,-30356,9350⟩
  | _ => ⟨0,0,0⟩

def vs212 : Nat → CartesianPoint3
  | 0 => ⟨22974,-8693,-8087⟩
  | 1 => ⟨22992,-18107,-20305⟩
  | 2 => ⟨10399,127,-8103⟩
  | 3 => ⟨10178,-26513,-20816⟩
  | 6 => ⟨35586,30,-8020⟩
  | 8 => ⟨35648,-26774,-20506⟩
  | 10 => ⟨22915,-14743,1049⟩
  | 11 => ⟨23177,-11959,-29360⟩
  | _ => ⟨0,0,0⟩

def read (p : Nat → CartesianPoint3) := relative (junctions.1.map p) (junctions.2.map p)

theorem source_checks :
    ((junctions.1.map vs211).volume,(junctions.2.map vs211).volume) = (8636659707494,-8592792812744) ∧
    ((junctions.1.map vs212).volume,(junctions.2.map vs212).volume) = (8743775978678,8682227165375) ∧
    read vs211 = some .s ∧ read vs212 = some .r := by decide +kernel
end TetraStereo.Examples.DecalinRelativeConfiguration
assert_kernel_only TetraStereo.Examples.DecalinRelativeConfiguration.both_junctions
assert_kernel_only TetraStereo.Examples.DecalinRelativeConfiguration.source_checks
