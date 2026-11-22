import TetraStereo.Engine.PublicAPI
import TetraStereo.Examples.Rule6CageAuxiliaries
import TetraStereo.Examples.LocalizedChemicalRingSpiroProjection

namespace TetraStereo.Examples.RecursivePromotions
open OneCenter Engine RingChemicalPriority LocalizedGenericMarkedRecalculation
open Rule6CageAuxiliaries

private def expect (test : Bool) (msg : String) : IO Unit :=
  unless test do throw (IO.userError msg)

private def simple (elements : List Element) : RawMolecule where
  atoms := (Element.C :: elements).map AtomSpec.aliphatic
  bonds := (List.range elements.length).map fun i => ⟨0,i+1,.single⟩

private def check : IO Unit := do
  let dioxaspiro := CentresRing.SpiroSource.molecule
  let geom : Geometry := fun i => LocalizedChemicalRingSpiroProjection.spatial.positions[i]?
  for flipped in [false,true] do
    let g := if flipped then mirror geom else geom
    let some s := checkRingPromotions? dioxaspiro g 0 1 0 (fun _ => none) (fun _ => 1)
      | throw (IO.userError "missing published spiro proof")
    expect (s.label == some (.chiral (if flipped then .S else .R)) &&
      s.trials.length == 4 && s.trials.all (·.unique)) "published spiro orders"
    let saved := if flipped then mirror twinGeometry else twinGeometry
    let some c := deriveRingOccurrence? twins saved [0] 4 hints (fun _ => 2)
      | throw (IO.userError "missing recursive Rule 5/6 derivation")
    expect (c.val == ⟨.R,.R⟩ && c.val.label == some (.pseudoasymmetric .r)) "two-cage letter"
  let some sp := checkRingPromotions? spiroPentane (fun _ => none) 0 0 0 (fun _ => none) (fun _ => 0)
    | throw (IO.userError "incomplete spiro[2.2]pentane experiment")
  expect (sp.label.isNone && sp.trials.length == 4 && sp.trials.all (!·.unique)) "four-way ring refusal"
  for (elements,n) in [([Element.Cl,.Cl,.H,.H],4),([.Cl,.H,.H,.H],3),([.H,.H,.H,.H],4)] do
    let some c := checkRingPromotions? (simple elements) (fun _ => none) 0 0 0
        (fun _ => none) (fun _ => 0) | throw (IO.userError "missing tied promotion")
    expect (c.label.isNone && c.trials.length == n && c.trials.all (!·.unique)) "unresolved ties"
  expect ((checkRingPromotions? dioxaspiro (fun _ => none) 0 1 0
    (fun _ => none) (fun _ => 1)).isNone) "missing coordinates on a strict order"
  expect ((deriveRingOccurrence? twins twinGeometry [0] 2 hints (fun _ => 2)).isNone)
    "an unfinished child derivation received a descriptor"
  expect ((checkRingPromotions? (simple [.F,.Cl,.H,.H]) geom 0 0 0
    (fun _ => none) (fun _ => 0)).isNone) "one tied pair entered Rule 6"
  IO.println "Both spiro geometries and both complete two-cage derivations agree. Spiro[2.2]pentane and three acyclic controls refuse after all promotions. Incomplete geometry, depth and ineligible partitions produce no certificate."

end TetraStereo.Examples.RecursivePromotions

def main := TetraStereo.Examples.RecursivePromotions.check
