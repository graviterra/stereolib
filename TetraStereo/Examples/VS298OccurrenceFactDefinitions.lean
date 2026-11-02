import TetraStereo.Examples.VS298OccurrenceSourceCertificate

set_option autoImplicit false

namespace TetraStereo.Examples.VS298

open OneCenter

def state : OccurrenceAuxState :=
  (buildOccurrenceAuxState? molecule fuel centerOne.val).getD []

def leftExpectedFact : OccurrenceAuxFact :=
  { key := canonicalOccurrenceKey leftSource
    atom := 6
    descriptor := .R
    uppercase := true
    priorityPositions := [3, 2, 0, 1] }

def rightExpectedFact : OccurrenceAuxFact :=
  { key := canonicalOccurrenceKey rightSource
    atom := 6
    descriptor := .S
    uppercase := true
    priorityPositions := [3, 0, 2, 1] }

end TetraStereo.Examples.VS298
