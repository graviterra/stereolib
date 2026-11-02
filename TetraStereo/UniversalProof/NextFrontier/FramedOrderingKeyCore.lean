import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorRuntime

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace TetraStereo.OneCenter.FramedOrderingKeyCore

open RawMolecule FrameRuntime

/-! Unary expansion for the actual framed runtime. Totalization affects only unsuccessful
queries. No ordering law is assumed of the sibling callback. Padding retains its parent cursor;
it is never identified with an ordinary phantom node. -/

def totalDecision (before : Cursor → Cursor → Option Ordering)
    (left right : Cursor) : Ordering := (before left right).getD .eq

def insertTotal (before : Cursor → Cursor → Option Ordering) (candidate : Cursor) :
    List Cursor → List Cursor
  | [] => [candidate]
  | head :: tail =>
      if totalDecision before candidate head == .lt then
        head :: insertTotal before candidate tail
      else candidate :: head :: tail

def sortTotal (before : Cursor → Cursor → Option Ordering) : List Cursor → List Cursor
  | [] => []
  | head :: tail => insertTotal before head (sortTotal before tail)

theorem insertTotal_success (before : Cursor → Cursor → Option Ordering) (candidate : Cursor) :
    ∀ input output, FrameRuntime.insert? before candidate input = some output →
      insertTotal before candidate input = output
  | [], output, computed => by
      simpa [FrameRuntime.insert?, insertTotal] using computed
  | head :: tail, output, computed => by
      cases decisionEq : before candidate head with
      | none => simp [FrameRuntime.insert?, decisionEq] at computed
      | some decision =>
          cases decision with
          | lt =>
              cases restEq : FrameRuntime.insert? before candidate tail with
              | none => simp [FrameRuntime.insert?, decisionEq, restEq] at computed
              | some rest =>
                  have recursive := insertTotal_success before candidate tail rest restEq
                  simpa [FrameRuntime.insert?, decisionEq, restEq, insertTotal,
                    totalDecision, recursive] using computed
          | eq =>
              simp [FrameRuntime.insert?, decisionEq] at computed
              subst output
              simp [insertTotal, totalDecision, decisionEq]
          | gt =>
              simp [FrameRuntime.insert?, decisionEq] at computed
              subst output
              simp [insertTotal, totalDecision, decisionEq]

theorem sortTotal_success (before : Cursor → Cursor → Option Ordering) :
    ∀ input output, FrameRuntime.sort? before input = some output →
      sortTotal before input = output
  | [], output, computed => by
      simpa [FrameRuntime.sort?, sortTotal] using computed
  | head :: tail, output, computed => by
      cases restEq : FrameRuntime.sort? before tail with
      | none => simp [FrameRuntime.sort?, restEq] at computed
      | some rest =>
          have recursive := sortTotal_success before tail rest restEq
          have inserted := insertTotal_success before head rest output (by
            simpa [FrameRuntime.sort?, restEq] using computed)
          simpa [sortTotal, recursive] using inserted

@[simp] theorem insertTotal_length (before : Cursor → Cursor → Option Ordering)
    (candidate : Cursor) : ∀ input,
    (insertTotal before candidate input).length = input.length + 1
  | [] => rfl
  | head :: tail => by
      simp only [insertTotal]
      split <;> simp [insertTotal_length before candidate tail]

@[simp] theorem sortTotal_length (before : Cursor → Cursor → Option Ordering) : ∀ input,
    (sortTotal before input).length = input.length
  | [] => rfl
  | head :: tail => by simp [sortTotal, sortTotal_length before tail]

def slots (authoritative : Bool) : Nat := if authoritative then authoritativeChildSlots else 3

def children (mol : RawMolecule) (authoritative : Bool)
    (before : Cursor → Cursor → Option Ordering) (parent : Cursor) : List Cursor :=
  let sorted := sortTotal before (((parent.original mol).children mol).map Cursor.actual)
  let bounded := sorted.take (slots authoritative)
  bounded ++ List.replicate (slots authoritative - bounded.length) (.padding parent)

@[simp] theorem children_length (mol : RawMolecule) (authoritative : Bool)
    (before : Cursor → Cursor → Option Ordering) (parent : Cursor) :
    (children mol authoritative before parent).length = slots authoritative := by
  simp [children]

/-- Every successful framed child expansion is the same independently compiled unary frame.
Profile and incidence validation remain production success conditions. -/
theorem ranked_success (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (before : Cursor → Cursor → Option Ordering) (parent : Cursor) (ranked : List Cursor)
    (computed : ranked? mol profile authoritative before parent = some ranked) :
    children mol authoritative before parent = ranked := by
  let originalChildren := ((parent.original mol).children mol).map Cursor.actual
  change ((cursor? mol profile parent).bind fun _ =>
      if slots authoritative < originalChildren.length then none else
      (originalChildren.mapM (cursor? mol profile)).bind fun _ =>
      (FrameRuntime.sort? before originalChildren).bind fun sorted =>
      some (sorted ++ List.replicate (slots authoritative - sorted.length) (.padding parent))) =
        some ranked at computed
  cases parentEq : cursor? mol profile parent with
  | none => simp only [parentEq, Option.bind_none, reduceCtorEq] at computed
  | some distance =>
      simp only [parentEq, Option.bind_some] at computed
      by_cases tooWide : slots authoritative < originalChildren.length
      · simp only [if_pos tooWide, reduceCtorEq] at computed
      · simp only [if_neg tooWide] at computed
        cases validatedEq : originalChildren.mapM (cursor? mol profile) with
        | none => simp only [validatedEq, Option.bind_none, reduceCtorEq] at computed
        | some validated =>
            simp only [validatedEq, Option.bind_some] at computed
            cases sortedEq : FrameRuntime.sort? before originalChildren with
            | none => simp only [sortedEq, Option.bind_none, reduceCtorEq] at computed
            | some sorted =>
                simp only [sortedEq, Option.bind_some, Option.some.injEq] at computed
                have totalSorted : sortTotal before originalChildren = sorted :=
                  sortTotal_success before originalChildren sorted sortedEq
                have sortedLength : sorted.length = originalChildren.length := by
                  rw [← totalSorted]
                  exact sortTotal_length before originalChildren
                have takeEq : sorted.take (slots authoritative) = sorted :=
                  List.take_of_length_le (sortedLength.trans_le (Nat.le_of_not_gt tooWide))
                change (sortTotal before originalChildren).take (slots authoritative) ++
                    List.replicate (slots authoritative -
                      ((sortTotal before originalChildren).take (slots authoritative)).length)
                      (.padding parent) = ranked
                rw [totalSorted, takeEq]
                exact computed

def next (mol : RawMolecule) (authoritative : Bool)
    (before : Cursor → Cursor → Option Ordering) (frontier : List Cursor) : List Cursor :=
  frontier.flatMap (children mol authoritative before)

def frontiers (mol : RawMolecule) (authoritative : Bool)
    (before : Cursor → Cursor → Option Ordering) : Nat → List Cursor → List (List Cursor)
  | 0, frontier => [frontier]
  | depth + 1, frontier =>
      frontier :: frontiers mol authoritative before depth (next mol authoritative before frontier)

/-- Both validation helpers only check their argument; they do not transform it. -/
theorem validateCursors_success (mol : RawMolecule) (profile : Profile) :
    ∀ input output, validateCursors? mol profile input = some output → output = input
  | [], output, computed => by simpa [validateCursors?] using computed.symm
  | cursor :: rest, output, computed => by
      cases cursorEq : cursor? mol profile cursor with
      | none => simp [validateCursors?, cursorEq] at computed
      | some distance =>
          cases restEq : validateCursors? mol profile rest with
          | none => simp [validateCursors?, cursorEq, restEq] at computed
          | some result =>
              have recursive := validateCursors_success mol profile rest result restEq
              simpa [validateCursors?, cursorEq, restEq, recursive] using computed.symm

theorem validatePairs_success (mol : RawMolecule) (profile : Profile) :
    ∀ input output, validatePairs? mol profile input = some output → output = input
  | [], output, computed => by simpa [validatePairs?] using computed.symm
  | (left, right) :: rest, output, computed => by
      cases leftEq : cursor? mol profile left with
      | none => simp [validatePairs?, leftEq] at computed
      | some ld =>
          cases rightEq : cursor? mol profile right with
          | none => simp [validatePairs?, leftEq, rightEq] at computed
          | some rd =>
              cases restEq : validatePairs? mol profile rest with
              | none => simp [validatePairs?, leftEq, rightEq, restEq] at computed
              | some result =>
                  have recursive := validatePairs_success mol profile rest result restEq
                  simpa [validatePairs?, leftEq, rightEq, restEq, recursive] using computed.symm

end TetraStereo.OneCenter.FramedOrderingKeyCore
