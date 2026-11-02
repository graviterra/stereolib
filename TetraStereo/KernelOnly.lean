import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Reusable kernel-authority certificate command

`assert_kernel_only declaration` rejects theorem closures containing native evaluator/compiler
trust, `sorryAx`, or project axioms.  Lean's standard logical principles `propext`,
`Classical.choice`, and `Quot.sound` remain allowed.
-/

open Lean Elab Command

elab "assert_kernel_only " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "{n} has non-kernel-authority axiom {axiomName}"
