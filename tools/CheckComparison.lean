import Lean
import MathNetwork.Comparisons.Registry

/-!
# Kernel-backed comparison check

This command compares the elaborated declaration types, not their source
spelling.  It succeeds exactly when Lean's definitional-equality procedure
accepts the two proposition types as equal.
-/

open Lean Elab Command Meta

syntax "check_defeq " ident ident : command

elab_rules : command
  | `(check_defeq $left:ident $right:ident) => do
    let env ← getEnv
    let some leftInfo := env.find? left.getId
      | throwError s!"declaration not found: {left.getId}"
    let some rightInfo := env.find? right.getId
      | throwError s!"declaration not found: {right.getId}"
    let equal ← liftTermElabM fun _ => isDefEq leftInfo.type rightInfo.type
    if !equal then
      throwError s!"declaration types are not definitionally equal: {left.getId} and {right.getId}"
    logInfo s!"definitional equality checked: {left.getId} ≡ {right.getId}"

/-!
The current √2 comparison has its Mathlib route registered.  The
computable-analysis rational-square-root criterion has a different native
`RealRaw` statement and will be added here once a checked representation
bridge supplies a literal common proposition.
-/
