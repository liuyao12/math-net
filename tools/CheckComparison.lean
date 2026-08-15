import Lean
import MathNetwork.Comparisons.Registry
import MathNetwork.Euler.Applications

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
A representative exact merge. `tools/build-graph.sh` generates and runs the
complete `isDefEq` check set for every exact merge in the published graph.
The computable square-root criterion deliberately remains a
foundation-aligned (not definitionally equal) comparison.
-/
check_defeq MathNetwork.Euler.trig_addition_real_route Real.cos_add
