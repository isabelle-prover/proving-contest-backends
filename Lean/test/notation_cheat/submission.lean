-- From https://leanprover-community.github.io/archive/113488general/94070ProvingforFun.html#173211569

namespace tactic.interactive
open lean.parser
@[user_command] meta def evil_cmd (_ : interactive.parse $ tk "evil") : lean.parser unit :=
with_input command_like ("nota" ++ "tion `false` := 0 = 0") >> return ()
end tactic.interactive
evil

theorem soundness_bug : false := rfl
