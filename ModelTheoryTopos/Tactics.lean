-- the syntax for the tactic `change a with b` is defined in Init.Tactics but not defined
-- Here's a slightly hackish implementation
macro_rules | `(tactic|change $a with $b) => `(tactic|(have : $a = $b := rfl) ; rw [this]; clear this)
