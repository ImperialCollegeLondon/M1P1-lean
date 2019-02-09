import tactic.linarith data.real.basic

local notation `|` x `|` := abs x

lemma zero_of_abs_lt_all (x : ℝ) (h : ∀ ε > 0, |x| < ε) : x = 0 :=
eq_zero_of_abs_eq_zero $ eq_of_le_of_forall_le_of_dense (abs_nonneg x) $ λ ε ε_pos, le_of_lt (h ε ε_pos)

-- The next few things should be hidden
@[user_attribute]
meta def ineq_rules : user_attribute :=
{ name := `ineq_rules,
  descr := "lemmas usable to prove inequalities" }

attribute [ineq_rules] add_lt_add le_max_left le_max_right

meta def obvineq := `[linarith <|> apply_rules ineq_rules]
run_cmd add_interactive [`obvineq]
-- end of scary things
