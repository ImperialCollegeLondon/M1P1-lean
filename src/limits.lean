import data.real.basic
import tactic.linarith
import problem_sheets.sheet_1.sht01Q01

noncomputable theory

local notation `|` x `|` := abs x

definition is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε

definition has_limit (a : ℕ → ℝ) : Prop := ∃ l : ℝ, is_limit a l

-- KB doesn't understand this
--definition limit (a : ℕ → ℝ) := classical.epsilon (is_limit a)

lemma limits_aux (a : ℕ → ℝ) (l m : ℝ) (hl : is_limit a l)
(hm : is_limit a m) (hlm : l < m) : false :=
begin
  let ε := (m - l) / 2,
  have Hε : ε > 0 := by show (m - l) / 2 > 0; linarith,
  cases hl ε Hε with Nl HNl,
  cases hm ε Hε with Nm HNm,
  let N := max Nl Nm,
  have this : | a N - l| < ε,
  { apply HNl,
    show max Nl Nm ≥ Nl,
    apply le_max_left
  },
  have that : | a N - m| < ε,
  { apply HNm,
    show max Nl Nm ≥ Nm,
    apply le_max_right
  },
  have theother : 2 * ε < 2 * ε,
    calc 2 * ε = 2 * ((m - l) / 2) : by refl
    ...        = m - l : by ring
    ...        ≤ | m - l | : le_abs_self _
    ...        ≤ |a N  - l| + |a N - m| : Q1h _ _ _
    ...        < ε + ε : by linarith
    ...        = 2 * ε : by ring,
  linarith  
end

theorem limits_are_unique (a : ℕ → ℝ) (l m : ℝ) (hl : is_limit a l)
(hm : is_limit a m) : l = m :=
begin
  have H1 : ¬ (l < m)  := limits_aux a l m hl hm,  
  have H2 : ¬ (m < l) := limits_aux a m l hm hl,
  linarith
end

--example (a : ℕ → ℝ) (l : ℝ) (h : is_limit a l) : limit a = l :=
--begin
--
--end