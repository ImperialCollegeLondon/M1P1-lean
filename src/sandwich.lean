import limits

namespace M1P1

theorem sandwich (a b c : ℕ → ℝ)
  (l : ℝ) (ha : is_limit a l) (hc : is_limit c l) 
  (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) : is_limit b l :=
begin
  -- Choose ε > 0
  intros ε Hε,
  -- we now need an N. As usual it is the max of two other N's.
  -- Choose Na and Nc such that |aₙ - l| < ε for n ≥ Na and |cₙ - l| < ε for n ≥ Nc.
  cases ha ε Hε with Na Ha,
  cases hc ε Hε with Nc Hc,
  -- and let N be the max.
  let N := max Na Nc,
  use N,
  -- Note n ≥ Na and N ≥ Nc,
  have HNa : Na ≤ N := by obvious_ineq,  
  have HNc : Nc ≤ N := by obvious_ineq,
  -- so for all n ≥ N, 
  intros n Hn,
  -- we have aₙ ≤ bₙ ≤ cₙ, and |aₙ - l|, |bₙ - l| both < ε.
  have h1 : a n ≤ b n := hab n,
  have h2 : b n ≤ c n := hbc n,
  have h3 : |a n - l| < ε := Ha n (le_trans HNa Hn),
  have h4 : |c n - l| < ε := Hc n (le_trans HNc Hn),
  -- The result now follows easily.
  revert h3,revert h4,
  unfold abs,unfold max,
  split_ifs;intros;linarith,
end

end M1P1