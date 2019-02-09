import data.real.basic tactic.linarith

theorem Q3 (S : set ℝ) (HS : ∃ a : ℝ, a ∈ S) (u : ℝ) (Hu : u ∈ upper_bounds S) :
is_lub S u ↔ ∀ ε > 0, ∃ s ∈ S, s > u - ε :=
begin
  split,
  { intro Hu,
    intros ε Hε,
    let v := u - ε,
    have Hv : ¬ (u ≤ v),
      change ¬ (u ≤ u - ε),
      linarith,
    have Hv' : v ∉ upper_bounds S,
      intro Hv'',
      apply Hv,
      apply Hu.2,
      assumption,
    change ¬ (v ∈ {x : ℝ | ∀ s, s ∈ S → s ≤ v}) at Hv', -- bug in Lean?
    change ¬ (v ∈ {x : ℝ | ∀ s, s ∈ S → s ≤ x}) at Hv', -- bug in Lean?
  --  change ¬ (∀ s : ℝ, s ∈ S → s ≤ v) at Hv',
    rw not_forall at Hv',
    sorry },
  { 
    sorry },
end

