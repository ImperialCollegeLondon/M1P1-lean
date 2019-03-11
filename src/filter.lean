import limits
import order.filter
import topology.basic
import topology.instances.real

--set_option pp.notation false
lemma is_limit_iff_tendsto (a : ℕ → ℝ) (l : ℝ) :
M1P1.is_limit a l ↔
  filter.tendsto a (filter.cofinite) (nhds l) :=
begin
  split,
  { -- a_n → l implies filter.tendsto
    intro Hl,
    intro X,
    intro HX,
    -- What we have to prove is that if that X is a nhd of l
    -- then `X ∈ (filter.map a filter.cofinite).sets`
    -- These next three lines show that WLOG X is B(l,ε)
    rw metric.mem_nhds_iff at HX,
    rcases HX with ⟨ε, Hε, Hlε⟩,
    apply filter.mem_sets_of_superset _ Hlε,
    -- Now let's figure out what this filter.map stuff means
    -- [dsimp and unfold faffing]
    show a ⁻¹' metric.ball l ε ∈ filter.cofinite.sets,
    -- Let's use the fact that a n → l
    rcases Hl ε Hε with ⟨N, HN⟩,
    let S := {n : ℕ | N ≤ n},
    have HS : S ⊆ a ⁻¹' metric.ball l ε,
    { intros n Hn,
      show a n ∈ _,
      rw metric.mem_ball,
      exact HN n Hn,
    },
    apply filter.mem_sets_of_superset _ HS,
    show set.finite (-S),
    show set.finite {n : ℕ | ¬ (N ≤ n)},
    simp only [not_le],
    exact ⟨set.fintype_lt_nat _⟩ },
  { intro h,
    intros ε hε,
    have H : metric.ball l ε ∈ nhds l := metric.mem_ball, 
    sorry },
end

