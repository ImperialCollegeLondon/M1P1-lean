-- begin header
import limits
import order.filter
import topology.basic
import topology.instances.real

--set_option pp.notation false
--set_option trace.simplify.rewrite true
-- end header

/- Section
Sequence tending to a limit
-/

/-
Here we show that a sequence $(a_n)_n$ tends to a limit $ℓ$ iff the
cofinite filter on ℕ tends to the neighbourgood filter of $ℓ$ along
the function $n ↦ a_n$. 
-/

/- Lemma
Let $(a_n)$ be a sequence of reals and let $ℓ$ be a real. 
Then $a_n→ℓ$ if and only if `filter.tendsto a (filter.cofinite) (nhds l)`.
-/
--set_option pp.all true
lemma is_limit_iff_tendsto (a : ℕ → ℝ) (l : ℝ) :
(∀ ε, ε > 0 → ∃ N : ℕ, ∀ n, N ≤ n → | a n - l| < ε) ↔
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
    change X ∈ filter.map a filter.cofinite,
    apply filter.mem_sets_of_superset _ Hlε,
    -- Now let's figure out what this filter.map stuff means
    -- [dsimp and unfold faffing]
    show a ⁻¹' metric.ball l ε ∈ filter.cofinite.sets,
    show a ⁻¹' metric.ball l ε ∈ filter.cofinite,
    -- Let's use the fact that a n → l
    rcases Hl ε Hε with ⟨N, HN⟩,
    let S := {n : ℕ | N ≤ n},
    -- this is the definition of a_n → l
    have HS : S ⊆ a ⁻¹' metric.ball l ε,
    { intros n Hn,
      show a n ∈ _,
      rw metric.mem_ball,
      exact HN n Hn,
    },
    suffices : S ∈ filter.cofinite.sets,
      exact filter.mem_sets_of_superset this HS,
    show set.finite (-S),
    show set.finite {n : ℕ | ¬ (N ≤ n)},
    simp only [not_le],
    exact ⟨set.fintype_lt_nat _⟩ },
  { -- filter.tendsto implies a_n → l
    intro h,
    intros ε hε,
    -- need N such that n ≥ N implies a_n → l,
<<<<<<< HEAD:src/filter2.lean
    have : metric.ball l ε ∈ (nhds l),
      exact metric.mem_nhds_iff.2 ⟨ε, hε, by refl⟩,
    
=======
    unfold filter.tendsto at HF,
    unfold filter.map at HF,
--    have X := HF _, --(metric.ball l ε),
>>>>>>> af595e6d3ec06d523668e63274e1ad9f6149e10e:src/filter.lean
    sorry },
end

