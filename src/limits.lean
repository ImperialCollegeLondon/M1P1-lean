/- limits.lean

Limits of sequences.

Part of the M1P1 Lean project.

This file contains the basic definition of the limit of a sequence, and
proves basic properties about it.

It is full of comments in an attempt to make it more comprehensible to
mathematicians with little Lean experience, although by far the best
way to understand what is going on is to open the file within Lean 3.4.2
so you can check out the goal at each line -- this really helps understanding.
-/

-- The import below gives us a working copy of the real numbers ℝ,
-- and functions such as abs : ℝ → ℝ 
import data.real.basic

-- This import has addition of functions, which we need for sums of limits.
import algebra.pi_instances

-- This next import gives us several tactics of use to mathematicians:
-- (1) norm_num [to prove basic facts about reals like 2+2 = 4]
-- (2) ring [to prove basic algebra identities like (a+b)^2 = a^2+2ab+b^2]
-- (3) linarith [to prove basic inequalities like x > 0 -> x/2 > 0]
import tactic.linarith

-- These lines switch Lean into "maths proof mode" -- don't worry about them.
-- Basically they tell Lean to use the axiom of choice and the
-- law of the excluded middle, two standard maths facts which we
-- assume all the time in maths, usually without comment. 
noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

-- the maths starts here.

-- We introduce the usual mathematical notation for absolute value
local notation `|` x `|` := abs x

-- We model a sequence a₀, a₁, a₂,... of real numbers as a function
-- from ℕ := {0,1,2,...} to ℝ, sending n to aₙ . So in the below
-- definition of the limit of a sequence, a : ℕ → ℝ is the sequence.

-- We first formalise the definition of "aₙ → l as n → ∞"
definition is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε

-- A sequence converges if and only if it has a limit. The difference
-- with this definition is that we don't specify the limit, we just
-- claim that it exists.
definition has_limit (a : ℕ → ℝ) : Prop := ∃ l : ℝ, is_limit a l

-- We now start on the proof of the theorem that if a sequence has
-- two limits, they are equal. We start with a lemma.

theorem triangle' (x y z : ℝ) : | x - y | ≤ | z - y | + | z - x | :=
begin
  -- See the solution to sheet 1 Q1a for a more detailed explanation of this argument.
  -- We start by unfolding the definitions.
  unfold abs, unfold max,
  -- The value of | x - y | depends on whether x - y ≥ 0 or < 0. 
  -- The `split_ifs` tactic splits into these 8 = 2^3 cases
  split_ifs,
  -- Each case is trivial by easy inequality arguments, and the `linarith`
  -- tactic solves them all.
  repeat {linarith},
end

-- We're ready to prove the theorem.
theorem limits_are_unique (a : ℕ → ℝ) (l m : ℝ) (hl : is_limit a l)
(hm : is_limit a m) : l = m :=
begin
  -- WLOG l ≤ m.
  wlog h : l ≤ m, 
  -- We're trying to prove l = m, so it suffices to prove l < m is false.
  suffices : ¬ (l < m),
    linarith,
  -- don't need h any more
  clear h,
  -- Let's prove it by contradiction. So let's assume l < m.
  intro hlm,
  -- Our goal is now "⊢ false" and hlm is the assumption l < m.
  -- Situation so far: aₙ → l, aₙ → m, hlm is the assumption l < m
  -- and we're looking for a contradiction.
  let ε := (m - l) / 2, -- This is a standard trick.
  -- First note that ε is positive, because l > m.
  have Hε : ε > 0 := by {show (m - l) / 2 > 0, linarith},
  -- Because aₙ → l, there exists N₁ such that n ≥ N₁ → |aₙ - l| < ε 
  cases hl ε Hε with N₁ HN₁,
  -- Because bₙ → m, there exists N₂ such that n ≥ N₂ → |bₙ - m| < ε 
  cases hm ε Hε with N₂ HN₂,
  -- The trick is to let N be the max of N₁ and N₂
  let N := max N₁ N₂,
  -- Now clearly N ≥ N₁...
  have H₁ : N₁ ≤ N := le_max_left _ _,
  -- ... so |a_N - l| < ε
  have Ha : | a N - l| < ε := HN₁ N H₁,
  -- similarly N ≥ N₂...
  have H₂ : N₂ ≤ N := le_max_right _ _,
  -- ... so |a_N - m| < ε too
  have H₂ : | a N - m| < ε := HN₂ N H₂,
  -- So now a basic calculation shows 2ε < 2ε. Let's go through it.
  have weird : 2 * ε < 2 * ε,
    calc 2 * ε = 2 * ((m - l) / 2) : by refl -- by definition
                 -- and this is obviously m - l
    ...        = m - l : by ring
                 -- which is at most its own absolute value
    ...        ≤ | m - l | : le_abs_self _
                 -- and now use the triangle inequality
    ...        ≤ |a N  - l| + |a N - m| : triangle' _ _ _
                 -- and stuff we proved already
    ...        < ε + ε : by linarith
                 -- to deduce this is less than 2ε
    ...        = 2 * ε : by ring,
  -- That's the contradiction we seek!
  linarith -- (it's an easy inequality argument)
end

-- We now prove that if aₙ → l and bₙ → m then aₙ + bₙ → l + m.
theorem tendsto_add (a : ℕ → ℝ) (b : ℕ → ℝ) (l m : ℝ)
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a + b) (l + m) :=
begin
  -- let epsilon be a positive real
  intros ε Hε,
  -- We now need to come up with N such that n >= N implies
  -- |aₙ + bₙ - (l + m)| < ε.
  -- Well, note first that epsilon / 2 is also positive.
  have Hε2 : ε / 2 > 0 := by linarith,
  -- Choose large M₁ such that n ≥ M₁ implies |a n - l| < ε /2
  cases (h1 (ε / 2) Hε2) with M₁ HM₁,
  -- similarly choose M₂ for the b sequence. 
  cases (h2 (ε / 2) Hε2) with M₂ HM₂,
  -- let N be the max of M1 and M2
  let N := max M₁ M₂,
  -- and let's use that 
  use N,
  -- Of course N ≥ M₁ and N ≥ M₂
  have H₁ : N ≥ M₁ := le_max_left _ _,
  have H₂ : N ≥ M₂ := le_max_right _ _,
  -- Now say n ≥ N.
  intros n Hn,
  -- Then obviously n ≥ M₁...
  have Hn₁ : n ≥ M₁ := by linarith,
  -- ...so |aₙ - l| < ε /2
  have H3 : |a n - l| < ε / 2 := HM₁ n Hn₁,
  -- and similarly n ≥ M₂, so |bₙ - l| < ε / 2
  have H4 : |b n - m| < ε / 2 := HM₂ n (by linarith),
  -- And now what we want (|aₙ + bₙ - (l + m)| < ε) 
  -- follows from a calculation.
                               -- First do some obvious algebra
  calc |(a + b) n - (l + m)| = |(a n - l) + (b n - m)| : by ring
                               -- now use the triangle inequality
  ...                        ≤ |(a n - l)| + |(b n - m)| : abs_add _ _
                               -- and our assumptions
  ...                        < ε / 2 + ε / 2 : by linarith 
                               -- and a bit more algebra
  ...                        = ε : by ring
end

-- A sequence (aₙ) is *bounded* if there exists some real number B such that |aₙ| ≤ B for all n≥0.

definition has_bound (a : ℕ → ℝ) (B : ℝ) := ∀ n, |a n| ≤ B
definition is_bounded (a : ℕ → ℝ) := ∃ B, has_bound a B

-- A convergent sequence is bounded.
open finset
theorem bounded_of_convergent (a : ℕ → ℝ) (Ha : has_limit a) : is_bounded a :=
begin
  -- let l be the limit of the sequence.
  cases Ha with l Hl,
  -- By definition, there exist some N such that n ≥ N → |aₙ - l| < 1
  cases Hl 1 (zero_lt_one) with N HN,
  -- Let X be {|a₀|, |a₁|, ... , |a_N|}...
  let X := image (abs ∘ a) (range (N + 1)),
  -- ...let's remark that |a₀| ∈ X so X ≠ ∅ while we're here...
  have H2 : |a 0| ∈ X := mem_image_of_mem _ (mem_range.2 (nat.zero_lt_succ _)),
  have H3 : X ≠ ∅ := ne_empty_of_mem H2,
  -- ...and let B₀ be the max of X.
  let B₀ := max' X H3,
  -- If n ≤ N then |aₙ| ≤ B₀.
  have HB₀ : ∀ n ≤ N, |a n| ≤ B₀ := λ n Hn, le_max' X H3 _
    (mem_image_of_mem _ (mem_range.2 (nat.lt_succ_of_le Hn))),
  -- So now let B = max {B₀, |l| + 1}
  let B := max B₀ ( |l| + 1),
  -- and we claim this bound works, i.e. |aₙ| ≤ B for all n ∈ ℕ.
  use B,
  -- Because if n ∈ ℕ,
  intro n,
  -- then either n ≤ N or n > N.
  cases le_or_gt n N with Hle Hgt,
  { -- if n ≤ N, then |aₙ| ≤ B₀
    have h : |a n| ≤ B₀ := HB₀ n Hle,
    -- and B₀ ≤ B 
    have h2 : B₀ ≤ B := le_max_left _ _,
    -- so we're done
    linarith },
  { -- and if n > N, then |aₙ - l| < 1...
    have h : |a n - l| < 1 := HN n (le_of_lt Hgt),
    -- ...so |aₙ| < 1 + |l|...
    have h2 : |a n| < |l| + 1,
      -- todo (kmb) -- remove linarith bug workaround
      revert h,unfold abs,unfold max,split_ifs;intros;linarith {restrict_type := ℝ},
    -- ...which is ≤ B
    have h3 : |l| + 1 ≤ B := le_max_right _ _,
    -- ...so we're done in this case too
    linarith   
  }
end

-- more convenient theorem: a sequence with a limit
-- is bounded in absolute value by a positive real.
theorem bounded_pos_of_convergent (a : ℕ → ℝ) (Ha : has_limit a) :
∃ B : ℝ, B > 0 ∧ has_bound a B :=
begin
  -- We know the sequence is bounded. Say it's bounded by B₀.
  cases bounded_of_convergent a Ha with B₀ HB₀,
  -- let B = |B₀| + 1; this bound works.
  let B := |B₀| + 1,
  use B,
  -- B is obviously positive 
  split,
  { -- (because 1 > 0...
    apply lt_of_lt_of_le zero_lt_one,
    show 1 ≤ |B₀| + 1,
    apply le_add_of_nonneg_left',
    -- ... and |B₀| ≥ 0)
    exact abs_nonneg _
  },
  -- so it suffices to prove B is a bound.
  -- If n is a natural
  intro n,
  -- then |aₙ| ≤ B₀
  apply le_trans (HB₀ n),
  -- so it suffices to show B₀ ≤ |B₀| + 1
  show B₀ ≤ |B₀| + 1,
  -- which is obvious.
  apply le_trans (le_abs_self B₀),
  simp [zero_le_one],
end

-- If a convergent sequence is bounded in absolute value by B,
-- then the limit is also bounded in absolute value by B.
theorem limit_bounded_of_bounded {a : ℕ → ℝ} {l : ℝ} (Ha : is_limit a l)
  {B : ℝ} (HB : has_bound a B) : |l| ≤ B :=
begin
  -- Suppose it's not true.
  apply le_of_not_gt,
  -- Then |l| > B.
  intro HlB,
  -- Set ε = (|l| - B) / 2,
  let ε := ( |l| - B) / 2,
  -- noting that it's positive
  have Hε : ε > 0 := div_pos (by linarith) (by linarith),
  -- and choose N such that |a_N - l| < ε
  cases Ha ε Hε with N HN,
  have HN2 := HN N (le_refl _),
  -- Now |a_N| ≤ B
  have HB2 : |a N| ≤ B := HB N,
  -- so now we get a contradiction
  have Hcontra :=
  calc |l| ≤ |a N - l| + |a N| : by unfold abs;unfold max;split_ifs;linarith
  ...      < ε + B : add_lt_add_of_lt_of_le HN2 HB2
  ...      = ( |l| - B) / 2 + B : rfl
  ...      < |l| : by linarith,
  linarith,  
end

-- The limit of the product is the product of the limits.
-- If aₙ → l and bₙ → m then aₙ * bₙ → l * m.
theorem tendsto_mul (a : ℕ → ℝ) (b : ℕ → ℝ) (l m : ℝ)
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a * b) (l * m) :=
begin
  -- let epsilon be a positive real
  intros ε Hε,
  -- Now aₙ has a limit,
  have ha : has_limit a := ⟨l,h1⟩,
  -- so it's bounded in absolute value by a positive real A
  rcases bounded_pos_of_convergent a ha with ⟨A,HApos,HAbd⟩,
  -- Similarly bₙ is bounded by B.
  rcases bounded_pos_of_convergent b ⟨m,h2⟩ with ⟨B,HBpos,HBbd⟩,
  -- Now chose N_A such that n ≥ N_A -> |aₙ - l| < ε / 2B
  cases h1 (ε / (2 * B)) (div_pos Hε (by linarith)) with NA HNA,
  -- and choose N_B such that n ≥ N_B -> |bₙ - m| < ε /2A
  cases h2 (ε / (2 * A)) (div_pos Hε (by linarith)) with NB HNB,
  -- Let N be the max of N_A and N_B; this N works.
  let N := max NA NB,
  use N,
  -- For if n ≥ N
  intros n Hn,
  -- then |aₙ bₙ - l m| ...
  calc 
        |a n * b n - l * m| 
      = |a n * (b n - m) + (a n - l) * m | : by ring
  ... ≤ |a n * (b n - m)| + |(a n - l) * m| : abs_add _ _
  ... ≤ |a n| * |b n - m| + |a n - l| * |m| : by simp [abs_mul]
  ... ≤ A * |b n - m| + |a n - l| * |m| :
                add_le_add_right (mul_le_mul_of_nonneg_right (HAbd n) (abs_nonneg _)) _
  ... < A * (ε / (2 * A)) + |a n - l| * |m| :
               add_lt_add_right (mul_lt_mul_of_pos_left (HNB n (le_trans (le_max_right _ _) Hn)) HApos) _
  ... ≤ A * (ε / (2 * A)) + (ε / (2 * B)) * |m| :
               add_le_add_left (mul_le_mul_of_nonneg_right (le_of_lt $ HNA n $ le_trans (le_max_left _ _) Hn) (abs_nonneg _)) _
  ... ≤ A * (ε / (2 * A)) + (ε / (2 * B)) * B :
               add_le_add_left (mul_le_mul_of_nonneg_left (limit_bounded_of_bounded h2 HBbd) $ le_of_lt $ div_pos Hε (by linarith)) _
  ... = ε / 2 + (ε / (2 * B)) * B : by rw [←div_div_eq_div_mul,mul_div_cancel' _ (show A ≠ 0, by intro h;rw h at HApos;linarith)]
  ... = ε / 2 + ε / 2 : by rw [←div_div_eq_div_mul,div_mul_cancel _ (show B ≠ 0, by intro h;rw h at HBpos;linarith)]
  ... = ε : by ring 
end

-- If aₙ → l and bₙ → m, and aₙ ≤ bₙ for all n, then l ≤ m
theorem tendsto_le_of_le (a : ℕ → ℝ) (b : ℕ → ℝ)
  (l : ℝ) (m : ℝ) (hl : is_limit a l) (hm : is_limit b m) 
  (hle : ∀ n, a n ≤ b n) : l ≤ m :=
begin
  -- Assume for a contradiction that m < l
  apply le_of_not_lt,
  intro hlt,
  -- Let ε be (l - m) / 2...
  let ε := (l - m) /2,
  -- ...and note that it's positive
  have Hε : ε > 0 := show (l - m) / 2 > 0 , by linarith,
  -- Choose Na s.t.  |aₙ - l| < ε for n ≥ Na
  cases hl ε Hε with Na HNa,
  have Hε : ε > 0 := show (l - m) / 2 > 0 , by linarith,
  -- Choose Nb s.t.  |bₙ - m| < ε for n ≥ Nb
  cases hm ε Hε with Nb HNb,
  -- let N be the max of Na and Nb...
  let N := max Na Nb,
  -- ...and note N ≥ Na and N ≥ Nb,
  have HNa' : Na ≤ N := le_max_left _ _,
  have HNb' : Nb ≤ N := le_max_right _ _,
  -- ... so |a_N - l| < ε and |b_N - m| < ε
  have Hl' : |a N - l| < ε := HNa N HNa',
  have Hm' : |b N - m| < ε := HNb N HNb',
  -- ... and also a_N ≤ b_N.
  have HN : a N ≤ b N := hle N,
  -- This is probably a contradiction.
  have Hε : ε = (l - m) / 2 := rfl,
  revert Hl' Hm',
  unfold abs,unfold max,split_ifs;intros;linarith
end
