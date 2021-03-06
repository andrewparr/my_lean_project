import tactic data.nat.basic data.nat.prime
open nat
open function

-- 3. Infinitely Many Primes

-- Today we will prove that there are infinitely many primes using mathlib library.
-- Our focus will be on how to use the library to prove more complicated theorems.

-- 3.1. Equality

/--------------------------------------------------------------------------

  ``rw``

    If ``f`` is a term of type ``P = Q`` (or ``P ↔ Q``), then
    ``rw f`` replaces ``P`` with ``Q`` in the target.
    Other variants:
      ``rw f at hp``, ``rw ←f``, ``rw ←f at hr``.

  Delete the ``sorry,`` below and replace them with a legitimate proof.

  --------------------------------------------------------------------------/

theorem add_self_self_eq_double(x : ℕ) : x + x = 2 * x :=
begin
  ring,
end

/-
For the following problem, use
  mul_comm a b : a * b = b * a
-/

example (a b c d : ℕ)
  (hyp : c = d * a + b)
  (hyp' : b = a * d)
: c = 2 * (a * d) :=
begin
  rw hyp,
  rw hyp',
  ring,
end

-- The above was solved, but comment above says to use mul_comm, so here's another go
example (a b c d : ℕ)
  (hyp : c = d * a + b)
  (hyp' : b = a * d)
: c = 2 * (a * d) :=
begin
  -- In order to use mul_comm I had to eliminate the 2 * first by using two_mul
  rw two_mul,
  rw hyp,
  rw hyp',
  rw mul_comm, -- then can use mul_comm with tries refl afterwards and this solves the goal.
end

/-
For the following problem, use
  sub_self (x : ℕ) : x - x = 0
-/

example (a b c d : ℕ)
  (hyp : c = b * a - d)
  (hyp' : d = a * b)
: c = 0 :=
begin
  rw hyp,
  rw hyp',
  -- goal is now b * a - a * b, so we can't yet apply rw sub_self
  rw mul_comm, -- now have a * b - a * b, but
  -- rw ← hyp', -- this replaces both sets of a * b to d
  -- rw nat.sub_self d,
  rw nat.sub_self _, -- you don't actually need to reduce the a * b to d
  -- I'm not sure why I needed nat.sub_self. But just using rw sub_self didn't work.
end

-- 3.1.1. Surjective functions

--  Recall that a function f : X → Y is surjective if for every y : Y there exists a term x : X such that
--  f(x) = y. In type theory, for every function f we can define a corresponding proposition
--  surjective (f) := ∀ y, ∃ x, f x = y and a function being surjective is equivalent to saying
--  that the proposition surjective(f) is inhabited.

/--------------------------------------------------------------------------

``unfold``

  If it gets hard to keep track of the definition of ``surjective``,
  you can use ``unfold surjective,`` or ``unfold surjective at h,``
  to get rid of it.

Delete the ``sorry,`` below and replace them with a legitimate proof.

--------------------------------------------------------------------------/

variables X Y Z : Type
variables (f : X → Y) (g : Y → Z)

/-
surjective (f : X → Y) := ∀ y, ∃ x, f x = y
-/

example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
begin
  -- These unfolds aren't necessary, bu they help to see the proof.
  unfold surjective,
  unfold surjective at hf,
  unfold surjective at hg,
  -- our goal is ∀ (b : Z) .., so we can introduce an arbitary z.
  intro z,
  -- we can now use hg with this z, to give use a y : Y
  -- we do this be creating the hypothesis that there must exist a y : Y
  have h1 : ∃ y : Y, g y = z, from hg z,
  -- and then uses cases on this hypothesis to obtain an arbitary y : Y
  cases h1 with y,
  -- similar as above, we now use hf with this y to first creat the hypothesis
  -- that an x : X must exist
  have h2 : ∃ x : X, f x = y, from hf y,
  -- then use cases to obtiain an arbitary x : X
  cases h2 with x,
  -- finally our goal is in sight, the goal is to prove
  -- ∃ (a : X), (g ∘ f) a = z
  -- and we can just use the x : X that we have proved exists above.
  use x,
  -- the finish tatic will now finish this proof.
  finish,
  -- If you use suggest rather than finish above, it suggest the following to finish the proof.
  -- exact (eq.congr_right h1_h).mp (congr_arg g (eq.symm h2_h)).symm,
 end

example
  (hgf : surjective (g ∘ f))
  : surjective g :=
begin
  -- The following proof we'll use is
  -- take any z ∈ Z,
  -- since g ∘ f is surjective, ∃ x ∈ X, s.t. (g ∘ f) x = z,
  -- so g(f(x)) = z,
  -- set y = f(x) , note y ∈ Y.
  -- then, g(b) = g(f(x)) = y
  -- see https://www.youtube.com/watch?v=bTKOC3Rst8c

  -- Again these unfolds aren't required but they help.
  unfold surjective,
  unfold surjective at hgf,
  -- take any z : Z
  intro z,
  -- since g ∘ f is surjective, ∃ x ∈ X, s.t. (g ∘ f) x = z,
  have h1 : ∃ (a : X), (g ∘ f) a = z, from hgf z,
  -- so (g ∘ f) x = z
  cases h1 with x h2,

  -- In order to set y = f x, we first prove that there exists a y : Y
  have h2 : ∃ (y : Y), y = f x :=
  begin
    use f x,
  end,
  -- this this we have our y.
  cases h2 with y h3,

  -- our proof is these exists, and y is the value to use.
  use y,
  -- hint, tells use finish will finish the goal
  --finish,
  -- But this doesn't teach us anything. These two rewrites will close the goal.
  rw ← h2,
  rw h3,
end



-- 3.2. Creating subgoals
/--------------------------------------------------------------------------

Often when we write a long proof in math, we break it up into simpler problems. This is done in
Lean using the have tactic.

``have``

  ``have hp : P,`` creates a new goal with target ``P`` and
  adds ``hp : P`` as a hypothesis to the original goal.


have is crucial for being able to use theorems from the library. To use these theorems you have to
create terms that match the hypothesis exactly. Consider the following example. The type n > 0
is not the same as 0 < n. If you need a term of type ``n > 0 `` and you only have ``hn : 0 < n``,
then you can use ``have hn2 : n > 0, linarith,`` and you will have constructed a term hn2 of type n > 0.

Warning: If you need to type the divisibility symbol, type \mid. This is not the vertical line
on your keyboard.

You'll need the following theorem from the library:

nat.dvd_sub : n ≤ m → k ∣ m → k ∣ n → k ∣ m - n

   (Note that you don't need to provide n m k as inputs to dvd_sub
   Lean can infer these from the rest of the expression.
   More on this tomorrow.)

Delete the ``sorry,`` below and replace it with a legitimate proof.

--------------------------------------------------------------------------/

theorem dvd_sub_one {p a : ℕ} : (p ∣ a) → (p ∣ a + 1) → (p ∣ 1) :=
begin
  intro h1, -- intro h1 : p ∣ a
  intro h2, -- intro h2 : p ∣ a + 1
  -- Our proof strategy is the to apply the proof
  --    nat.dvd_sub : n ≤ m → k ∣ m → k ∣ n → k ∣ m - n
  -- for this we have the follow
  --     n = a
  --     m = a + 1
  --     k = p
  -- so
  -- nat.dvd_sub : a ≤ a + 1 → p ∣ a + 1 → p ∣ a → p ∣ a + 1 - a
  -- Thus before we can apply this, we need to have these hypotheses
  --have h3 : p ∣ a + 1 - a := begin
  have h3 : p ∣ a + 1 - a := begin
    refine dvd_sub _ h2 h1,
    linarith,
  end,
  -- This is showing off the power of finish, but it teaches us less.
  -- finish,
  -- suggest gives the folowing one line proof, which tells us more but is not simple
  -- exact (nat.dvd_add_right h1).mp h2,
  -- A far more wordy way to prove it, but it teaches us much more.
  -- First show that a + 1 - a = 1 which is easily prooved by norm_num
  have h4 : a + 1 - a = 1, by norm_num,
  -- rw this at h3 to give
  -- h3 : p ∣ 1
  rw h4 at h3,
  -- our goal is h3, one of our assumptions and so we are done.
  -- assumption,
  -- exact h3 would also do and is possibly cleaner.
  exact h3,
end

-- 3.3. Infinitely many primes

-- We’ll now prove that there are infinitely many primes. The strategy is to show that there is a
-- prime greater than n, for every natural number n. We will choose this prime to be smallest
-- non-trivial factor of n! + 1. We’ll need the following definitions and theorems from the library.

-- From aobve, `dvd_sub_one : (p ∣ a) → (p ∣ a + 1) → (p ∣ 1)`

-- Primes
--        `m ∣ n := ∃ k : ℕ, m * k = n`
--        `m.prime :=  2 ≤ p ∧ (∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p)`
--        `prime.not_dvd_one : (prime p) → ¬ p ∣ 1`

-- Factorials
--        `n.fact := n!  --n factorial`
--        `fact_pos : ∀ (n : ℕ), 0 < n.fact`
--        `dvd_fact : 0 < m → m ≤ n → m ∣ n.fact`

-- Smallest factor
--        `n.min_fac := smallest non-trivial factor of n`
--        `min_fac_prime : n ≠ 1 → n.min_fac.prime`
--        `min_fac_pos : ∀ (n : ℕ), 0 < n.min_fac`
--        `min_fac_dvd : ∀ (n : ℕ), n.min_fac ∣ n`

noncomputable theory
open_locale classical

theorem exists_infinite_primes (n : ℕ) : ∃ p, prime p ∧ p ≥ n :=
begin
  -- This first line was given with no explanation.
  set p:= (n.factorial + 1).min_fac,

  -- Our first goal is to prove this this p is prime. To do this we'll use min_fac_prime
  -- but from notes above, this requies a proof that (n.factorial + 1) ≠ 1
  have h : factorial n + 1 ≠ 1 := begin
    apply ne_of_gt,
    apply succ_lt_succ,
    apply factorial_pos _,
  end,
  -- we can now prove p is prime as required.
  have pp : prime p, from min_fac_prime h,
  -- we now want to prove that p ≥ n
  have np : p ≥ n := begin
    by_contradiction,
    have h₁ : p ∣ factorial n + 1 := min_fac_dvd (factorial n + 1),
    have h₂ : p ∣ factorial n :=
    begin
      refine pp.dvd_factorial.mpr _,
      exact le_of_not_ge h,
    end,
    have h : p ∣ 1 := dvd_sub_one h₂ h₁,
    exact prime.not_dvd_one pp h,
  end,
  -- finally, the proof is straightforward.
  -- The goal is an existance proof, and p is it. So use p is the logical step
  use p,
  -- goal is now prime p ∧ p ≥ n which is exactly pp ∧ np
  exact ⟨pp, np⟩,
end

-- alternative proof : Ref: https://www.youtube.com/watch?v=b59fpAJ8Mfs
theorem infinitude_of_primes : ∀ n, ∃ p ≥ n, prime p :=
begin
  -- this proof says something for all n : N, we let n be an arbitary ℕ
  intro n,

  let m := factorial n + 1,
  let p := min_fac m,

  have pp : prime p :=
  begin
    refine min_fac_prime _,
    have h : factorial n > 0 := factorial_pos n,
    linarith,
  end,

  use p,
  split,
  {
    by_contradiction,
    have h₁ : p ∣ factorial n + 1 := min_fac_dvd m,
    have h₂ : p ∣ factorial n :=
    begin
      refine pp.dvd_factorial.mpr _,
      exact le_of_not_ge h,
    end,
    have h : p ∣ 1 := dvd_sub_one h₂ h₁,
    exact prime.not_dvd_one pp h,
  },
  {
    exact pp,
  }
end

-- For reference, here's a copy of the proof in mathlib
theorem exists_infinite_primes' (n : ℕ) : ∃ p, n ≤ p ∧ prime p :=
let p := min_fac (factorial n + 1) in
have f1 : factorial n + 1 ≠ 1, from ne_of_gt $ succ_lt_succ $ factorial_pos _,
have pp : prime p, from min_fac_prime f1,
have np : n ≤ p, from le_of_not_ge $ λ h,
  have h₁ : p ∣ factorial n, from dvd_factorial (min_fac_pos _) h,
  have h₂ : p ∣ 1, from (nat.dvd_add_iff_right h₁).2 (min_fac_dvd _),
  pp.not_dvd_one h₂,
⟨p, np, pp⟩
