import tactic
import data.nat.basic
import data.nat.prime

noncomputable theory
open_locale classical

open nat

-- 4. Sqrt 2 is irrational

-- 4.1. Implicit arguments

/-
Consider the following theorem which says that the smallest non-trivial factor of a natural
number greater than 1 is a prime number.

 `min_fac_prime : n ≠ 1 → n.min_fac.prime`

It needs only one argument, namely a term of type `n ≠ 1`. But we have not told Lean what `n` is!
That’s because if we pass a term, say `hp : 2 ≠ 1` to `min_fac_prime` then from `hp` Lean can infer
that `n = 2`. `n` is called an implicit argument.
An argument is made implicit by using curly brackets { and } instead of the usual ( and ) while
defining the theorem.

  `theorem min_fac_prime {n : ℕ} (hne1 : n ≠ 1) : n.min_fac.prime := ...`

Sometimes the notation is ambiguous and Lean is unable to infer the implicit arguments.
In such a case, you can force all the arguments to become explicit by putting an `@` symbol in from
on the theorem. For example,

  `@min_fac_prime : (n : ℕ) → n ≠ 1 → n.min_fac.prime`

Use this sparingly as this makes the proof very hard to read and debug
-/

-- 4.2. The two haves

/-
We have seen two slightly different variants of the have tactic.

  `have hq := ...`
  `have hq : ...`

In the first case, we are defining `hq` to be the term on the right hand side.
In the second case, we are saying that we do not know what the term hq is but we know it’s type.

Let’s consider the example of `min_fac_prime` again. Suppose we want to conclude that the smallest
factor of 10 is a prime. We will need a term of type `10.min_fac.prime`. If this is the target,
we can use apply `min_fac_prime`,. If not, we need a proof of `10 ≠ 1` to provide as input to
`min_fac_prime`. For this we’ll use

  `have ten_ne_zero : 10 ≠ 1,`

which will open up a goal with target `10 ≠ 1`. If on the other hand, you have another hypothesis,
say `f : P →  (10 ≠ 1)` and a term `hp : P`, then

  `have ten_ne_zero := f(hp)`

will immediately create a term of type `10 ≠ 1`. More generally, remember that

    “:=” stands for definition. x := ... means that x is defined to be the right hand side.

    “:” is a way of specifying type. x : ... means that the type of x is the right hand side.

    “=” is only ever used in propositions and has nothing to do with terms or types.

-/

-- 4.3. Sqrt(2) is irrational

/-
We will show that there do not exist non-zero natural numbers `m` and `n` such that

  `2 * m ^ 2 = n ^ 2  -- (*)`

The crux of the proof is very easy. You simply have to start with the assumption that `m` and `n`
are coprime without any loss of generality and derive a contradiction.
But proving that without a loss of generality is a valid argument requires quite a bit of effort.
This proof is broken down into several parts. The first two parts prove (*) assuming that `m` and `n`
are coprime. The rest of the parts prove the without loss of generality part.

For this problem you’ll need the following definitions.

        `m.gcd n : ℕ is the gcd of m and n.`

        `m.coprime n is defined to be the proposition m.gcd n = 1.`

The descriptions of the library theorems that you’ll be needing are included as comments. Have fun!
-/

-- 4.3.1. Lemmas for proving (*) assuming m and n are coprime.


/-
prime.dvd_of_dvd_pow : ∀ {p m n : ℕ}, p.prime → p ∣ m ^ n → p ∣ m
-/
lemma two_dvd_of_two_dvd_sq {k : ℕ} (hk : 2 ∣ k ^ 2) : 2 ∣ k :=
begin
  apply prime.dvd_of_dvd_pow,
  -- norm_num does most of the work here
  -- { norm_num, },
  { exact nat.prime_two }, -- alternatively the goal of prime 2 is already in mathlib
  exact hk,
end

-- to switch the target from ``P = Q`` to ``Q = P``,
-- use the tactic ``symmetry,``
lemma division_lemma_n {m n : ℕ}
  (hmn : 2 * m ^ 2 = n ^ 2)
: 2 ∣ n :=
begin
  -- Here the goal is 2 | n and what we just proved above is that
  -- given the hypothesis that 2 ∣ k^2 we have 2 ∣ k
  -- so from our goal of 2 ∣ n, we apply this to get the goal of
  -- 2 ∣ n^2
  apply two_dvd_of_two_dvd_sq,
  -- Here we have to remember that the division is defined as `m ∣ n := ∃ k : ℕ, m * k = n`
  -- so our goal of 2 ∣ n^2 is to show the existance of a k such that 2 * k = n^2
  -- out hypothesis tells us this is simply m^2
  use m^2,
  -- Goal is now the symmetry of hmn, so lets use the symmetry hint followed by exact.
  symmetry,
  exact hmn,
end

lemma div_2 {m n : ℕ} (hnm : 2 * m = 2 * n) : (m = n) :=
begin
  linarith,
end

lemma division_lemma_m {m n : ℕ} (hmn : 2 * m ^ 2 = n ^ 2) : 2 ∣ m :=
begin
  apply two_dvd_of_two_dvd_sq,
  -- goal is now 2 ∣ m^2 , which is is find k such that 2 * k = m^2
  -- We need to use the division_lemma_n which will take a hypothesis of hmn
  -- and produce a proof that 2 | n
  have hn := division_lemma_n hmn, -- we now have hn : 2 ∣ n
  -- since 2 ∣ n, n must be some multiple of 2 and so performing cases...
  cases hn with k hk,
  -- gives hk : n = 2 * k
  -- we now know ...n = 2k, and 2m^2 = n^2 = (2k)^2 = 4 * k^2
  -- and so m^2 = 2 * k^2 and so the k we want is k^2
  use k^2,
  -- goal is now m^2 = 2 * k^2
  -- we can't proove this directly
  -- but we have
  --   hmn : 2 * m^2 = n^2
  --   hk  : n = 2 * k
  -- and so
  rw hk at hmn,
  -- gives, hmn : 2 * m^2 = (2*k)^2
  -- which linarith can solve
  linarith,
end

-- 4.3.2. Prove (*) assuming m and n are coprime.

/-
theorem nat.not_coprime_of_dvd_of_dvd  : 1 < d → d ∣ m → d ∣ n → ¬m.coprime n
-/

theorem sqrt2_irrational' : ¬ ∃ (m n : ℕ), 2 * m^2 = n^2 ∧ m.coprime n :=
begin
  -- goal is ¬∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m.coprime n
  by_contradiction,
  -- now have h : ∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m.coprime n
  -- and goal is false
  -- rcases on this h gives
  --    m n : ℕ
  --   hmn : 2 * m ^ 2 = n ^ 2
  --   h_cop : m.coprime n
  rcases h with ⟨m, n, hmn, h_cop⟩,
  -- rcases is a way of doing cases iteratively
  -- you get the brackets by typing ``\langle`` and ``\rangle``
  -- We need to use the proofs above
  -- using the have syntax we're given above
  -- first, the division algorithm gives us  2 ∣ m
  have h_m_even : 2 ∣ m := division_lemma_m(hmn),
  -- we have h_cop : m.coprime m
  -- to apply the not_coprime_of_dvd_of_dvd above we want ¬ m.coprime
  -- so lets use contrapose on it
  contrapose h_cop,
  -- goal is now ¬m.coprime n and so
  -- we can now apply not_coprime_of_dvd_of_dvd
  apply not_coprime_of_dvd_of_dvd,
  -- we now have a number of goals all the ones to the left of the of the ¬m.coprime n in
  -- the definition of theorem nat.not_coprime_of_dvd_of_dvd
  -- so these are 1 < d → d ∣ m → d ∣ n
  {
    -- here the goal is 1 < d, but actually we have 2 ∣ m and so d is 2
    -- the goal is written as 1 < ?m_1
    -- but it's actually 2 or 1+1 and this is
    exact lt_add_one 1,
  },
  {
    -- goal here is 1 + 1 | m, and this is
    exact h_m_even,
  },
  {
    -- goal here is 1 + 1 ∣ n, this is exactly the division_lemma_m just proved on hmn
    exact division_lemma_n hmn,
  }
end


-- alternatively
example : ¬ ∃ (m n : ℕ), 2 * m^2 = n^2 ∧ m.coprime n :=
begin
  -- goal is ¬∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m.coprime n
  by_contradiction,
  -- now have h : ∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ m.coprime n
  -- and goal is false
  -- rcases on this h gives
  --    m n : ℕ
  --   hmn : 2 * m ^ 2 = n ^ 2
  --   h_cop : m.coprime n
  rcases h with ⟨m, n, hmn, h_cop⟩,
  -- rcases is a way of doing cases iteratively
  -- you get the brackets by typing ``\langle`` and ``\rangle``
  -- We need to use the proofs above
  -- using the have syntax we're given above
  -- first, the division_lemma_m gives us  2 ∣ m
  have h_m_even : 2 ∣ m := division_lemma_m(hmn),
  -- secondly, the division_lemma_n gives us 2 ∣ n
  have h_n_even : 2 ∣ n := division_lemma_n(hmn),
  -- we have h_cop : m.coprime m
  -- to apply the not_coprime_of_dvd_of_dvd above we want ¬ m.coprime
  -- so lets use contrapose on it
  contrapose h_cop,
  -- goal is now ¬m.coprime n and so
  -- we can now apply not_coprime_of_dvd_of_dvd
  apply not_coprime_of_dvd_of_dvd,
  -- we now have a number of goals all the ones to the left of the of the ¬m.coprime n in
  -- the definition of theorem nat.not_coprime_of_dvd_of_dvd
  -- so these are 1 < d → d ∣ m → d ∣ n
  exact lt_add_one 1,
  exact h_m_even,
  exact h_n_even,
end

-- 4.3.3. Lemmas for proving (*) assuming m ≠ 0

lemma ne_zero_ge_zero {n : ℕ} (hne : n ≠ 0) : (0 < n) :=
begin
  -- this following line is given in mc2020 notes
  contrapose! hne,
  -- linarith then closes the goal
  --linarith,
  -- but a library_search finds the exact mathlib proof.
  exact le_zero_iff.mp hne,
end

/-
nat.pow_pos : ∀ {p : ℕ}, 0 < p → ∀ (n : ℕ), 0 < p ^ n
-/
lemma ge_zero_sq_ge_zero {n : ℕ} (hne : 0 < n) : (0 < n^2)
:=
begin
  -- again library_search is useful here to find the exact proof in mathlib
  -- exact pow_pos hne 2,
  -- for a more manual process.
  cases n, -- n is either 0 or n.succ for some other n
  {
    -- if n is zero
    rw zero_pow,
    exact hne,
    exact zero_lt_two,
  },
  {
    -- if n is n.succ for some other n
    rw pow_succ,
    rw pow_one;
    exact mul_pos hne hne,
  }
end

lemma cancellation_lemma {k m n : ℕ} (hk_pos : 0 < k^2) (hmn : 2 * (m * k) ^ 2 = (n * k) ^ 2) : 2 * m ^ 2 = n ^ 2 :=
begin
  -- this following line is given in the mc2020 notes.
  apply (nat.mul_left_inj hk_pos).mp,
  -- mc2020 notes also give the following two lines, but these fail to prove this lemma
  --ring at *,
  --exact hmn,
  -- however linarith is sufficient.
  linarith,
end

-- 4.3.4. Prove (*) assuming m ≠ 0

/-
gcd_pos_of_pos_left : ∀ {m : ℕ} (n : ℕ), 0 < m → 0 < m.gcd n
gcd_pos_of_pos_right : ∀ (m : ℕ) {n : ℕ}, 0 < n → 0 < m.gcd n
exists_coprime : ∀ {m n : ℕ}, 0 < m.gcd n → (∃ (m' n' : ℕ), m'.coprime n' ∧ m = m' * m.gcd n ∧ n = n' * m.gcd n)
-/
theorem wlog_coprime : (∃ (m n : ℕ), 2 * m^2 = n^2 ∧ m ≠ 0 ) → (∃ (m' n' : ℕ), 2 * m'^2 = n'^2 ∧ m'.coprime n' ) :=
begin
  intro key,
  rcases key with ⟨m, n, hmn, hme0⟩,
  set k := m.gcd n with hk,
  -- might be useful to declutter
  -- you can replace all the ``m.gcd n`` with ``k`` using ``rw ←hk,`` if needed
  -- The lines above this one are given in the mc2020 notes.
  have hmge : 0 < m := by exact ne.bot_lt hme0,
  have hge : 0 < m.gcd n := by exact pos_of_dvd_of_pos (gcd_dvd_left m n) hmge,
  have he := exists_coprime(hge),
  cases he,
  set m' := m / k,
  set n' := n / k;
  cases he_h with h1 h2,
  use (he_w * k),
  use (h1 * k),
  cases h2 with h2_1 h2_2,
  rw ← hk at h2_2,
  rw h2_2.1 at hmn,
  rw h2_2.2 at hmn,
  split,
  exact hmn,
  -- need to prove  (he_w * k).coprime (h1 * k)
  -- this can't be right (he_w * k) is coprime with (h1 * k) only if k is one
  repeat {sorry},
end


theorem sqrt2_irrational'' : ¬ ∃ (m n : ℕ), 2 * m^2 = n^2 ∧ m ≠ 0 :=
begin
  sorry,
end
