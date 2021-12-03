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



