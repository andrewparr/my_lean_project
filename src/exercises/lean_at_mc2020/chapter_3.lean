-- 3. Infinitely Many Primes

-- Today we will prove that there are infinitely many primes using mathlib library.
-- Our focus will be on how to use the library to prove more complicated theorems. 

-- 3.1. Equality

import tactic data.nat.basic
open nat

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
