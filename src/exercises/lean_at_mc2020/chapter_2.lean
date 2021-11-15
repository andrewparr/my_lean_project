import tactic
-- the next two lines let us use the by_cases tactic without trouble
noncomputable theory
open_locale classical

-- 2.1.2. Proofs as functions

-- Every time you successfully construct a proof of a theorem say
theorem tautology (P : Prop) : P → P :=
begin
  intro hp,
  exact hp,
end

-- Lean constructs a proof term tautology : ∀ P : Prop, P → P (you can see this by typing #check tautology).
#check tautology


-- Once constructed, any term can be used in a later proof. For example,
example (P Q : Prop) : (P → Q) → (P → Q) :=
begin
  exact tautology (P → Q),
end

-- This is how Lean simulates mathematics.
-- Every time you prove a theorem using tactics a proof term gets created.
-- Because of proof irrelevance, Lean forgets the exact content of the proof and only remembers its type.
-- All the proof terms can then be used in later proofs.
-- All of this falls under the giant umbrella of the Curry–Howard correspondence.

-- 2.2 And / Or

/--------------------------------------------------------------------------

``cases``

  ``cases`` is a general tactic that breaks up complicated terms.
  If ``hpq`` is a term of type ``P ∧ Q`` or ``P ∨ Q`` or ``P ↔ Q``, then use
  ``cases hpq with hp hq,``.

``split``

  If the target of the current goal is ``P ∧ Q`` or ``P ↔ Q``, then use
  ``split,``.

``left``/``right``

  If the target of the current goal is ``P ∨ Q``, then use
  either ``left,`` or ``right,`` (choose wisely).

``exfalso``

  Changes the target of the current goal to ``false``.

Delete the ``sorry,`` below and replace them with a legitimate proof.

--------------------------------------------------------------------------/

example (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
  intro hpq,
  cases hpq with hp hq,
  split,
  exact hq,
  exact hp,
end

example (P Q : Prop) : P ∨ Q → Q ∨ P :=
begin
  intro hpq,
  cases hpq with hp hq,
  {
    right,
    exact hp,
  }, {
    left,
    exact hq,
  }
end

example (P Q R : Prop) : P ∧ false ↔ false :=
begin
  split,
  {
    -- here we need to prove P ∧ false → false
    intro hPnFalse,
    cases hPnFalse with hp hfalse,
    exact hfalse,
  },
  {
      -- here we need to prove false → P ∧ false
      intro h,
      exfalso,
      exact h,
  }
end

theorem principle_of_explosion (P Q : Prop) : P ∧ ¬ P → Q :=
begin
  intro hPnP,
  cases hPnP with hP hnP,
  exfalso,
  apply hnP,
  exact hP,
end

-- 2.3. Quantifiers

-- 2.3.1. Barber paradox

/--------------------------------------------------------------------------

``by_cases``

  If ``P`` is a proposition, then ``by_cases P,`` creates two goals,
    the first with a hypothesis ``hp: P`` and
    second with a hypothesis ``hp: ¬ P``.

Delete the ``sorry,`` below and replace them with a legitimate proof.

--------------------------------------------------------------------------/

-- men is type.
-- x : men means x is a man in the town
-- shaves x y is inhabited if x shaves y

variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

/--------------------------------------------------------------------------
The claim is that in a certain town there is a (male) barber that shaves all
the men who do not shave themselves. (Why is this a paradox?) Prove that this
is a contradiction.

I found this complicated - the outline of the proof is as follows:

Use proof by contradiction, so first assume
  shaves barber x ↔ ¬ shaves x x
I.e. we are assuming both
  p1: shaves barber x → ¬ shaves x x
and
  p2: ¬ shaves x x → shaves barber x

assume shaves barber x
then by p1, we also have ¬ shaves x x
but barber is a man and this means ¬ shaves barber x
which is a contradiction.
This contradiction means the assumption above is invalid and so ¬ assume shaves barber x

Now assuming
¬ shaves barber x
then by p2 we must have shaves barber x
this is also a contraction.

This second contraction, means the initial assumption was wrong and so
this completes the proof.
---------------------------------------------------------------------------/

example : ¬ (∀ x : men, shaves barber x ↔ ¬ shaves x x) :=
begin
  -- we prove by contradiction, so assume it's true
  by_contradiction,
  -- x is a barber
  have x := barber,
  -- h is currently (x : men), shaves barber x ↔ ¬shaves x x
  -- so lets specialize to just get
  -- h : h: shaves barber barber ↔ ¬shaves barber barber
  specialize h barber,
  -- since h is a ↔ hypothesis, we do cases on it.
  cases h with p1 p2,
  by_cases shaves barber barber,
  {
    -- goal here is false, and have h : shaves barber barber
    -- show false, from p1 h h, -- this is one line that will solve the goal
    -- apply p1 h h, -- this line also on it's own solves the goal
    apply p1 h,
    exact h,
    -- remember, goal was false and
    -- ¬ shaves barber barber is the same as shaves barber barber → false
    -- so applying p1: shaves barber barber → ¬shaves barber barber
    -- gives shaves barber barber and this is exactly h
  },
  {
    -- goal here is false and have h : ¬ shaves barber barber
    -- show false, from h (p2 h), -- solves this is onle line
    -- apply h (p2 h), -- this also solves the goal in one line
    apply h,
    apply p2,
    exact h,
    -- again goal was false, and h is
    -- ¬shaves barber barber which is the same as shaves barber barber → false
    -- so we can apply h on false to give goal of
    -- shaves barber barber
    -- now p2 is  ¬shaves barber barber → shaves barber barber
    -- so after applying this, we get goal of ¬ shaves barber barber
    -- and this is exactly h.

  }
end


--- temp, the following are various proofs found on the internet that I used to help me to write the proof above.

-- standalone
-- See https://github.com/hyponymous/theorem-proving-in-lean-solutions/blob/a95320ae81c90c1b15da04574602cd378794400d/4.6.3.lean
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
have hparadox : shaves barber barber ↔ ¬shaves barber barber, from
    (h barber),
have hn_self_shave : ¬shaves barber barber, from
    (show shaves barber barber → false, from
        assume h_self_shave : shaves barber barber,
        absurd h_self_shave (hparadox.mp h_self_shave)),
absurd (hparadox.mpr hn_self_shave) hn_self_shave


example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
begin
  -- goal is false
  have hparadox : shaves barber barber ↔ ¬shaves barber barber, from
      (h barber),
  -- now have hypothesis : shaves barber barber ↔ ¬shaves barber barber
  have hn_self_shave : ¬shaves barber barber, from
      (show shaves barber barber → false, from
          assume h_self_shave : shaves barber barber,
          absurd h_self_shave (hparadox.mp h_self_shave)),
  -- now also have hypotheisis :  ¬shaves barber barber
  -- this line comes from suggest, but what is it doing ?
  exact (not_congr hparadox).mp hn_self_shave hn_self_shave,
  --absurd (hparadox.mpr hn_self_shave) hn_self_shave
end

-- another proof from zulip chat
variables (Man : Type) (tshaves : Man → Man → Prop)
theorem NoSuchBarber ( h : ∃ x : Man,  ∀ y : Man, tshaves x y ↔ ¬ tshaves y y )
: false :=
    exists.elim h
  ( assume barber,
    begin
        intro h,
        have hbarbermpr : ¬tshaves barber barber → tshaves barber barber,
            from iff.mpr (h barber),
        have hbarbermp  : tshaves barber barber → ¬tshaves barber barber,
            from iff.mp (h barber),
        have nsbb : ¬tshaves barber barber, from
            assume sbb : tshaves barber barber,
            show false, from hbarbermp sbb sbb,
        show false, from nsbb (hbarbermpr nsbb)
    end
)
#print NoSuchBarber


-- from Kevin Buzzard
--variables (Man : Type) (shaves : Man → Man → Prop)
theorem NoSuchBarber2 ( h : ∃ x : Man,  ∀ y : Man, tshaves x y ↔ ¬ tshaves y y )
: false :=
    exists.elim h
  ( assume barber,
    begin
        intro h2, -- I don't want two hypotheses called h
        have hbarber := h2 barber, -- human-generated good idea
        tauto!, -- computer can finish it off
    end
)


-- trying to rewrite this
-- theorem NoSuchBarber ( h : ∃ x : Man,  ∀ y : Man, tshaves x y ↔ ¬ tshaves y y )
example : ¬ (∀ x : men, shaves barber x ↔ ¬ shaves x x) :=
begin
  by_contradiction,
  have x := barber,
  specialize h barber,
  cases h with p1 p2,
  by_cases shaves barber barber,
  {
    show false, from p1 h h,
  },
  {
    show false, from h (p2 h),
  }
end

-- 2.3.2. Mathcampers singing paradox

-- Assume that the main lounge is non-empty. At a fixed moment in time,
-- there is someone in the lounge such that, if they are singing, then
-- everyone in the lounge is singing.

-- Note: This paradox is a rewording of the Drinker paradox.
-- See https://en.wikipedia.org/wiki/Drinker_paradox
-- "There is someone in the pub such that, if he is drinking, then everyone in the pub is drinking."

-- The outline of the proof from wikipedia.
-- The proof begins by recognizing it is true that either:
--  [1] everyone in the pub is drinking, or
--  [2] at least one person in the pub is not drinking.
-- Consequently, there are two cases to consider:
-- [1] Suppose everyone is drinking.
--     For any particular person, it cannot be wrong to say that if that particular person is drinking,
--     then everyone in the pub is drinking—because everyone is drinking.
--     Because everyone is drinking, then that one person must drink because when that person drinks everybody drinks
--     everybody includes that person.
-- [2] Otherwise at least one person is not drinking.
--     For any nondrinking person, the statement if that particular person is drinking,
--     then everyone in the pub is drinking is formally true:
--     its antecedent ("that particular person is drinking") is false, therefore the statement is true due to the
--     nature of material implication in formal logic, which states that
--     "If P, then Q" is always true if P is false.

/--------------------------------------------------------------------------

``by_cases``

  If ``P`` is a proposition, then ``by_cases P,`` creates two goals,
    the first with a hypothesis ``hp: P`` and
    second with a hypothesis ``hp: ¬ P``.

Delete the ``sorry,`` below and replace them with a legitimate proof.

--------------------------------------------------------------------------/

-- camper is a type.
-- If x : camper then x is a camper in the main lounge.
-- singing(x) is inhabited if x is singing

theorem math_campers_singing_paradox
  (camper : Type)
  (singing : camper → Prop)
  (alice : camper) -- making sure that there is at least one camper in the lounge
  : ∃ x : camper, (singing x → (∀ y : camper, singing y)) :=
begin
  -- Following the proof structure above we first create two goals,
  -- in which either everyone sings, or someone is not singing
  by_cases (∃ bob : camper, ¬ singing bob),
  {
    -- Here we have the case:
    -- h: ∃ (bob : camper), ¬singing bob
    -- So this is case [2] above, the one where not everyone is singing.
    -- h says there exists a bob such that bob is not singing. The line
    cases h with bob h_bob_not_singing,
    -- gives us the hypotheiss that bob isn't singing
    use bob, -- vacuously proving the goal.
  },
  {
    -- Here we have the case where everyone sings, but it is written with a negative
    -- h: ¬∃ (bob : camper), ¬singing bob
    -- push_neg will sort this out
    push_neg at h,
    -- we now have
    -- h: ∀ (bob : camper), singing bob
    -- Our goal is a "there exists", we only know alice is in the lounge so lets use alice.
    use alice,
    -- goal is now singing alice → ∀ (y : camper), singing y
    -- Which is an implication, so lets use intro.
    intro h2, -- gives h2: singing alice
    -- goal is now : camper), singing y
    -- which is exactly h
    exact h,
  }
end

-- 2.3.3. Relationship conundrum

/--------------------------------------------------------------------------
  A relation r on a type X is a map r : X → X → Prop. We say that x is related to y if r x y is inhabited.

  r is reflexive if ∀ x : X, x is related to itself.
  r is symmetric if ∀ x y : X, x is related to y implies y is related to x.
  r is transitive if ∀ x y z : X, x is related to y and y is related to x implies z is related to z.
  r is connected if for all x : X there is a y : Y such that x is related to y.
---------------------------------------------------------------------------/

-- Show that if a relation is symmetric, transitive, and connected, then it is also reflexive.

variable X : Type

theorem reflexive_of_symmetric_transitive_and_connected
  (r : X → X → Prop)
  (h_symm : ∀ x y : X, r x y → r y x)
  (h_trans : ∀ x y z : X, r x y → r y z → r x z)
  (h_connected : ∀ x, ∃ y, r x y)
: (∀ x : X, r x x) :=
begin
  -- out goal is ∀ x : X, so lets introduce an arbitary x : X
  intro x,
  -- Either r x x is true, or it is false
  by_cases (r x x), {
    -- it's true, we are done as this is simpley h
    exact h,
  }, {
    -- we now need to prove r x x when we know ¬ r x x, which we do by contradiction
    by_contradiction,
    -- from h_connected we know there exists a y such that r x y
    -- by h_conneced is written as ∀ first, so we specialise on the x we have
    specialize h_connected x,
    -- we can now use cases on this to introduce the y : X such that we have h_rxy
    cases h_connected with y h_rxy,
    -- we now have h_rxy : r x y
    -- we have also h_ryx y x := by applying h_symm,
    have h_ryx : r y x := begin
      apply h_symm,
      assumption,
    end,
    -- and h_rxy and h_ryx and h_trans we have h_rxx
    have h_rxx : r x x := begin
      -- first specialize h_trans with the variables we want
      specialize h_trans x y x,
      -- our goal of r x x is now the result of applying this
      exact h_trans h_rxy h_ryx,
    end,
    -- we now have h : ¬ r x x and h_rxx : r x x which is the contradtion we need to prove the goal of false.
    show false, from h h_rxx,
  }
end

-- note: a similar proof from the course notes solutions
theorem reflexive_of_symmetric_and_transitive' (r : ℕ → ℕ → Prop)
  (h_symm : symmetric r)
  (h_trans : transitive r)
  (h_connected : ∀ x, ∃ y, r x y) :
  reflexive r :=
begin
  intro x,
  have hxy := h_connected x,
  cases hxy with y hy,
  apply h_trans hy,
  apply h_symm hy,
end

-- 2.4. Proving “trivial” statements

/--
   In mathlib, divisibility for natural numbers is defined as the following proposition.

   a ∣ b := (∃ k : ℕ, a = b * k)

  For example, 2 | 4 will be a proposition ∃ k : ℕ, 4 = 2 * k.
  Very important. The statement 2 | 4 is not saying that “2 divides 4 is true”.
  It is simply a proposition that requires a proof.

  Similarly, the mathlib library also contains the following definition of prime.
--/

def nat.prime (p : ℕ) : Prop :=
  2 ≤ p                                       -- p is at least 2
  ∧                                           -- and
  ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p            -- if m divides p, then m = 1 or m = p.

/--------------------------------------------------------------------------

  These tactics in Lean are useful for proving trivial proofs such as these.

``norm_num``

  Useful for arithmetic.

``ring``

  Useful for basic algebra.

``linarith``

  Useful for inequalities.

``simp``

  Complex simplifier. Use only to close goals.

Delete the ``sorry,`` below and replace them with a legitimate proof.

--------------------------------------------------------------------------/

example : 1 > 0 :=
begin
  norm_num,
end

example (m a b : ℕ) :  m^2 + (a + b) * m + a * b = (m + a) * (m + b) :=
begin
  ring,
end

example : 101 ∣ 2020 :=
begin
  norm_num,
end


example : nat.prime 101 :=
begin
  -- remember nat.prime is defined as two propositions joined with an and
  split, {
    -- first goal is just to prove 2 ≤ 101.
    norm_num,
  }, {
    -- second goal is prove that ∀ m | 101, either m = 1 ∨ m = 101
    intro m, -- let m be the arbitary natural number,
    intro h,
    cases h with k,
    -- either m = 1, or it isn't
    by_cases h_m_ne_1 : m = 1,
    {
      -- if m = 1, this matches the lhs of our goal
      left, assumption,
    },
    -- we now have ¬ m = 1,
    -- either m = 101, or it does not.
    by_cases h_m_ne_101 : m = 101,
    {
      -- for our goal m = 101, this is the rhs of our goal.
      right, assumption,
    },
    -- we now know m ≠ 1 and m ≠ 101  but need to prve m = 1 ∨ m = 101
    by_contradiction,
    have hhh : (¬m = 1) ∧ (¬m = 101) := begin
      split,
      exact h_m_ne_1,
      exact h_m_ne_101,
    end,
    rw not_or_distrib at h,
    --apply not_and_of_not_or_not h,
        --rw not_and_of_not_or_not h_m_ne_1 ∨ h_m_ne_101,

    sorry,
  }
end

-- you will need the definition
-- a ∣ b := (∃ k : ℕ, a = b * k)
example (m a b : ℕ) :  m + a ∣ m^2 + (a + b) * m + a * b :=
begin
  sorry,
end

-- try ``unfold nat.prime at hp,`` to get started
example (p : ℕ) (hp : nat.prime p) : ¬ (p = 1) :=
begin
  sorry,
end

-- if none of the simplifiers work, try doing ``contrapose!``
-- sometimes the simplifiers need a little help
example (n : ℕ) : 0 < n ↔ n ≠ 0 :=
begin
  sorry,
end
