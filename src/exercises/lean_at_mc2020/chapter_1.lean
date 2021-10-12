import tactic

-- 1.2. Implications in Lean

/--------------------------------------------------------------------------

``exact``

  If ``P`` is the target of the current goal and
  ``hp`` is a term of type ``P``, then
  ``exact hp,`` will close the goal.


``intro``

  If the target of the current goal is a function ``P → Q``, then
  ``intro hp,`` will produce a hypothesis
  ``hp : P`` and change the target to  ``Q``.

Delete the ``sorry,`` below and replace them with a legitimate proof.

--------------------------------------------------------------------------/

theorem tautology (P : Prop) (hp : P) : P :=
begin
  exact hp,
end

theorem tautology' (P : Prop) : P → P :=
begin
  intro hp,
  exact hp,
end

example (P Q : Prop): (P → (Q → P)) :=
begin
  intro hP,
  intro hQ,
  exact hP,
end

-- Can you find two different ways of proving the following?

-- First way
example (P Q : Prop) : ((Q → P) → (Q → P)) :=
begin
  intro hQP,
  exact hQP,
end

-- Second way - using the tautology' proof above
example (P Q : Prop) : ((Q → P) → (Q → P)) :=
begin
  exact tautology' _,
end

/--------------------------------------------------------------------------

``have``

  If ``f`` is a term of type ``P → Q`` and
  ``hp`` is a term of type ``P``, then
  ``have hq := f(hp),`` creates the hypothesis ``hq : Q`` .


``apply``

  If the target of the current goal is ``Q`` and
  ``f`` is a term of type ``P → Q``, then
  ``apply f,`` changes target to ``P``.

Delete the ``sorry,`` below and replace them with a legitimate proof.

--------------------------------------------------------------------------/

example (P Q R : Prop) (hp : P) (f : P → Q) (g : Q → R) : R :=
begin
  -- apply is reasoning backward
  apply g,
  apply f,
  exact hp,
end

example (P Q R : Prop) (hp : P) (f : P → Q) (g : Q → R) : R :=
begin
  -- have is reasoning forward
  have hq := f(hp),
  have hr := g(hq),
  exact hr,
end

example (P Q R S T U: Type)
  (hpq : P → Q)
  (hqr : Q → R)
  (hqt : Q → T)
  (hst : S → T)
  (htu : T → U)
  : P → U :=
begin
  intro hp,
  apply htu,
  apply hqt,
  apply hpq,
  exact hp,
end

example (P Q R S T U: Type)
  (hpq : P → Q)
  (hqr : Q → R)
  (hqt : Q → T)
  (hst : S → T)
  (htu : T → U)
  : P → U :=
begin
  intro hp,
  have hQ := hpq(hp),
  have hT := hqt(hQ),
  have hU := htu(hT),
  exact hU,
end

/--------------------------------------------------------------------------

Recall that
  ``¬ P`` is ``P → false``,
  ``¬ (¬ P)`` is ``(P → false) → false``, and so on.

Delete the ``sorry,`` below and replace them with a legitimate proof.

--------------------------------------------------------------------------/

-- Hint 
-- If two of your hypotheses are hp : Q and hnp : ¬ Q, then the term
-- hnp (hp)
-- has the type false.

theorem self_imp_not_not_self (P : Prop) : P → ¬ (¬ P) :=
begin
  intro hP,
  intro hnP,
  have x := hnP(hP),
  exact x,
end

theorem contrapositive (P Q : Prop) : (P → Q) → (¬Q → ¬P) :=
begin
  intro hPQ,
  intro hnQ,
  intro hP,
  have hQ := hPQ(hP),
  have x := hnQ(hQ),
  exact x,
end

-- Hint
-- If your target is false, and one of your assumptions is hnq : ¬ Q then try
-- apply hnq,

example (P : Prop) : ¬ (¬ (¬ P)) → ¬ P :=
begin
  intro hnnnP,
  intro hP,
  apply hnnnP,
  intro hnP,
  apply hnP,
  exact hP,
end

-- 1.3. Proof by contradiction

/--------------------------------------------------------------------------

You can prove exactly one of the following three using just
``exact``, ``intro``, ``have``, and ``apply``.

Can you find which one?

--------------------------------------------------------------------------/

theorem not_not_self_imp_self (P : Prop) : ¬ ¬ P → P:=
begin
  sorry,
end

theorem contrapositive_converse (P Q : Prop) : (¬Q → ¬P) → (P → Q) :=
begin
  sorry,
end

example (P : Prop) : ¬ P → ¬ ¬ ¬ P :=
begin
  intro hP,
  intro hnnP,
  apply hnnP,
  exact hP,
end

/--
  This is because it is not true that ¬ ¬ P = P by definition, after all,
     ¬ ¬ P is (P → false) → false
  which is drastically different from P.
  There is an extra axiom called the law of excluded middle which says that either P is inhabited
  or ¬ P is inhabited (and there is no middle option) and so P ↔ ¬ ¬ P.
  This is the axiom that allows for proofs by contradiction.
  Lean provides us the following tactics to use it.
--/

/--------------------------------------------------------------------------

``exfalso``

  Changes the target of the current goal to ``false``.

``push_neg``

  ``push_neg,`` simplifies negations in the target.
  You can push negations across a hypothesis ``hp : P`` using
  ``push_neg at hp,``.


``contrapose!``

  If the target of the current goal is  ``P → Q``,
  then ``contrapose!,`` changes the target to  ``¬ Q → ¬ P``.

  If the target of the current goal is ``Q`` and
  one of the hypotheses is ``hp : P``, then
  ``contrapose! hp,`` changes the target to  ``¬ P`` and
  changes the hypothesis to ``hp : ¬ Q``.


Delete the ``sorry,`` below and replace them with a legitimate proof.

--------------------------------------------------------------------------/

theorem not_not_self_imp_self' (P : Prop) : ¬ ¬ P → P:=
begin
  push_neg,
  intro hP,
  exact hP,
end

theorem contrapositive_converse' (P Q : Prop) : (¬Q → ¬P) → (P → Q) :=
begin
  intro hnQnP,
  -- goal is now P → Q, so use contrapose! following hints above
  contrapose,
  exact hnQnP, -- and we are left with hnQnP
end

example (P : Prop) : ¬ P → ¬ ¬ ¬ P :=
begin
  push_neg,
  exact tautology' _, -- goal was ¬ P → ¬ P, so use earlier proof of P → P.
end

theorem principle_of_explosion (P Q : Prop) : P → (¬ P → Q) :=
begin
  intro hP,   -- gives hP : P
  intro hnP,  -- gives hnP : ¬ P
  exfalso,    -- changes goal of Q to false
  apply hnP,  -- recall ¬ P is P → false and so this makes goal P
  exact hP,
end


