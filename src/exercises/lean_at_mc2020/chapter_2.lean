
-- 2.1.2. Proofs as functions¶

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
