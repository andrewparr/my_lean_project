import tactic

/-
  If x is a positive integer, then x^2 - x is even.
-/

variables x y : ℤ

-- First need to define what it means to be even or odd
def is_even : Prop := ∃ k, x = 2*k
def is_odd : Prop := ¬ (is_even x)

lemma if_even_then_not_odd : (is_even x → ¬ is_odd x) :=
begin
  rintro ⟨k, h⟩,
  refine not_not.mpr _,
  use k,
  exact h
end

lemma if_odd_then_not_even : (is_odd x → ¬ is_even x) :=
begin
  intro h,
  exact h,
end

-- First prove a lemma
lemma even_sub_even_is_even : is_even x → is_even y → is_even (x - y) :=
begin
  rintro ⟨k1, h1⟩ ⟨k2, h2⟩,
  use (k1 - k2),
  rw h1,
  rw h2,
  rw ← mul_sub_left_distrib,
end

lemma even_prod_is_even : is_even x → is_even(x * y) :=
begin
  rintro ⟨c, h⟩,
  use c*y,
  rw h,
  rw mul_assoc,
end

lemma prod_even_is_even : is_even y → is_even (x * y) :=
begin
  rintro ⟨c, h⟩,
  use c*x,
  rw h,
  ring,
end

lemma one_of_consecutive_is_even : is_even x ∨ is_even (x + 1) :=
begin
    

end

example : is_even (x^2 - x) :=
begin
  rw pow_two,
  --rw ← mul_one x, -- this does all instances of x but I only want the right hand one
  -- conv_rhs rw ← mul_one x,
  ring_nf,
  split,
  {sorry,},
  assumption,
end
