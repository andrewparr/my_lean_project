import tactic
import data.real.basic

-- Some notes on Lean's coercion

-- Here since 1 and 2 are Natural numbers and so 1 - 2 evaluates to 0
#eval (1 : ℕ) - (2 : ℕ)

-- When using integers you get correct value of -1 : ℤ
#eval (1 : ℤ) - (2 : ℤ)


-- Note, Natural numbers are automaticially coerced to Integers
example : (2 : ℤ) = (2 : ℕ) := begin
  -- If you look at the goal for this you will actually see
  -- 2 = ↑2
  -- the up arrow is coercing 2 as a Natrual number to 2 as an Integer
  refl,
  -- the proof isn't that 2 as an integer is 2 as a nutural number
  -- it's a proof that 2 as an integer is the same as 2 the natural number coerced (converted to) an integer
end

-- This doesn't work the other way around because the Lean elaborator processes left to right
-- if it sees 2 : ℕ first, then it expects Natural numbers.
-- In this case we have to manually add the ↑ to coerce the natural number 2.
example : ↑(2 : ℕ) = (2 : ℤ) := begin
  -- the proof by reflextivity is the same however.
  refl,
end

-- NOTE: The coersion ↑ character is entered by typing \u

-- Here's the same example using real numbers rather than integers.
example : (2 : ℝ) = (2 : ℕ) := begin
  -- refl  doesn't solve this goal, but norm_cast will
  norm_cast,
end

-- As before, this way around and we need to manually add the coercion.
example : ↑(2 : ℕ) = (2 : ℝ) := begin
  norm_cast,
end


-- Just to complete the set, here's the examples with real and integers.
example : (2 : ℝ) = (2 : ℤ) := begin
  norm_cast,
end

example : ↑(2 : ℤ) = (2 : ℝ) := begin
  norm_cast,
end
