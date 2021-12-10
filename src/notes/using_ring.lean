import data.real.basic
import tactic

variables x y : ℝ

-- Showing examples of how ring works

example : (x + y)^2 = x^2 + 2 * x * y + y^2 :=
begin
  ring,
end

example : (x + y)^3 = x^3 + 3 * x^2 * y + 3 * x * y^2  + y^3 :=
begin
  ring,
end

-- If didn't use the variables decleared first
example {a : ℝ} {b : ℝ} : (a + b)^2 = a^2 + 2 * a * b + b^2 :=
begin
  ring,
end
