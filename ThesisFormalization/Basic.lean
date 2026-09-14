import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

-- I.2.2 Check results of following code
#eval 1+2

example (x y z : ℚ)
  (h1 : 2 * x < 3 * y)
  (h2 : -4 * x + 2 * z < 0)
  (h3 : 12 * y - 4 * z < 0) : False := by
  linarith
