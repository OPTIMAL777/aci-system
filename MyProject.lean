import Mathlib.Data.Nat.Basic

-- Verify that for any natural numbers a and b, addition is commutative
theorem apex_tier_verification (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b

