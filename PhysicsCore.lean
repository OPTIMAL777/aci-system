import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace PhysicsCore

-- ENERGY TRIAD (ETS)
structure EnergyTriad where
  energy   : ℝ
  thermal  : ℝ
  structural : ℝ

-- LAWSON CRITERION
def LawsonBound : ℝ := 1e21

def lawson_check (n T τ : ℝ) : Bool :=
  decide (n * T * τ ≥ LawsonBound)

-- DEI TRIPLE PRODUCT
def triple_product (n T τ : ℝ) : ℝ := n * T * τ

theorem triple_product_pos (n T τ : ℝ)
    (hn : 0 < n) (hT : 0 < T) (hτ : 0 < τ) :
    0 < triple_product n T τ := by
  unfold triple_product
  exact mul_pos (mul_pos hn hT) hτ

-- ETS COUPLING RULE
def ets_valid (e : EnergyTriad) : Prop :=
  e.energy > 0 ∧ e.thermal > 0 ∧ e.structural > 0

theorem ets_all_positive (e : EnergyTriad)
    (h : ets_valid e) : e.energy > 0 ∧ e.thermal > 0 := by
  exact ⟨h.1, h.2.1⟩

end PhysicsCore
