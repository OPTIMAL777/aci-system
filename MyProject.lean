import Mathlib.Data.Rat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Tactic

namespace ACI_Certified

open BigOperators Classical

-- CONFIGURATION
structure Config where
  dim   : ℕ
  lower : ℚ
  upper : ℚ
  k     : ℚ

def cfg : Config :=
  { dim := 21, lower := -5, upper := 5, k := (85 : ℚ) / 100 }

abbrev State := Fin cfg.dim → ℚ
def Zero : State := fun _ => 0

def clamp (x : ℚ) : ℚ :=
  if x < cfg.lower then cfg.lower
  else if x > cfg.upper then cfg.upper
  else x

def Proj (s : State) : State := fun i => clamp (s i)
def norm (s : State) : ℚ := Finset.univ.sum (fun i : Fin cfg.dim => |s i|)
def dist (x y : State) : ℚ := norm (fun i => x i - y i)
def U (s : State) : State := fun i => cfg.k * s i
def T (s : State) : State := Proj (U s)
def traj : ℕ → State → State
  | 0, s => s
  | n + 1, s => traj n (T s)
def Fixed (s : State) : Prop := T s = s
def InBounds (x : ℚ) : Prop := cfg.lower ≤ x ∧ x ≤ cfg.upper
def Valid (s : State) : Prop := ∀ i, InBounds (s i)

theorem k_lt_one : cfg.k < 1 := by unfold cfg; norm_num
theorem k_nonneg : 0 ≤ cfg.k := by unfold cfg; norm_num

theorem zero_fixed : Fixed Zero := by
  unfold Fixed T U Proj Zero clamp cfg; funext i; simp

theorem projection_valid (s : State) : Valid (Proj s) := by
  intro i; unfold Valid InBounds Proj clamp cfg; simp only
  split_ifs with h₁ h₂
  · constructor <;> linarith
  · constructor <;> linarith
  · push_neg at h₁ h₂; exact ⟨h₁, le_of_not_lt h₂⟩

theorem evolution_valid (s : State) : Valid (T s) := projection_valid (U s)

theorem clamp_nonexpansive (x y : ℚ) : |clamp x - clamp y| ≤ |x - y| := by
  unfold clamp cfg; simp only
  split_ifs with hx₁ hx₂ hy₁ hy₂ hy₁ hy₂ hy₁ hy₂ <;>
  simp_all <;> push_neg at * <;> try linarith
  all_goals (try (rw [abs_of_nonpos (by linarith)]; linarith))
  all_goals (try (rw [abs_of_nonneg (by linarith)]; linarith))
  all_goals (try (rw [abs_le]; constructor <;> linarith))

theorem proj_nonexpansive (x y : State) : dist (Proj x) (Proj y) ≤ dist x y := by
  unfold dist norm Proj; apply Finset.sum_le_sum
  intro i _; exact clamp_nonexpansive (x i) (y i)

theorem U_lipschitz (x y : State) : dist (U x) (U y) = cfg.k * dist x y := by
  unfold dist norm U cfg; simp only [← Finset.mul_sum]; congr 1
  apply Finset.sum_congr rfl; intro i _
  rw [show cfg.k * x i - cfg.k * y i = cfg.k * (x i - y i) by ring]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ (85 : ℚ) / 100)]

theorem contraction (x y : State) : dist (T x) (T y) ≤ cfg.k * dist x y := by
  unfold T
  calc dist (Proj (U x)) (Proj (U y))
      ≤ dist (U x) (U y) := proj_nonexpansive (U x) (U y)
    _ = cfg.k * dist x y := U_lipschitz x y

theorem dist_nonneg (x y : State) : 0 ≤ dist x y := by
  unfold dist norm; apply Finset.sum_nonneg; intro i _; exact abs_nonneg _

theorem dist_self_zero (s : State) : dist s s = 0 := by
  unfold dist norm; simp [sub_self, abs_zero]

theorem dist_triangle (x y z : State) : dist x z ≤ dist x y + dist y z := by
  unfold dist norm; simp only [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro i _
  have : x i - z i = (x i - y i) + (y i - z i) := by ring
  rw [this]; exact abs_add _ _

theorem zero_fixed_dist (s : State) : dist (T s) Zero ≤ cfg.k * dist s Zero := by
  have h := contraction s Zero; simp only [zero_fixed] at h; exact h

theorem decay (s : State) (n : ℕ) : dist (traj n s) Zero ≤ cfg.k ^ n * dist s Zero := by
  induction n generalizing s with
  | zero => simp [traj, pow_zero]
  | succ n ih =>
    simp only [traj]
    calc dist (traj n (T s)) Zero
        ≤ cfg.k ^ n * dist (T s) Zero := ih (T s)
      _ ≤ cfg.k ^ n * (cfg.k * dist s Zero) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg k_nonneg n)
            exact zero_fixed_dist s
      _ = cfg.k ^ (n + 1) * dist s Zero := by ring

def Converges (seq : ℕ → State) (tgt : State) : Prop :=
  ∀ ε : ℚ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, dist (seq n) tgt < ε

lemma geom_squeeze (C : ℚ) (hC : 0 ≤ C) (ε : ℚ) (hε : ε > 0) :
    ∃ N : ℕ, cfg.k ^ N * C < ε := by
  rcases eq_or_lt_of_le hC with rfl | hCpos
  · exact ⟨0, by simp [hε]⟩
  · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hCpos) k_lt_one
    exact ⟨N, by rwa [gt_iff_lt, ← div_lt_iff hCpos]⟩

theorem convergence (s : State) : Converges (fun n => traj n s) Zero := by
  intro ε hε
  obtain ⟨N, hN⟩ := geom_squeeze (dist s Zero) (dist_nonneg s Zero) ε hε
  refine ⟨N, fun n hn => ?_⟩
  calc dist (traj n s) Zero
      ≤ cfg.k ^ n * dist s Zero := decay s n
    _ ≤ cfg.k ^ N * dist s Zero := by
          apply mul_le_mul_of_nonneg_right _ (dist_nonneg s Zero)
          exact pow_le_pow_of_le_one k_nonneg (le_of_lt k_lt_one) hn
    _ < ε := hN

-- MASTER CERTIFICATION LOCK
structure Certified where
  k_bound      : cfg.k < 1                                           := k_lt_one
  proj_sound   : ∀ s, Valid (Proj s)                                 := projection_valid
  contract     : ∀ x y, dist (T x) (T y) ≤ cfg.k * dist x y        := contraction
  zero_fp      : Fixed Zero                                          := zero_fixed
  decay_bound  : ∀ s n, dist (traj n s) Zero ≤ cfg.k^n * dist s Zero := decay
  convergence  : ∀ s, Converges (fun n => traj n s) Zero             := convergence

def SystemLock : Certified := {}

end ACI_Certified
