module

public import Oberwolfach.CapacityPathProducts

@[expose] public section

/-! Quantitative bounds for each surviving half-residual path. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem halfResidualPathWeight_bounds {X : Type*} [Fintype X] {k : ℕ} (hk : 0 < k)
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ)
    (ρ : (Fin (k+1) → X) → ℝ)
    (ha : ∀ j x y, 0 ≤ a j x y) (hd : ∀ j x, 0 < d j x)
    (hrow : ∀ j x, ∑ y, a j x y=d j.castSucc x)
    (hcol : ∀ j y, ∑ x, a j x y=d j.succ y)
    (hρ : ∀ p, 0 ≤ ρ p)
    (hreserve : ∀ j x y, pathEdgeLoad ρ j x y ≤ (11/27)*a j x y)
    (p : Fin (k+1) → X) (a₀ a₁ d₀ d₁ : ℝ) (ha₀ : 0 < a₀) (hd₀ : 0 < d₀)
    (hap : ∀ j, a₀ ≤ a j (p j.castSucc) (p j.succ) ∧ a j (p j.castSucc) (p j.succ) ≤ a₁)
    (hdp : ∀ j, d₀ ≤ d j (p j) ∧ d j (p j) ≤ d₁) :
    ((d₀/2)*((a₀/2)/d₁)^k)/2 ≤ halfResidualPathWeight a d ρ p ∧
      halfResidualPathWeight a d ρ p ≤ (d₁*(a₁/(d₀/2))^k)/2 := by
  have har (j : Fin k) : a₀/2 ≤ residualIntervalCapacity a ρ j (p j.castSucc) (p j.succ) ∧
      residualIntervalCapacity a ρ j (p j.castSucc) (p j.succ) ≤ a₁ := by
    have hh := residual_path_capacity_bounds a ρ ha hρ hreserve j (p j.castSucc) (p j.succ)
    exact ⟨(div_le_div_of_nonneg_right (hap j).1 (by norm_num)).trans hh.1,hh.2.trans (hap j).2⟩
  have hdr (j : Fin (k+1)) : d₀/2 ≤ residualIntervalDegree d ρ j (p j) ∧
      residualIntervalDegree d ρ j (p j) ≤ d₁ := by
    have hh := residualIntervalDegree_bounds hk a d ρ hρ hd hrow hcol hreserve j (p j)
    exact ⟨(div_le_div_of_nonneg_right (hdp j).1 (by norm_num)).trans hh.1,hh.2.trans (hdp j).2⟩
  obtain ⟨hlo,hup⟩ := capacityPathWeight_bounds (residualIntervalCapacity a ρ)
    (residualIntervalDegree d ρ) p (a₀/2) a₁ (d₀/2) d₁ (half_pos ha₀) (half_pos hd₀) har hdr
  exact ⟨div_le_div_of_nonneg_right hlo (by norm_num),div_le_div_of_nonneg_right hup (by norm_num)⟩

end Oberwolfach
