module

public import Oberwolfach.LongCapacityScales
public import Oberwolfach.HalfResidualPathBounds

@[expose] public section

/-! Uniform positive coefficients in the scale n^{1-L} for conditional original
paths and half-residual paths. All estimates refer to the same fixed capacities. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def conditionalPathLower (a₀ d₀ d₁ : ℝ) (k : ℕ) : ℝ :=
  (a₀/d₁)^k / ((11/10)*(d₁/d₀))
def conditionalPathUpper (a₁ d₀ d₁ : ℝ) (k : ℕ) : ℝ :=
  (a₁/d₀)^k / ((9/10)*(d₀/d₁))
def halfResidualLower (a₀ d₀ d₁ : ℝ) (k : ℕ) : ℝ :=
  (d₀/4)*(a₀/(2*d₁))^k
def halfResidualUpper (a₁ d₀ d₁ : ℝ) (k : ℕ) : ℝ :=
  (d₁/2)*(2*a₁/d₀)^k

theorem conditionalPathLower_pos (a₀ d₀ d₁ : ℝ) (k : ℕ)
    (ha₀ : 0<a₀) (hd₀ : 0<d₀) (hd₁ : 0<d₁) :
    0<conditionalPathLower a₀ d₀ d₁ k := by unfold conditionalPathLower; positivity

theorem conditionalPathUpper_pos (a₁ d₀ d₁ : ℝ) (k : ℕ)
    (ha₁ : 0<a₁) (hd₀ : 0<d₀) (hd₁ : 0<d₁) :
    0<conditionalPathUpper a₁ d₀ d₁ k := by unfold conditionalPathUpper; positivity

theorem halfResidualLower_pos (a₀ d₀ d₁ : ℝ) (k : ℕ)
    (ha₀ : 0<a₀) (hd₀ : 0<d₀) (hd₁ : 0<d₁) :
    0<halfResidualLower a₀ d₀ d₁ k := by unfold halfResidualLower; positivity

theorem halfResidualUpper_pos (a₁ d₀ d₁ : ℝ) (k : ℕ)
    (ha₁ : 0<a₁) (hd₀ : 0<d₀) (hd₁ : 0<d₁) :
    0<halfResidualUpper a₁ d₀ d₁ k := by unfold halfResidualUpper; positivity

theorem conditional_path_scale_bounds {X : Type*}
    (R : ℕ → X → X → ℝ) (i k : ℕ) (p : Fin (k+1) → X)
    (n a₀ a₁ d₀ d₁ T : ℝ) (hn : 0<n) (hk : 0<k)
    (ha₀ : 0<a₀) (ha₁ : 0<a₁) (hd₀ : 0<d₀) (hd₁ : 0<d₁)
    (hR : ∀ j : Fin k,
      a₀/(d₁*n) ≤ R (i+j.val) (p j.castSucc) (p j.succ) ∧
      R (i+j.val) (p j.castSucc) (p j.succ) ≤ a₁/(d₀*n))
    (hT : ((9/10)*(d₀/d₁))/n ≤ T ∧ T ≤ ((11/10)*(d₁/d₀))/n) :
    conditionalPathLower a₀ d₀ d₁ k/n^(k-1) ≤ transitionPathWeight R i k p/T ∧
      transitionPathWeight R i k p/T ≤ conditionalPathUpper a₁ d₀ d₁ k/n^(k-1) := by
  obtain ⟨hplo,hpup⟩ := path_probability_bounds R i k p _ _ (by positivity) hR
  have hTp : 0<T := (by positivity : 0<((9/10)*(d₀/d₁))/n).trans_le hT.1
  have hpp : 0 ≤ transitionPathWeight R i k p := (by positivity : 0 ≤ (a₀/(d₁*n))^k).trans hplo
  have hlo := div_le_div₀ hpp hplo hTp hT.2
  have hup := div_le_div₀ (by positivity : 0 ≤ (a₁/(d₀*n))^k) hpup
    (by positivity : 0<((9/10)*(d₀/d₁))/n) hT.1
  rw [normalized_path_scale a₀ d₁ _ n hn k hk] at hlo
  rw [normalized_path_scale a₁ d₀ _ n hn k hk] at hup
  exact ⟨hlo,hup⟩

theorem half_residual_scale_bounds {X : Type*} [Fintype X] {k : ℕ} (hk : 0<k)
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ)
    (ρ : (Fin (k+1) → X) → ℝ)
    (ha : ∀ j x y, 0 ≤ a j x y) (hd : ∀ j x, 0<d j x)
    (hrow : ∀ j x, ∑ y, a j x y=d j.castSucc x)
    (hcol : ∀ j y, ∑ x, a j x y=d j.succ y)
    (hρ : ∀ p, 0 ≤ ρ p)
    (hreserve : ∀ j x y, pathEdgeLoad ρ j x y ≤ (11/27)*a j x y)
    (p : Fin (k+1) → X) (n a₀ a₁ d₀ d₁ : ℝ)
    (hn : 0<n) (ha₀ : 0<a₀) (hd₀ : 0<d₀)
    (hap : ∀ j, a₀ ≤ a j (p j.castSucc) (p j.succ) ∧ a j (p j.castSucc) (p j.succ) ≤ a₁)
    (hdp : ∀ j, d₀*n ≤ d j (p j) ∧ d j (p j) ≤ d₁*n) :
    halfResidualLower a₀ d₀ d₁ k/n^(k-1) ≤ halfResidualPathWeight a d ρ p ∧
      halfResidualPathWeight a d ρ p ≤ halfResidualUpper a₁ d₀ d₁ k/n^(k-1) := by
  obtain ⟨hlo,hup⟩ := halfResidualPathWeight_bounds hk a d ρ ha hd hrow hcol hρ hreserve
    p a₀ a₁ (d₀*n) (d₁*n) ha₀ (mul_pos hd₀ hn) hap hdp
  have elo : ((d₀*n/2)*((a₀/2)/(d₁*n))^k)/2 = halfResidualLower a₀ d₀ d₁ k/n^(k-1) := by
    rw [show d₀*n/2=(d₀/2)*n by ring, degree_times_path_scale (a₀/2) d₁ (d₀/2) n hn k hk]
    unfold halfResidualLower
    rw [show (a₀/2)/d₁=a₀/(2*d₁) by ring]
    ring
  have eup : ((d₁*n)*(a₁/(d₀*n/2))^k)/2 = halfResidualUpper a₁ d₀ d₁ k/n^(k-1) := by
    rw [show d₀*n/2=(d₀/2)*n by ring, degree_times_path_scale a₁ (d₀/2) d₁ n hn k hk]
    unfold halfResidualUpper
    rw [show a₁/(d₀/2)=2*a₁/d₀ by ring]
    ring
  exact ⟨elo ▸ hlo,eup ▸ hup⟩

end Oberwolfach
