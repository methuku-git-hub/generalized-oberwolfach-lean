module

public import Oberwolfach.ScaledCapacityPaths

@[expose] public section

/-! Applying the path estimates to normalized, balanced capacities. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem mixed_capacity_transition_scale {X : Type*} [Fintype X]
    (d : ℕ → X → ℝ) (M n d₀ d₁ : ℝ)
    (hn : (Fintype.card X : ℝ)=n) (hnpos : 0<n) (hd₀ : 0<d₀) (hd₁ : 0<d₁)
    (hms : ∀ i, ∑ x, d i x=M)
    (hd : ∀ i x, d₀*n ≤ d i x ∧ d i x ≤ d₁*n)
    (i : ℕ) (z : X) (T : ℝ)
    (hmix : |T-capacityProfile d M i z| ≤ (1/10)*capacityProfile d M i z) :
    ((9/10)*(d₀/d₁))/n ≤ T ∧ T ≤ ((11/10)*(d₁/d₀))/n := by
  obtain ⟨hlo,hup⟩ := capacity_profile_scale (d i) n M d₀ d₁ hn hnpos hd₀ hd₁ (hms i) (hd i) z
  obtain ⟨hml,hmu⟩ := abs_le.mp hmix
  change -((1/10)*(d i z/M)) ≤ T-d i z/M at hml
  change T-d i z/M ≤ (1/10)*(d i z/M) at hmu
  simp only [mul_div_assoc]
  constructor <;> linarith

theorem capacity_transition_scale {X : Type*}
    (a : ℕ → X → X → ℝ) (d : ℕ → X → ℝ)
    (n a₀ a₁ d₀ d₁ : ℝ) (hn : 0<n) (ha₀ : 0<a₀) (hd₀ : 0<d₀)
    (j : ℕ) (x y : X)
    (ha : a₀ ≤ a j x y ∧ a j x y ≤ a₁)
    (hd : d₀*n ≤ d j x ∧ d j x ≤ d₁*n) :
    a₀/(d₁*n) ≤ capacityTransition a d j x y ∧
      capacityTransition a d j x y ≤ a₁/(d₀*n) := by
  have hdp : 0<d j x := (mul_pos hd₀ hn).trans_le hd.1
  exact ⟨div_le_div₀ (ha₀.le.trans ha.1) ha.1 hdp hd.2,
    div_le_div₀ (ha₀.le.trans (ha.1.trans ha.2)) ha.2 (mul_pos hd₀ hn) hd.1⟩

theorem conditional_capacity_path_bounds {X : Type*} [Fintype X]
    (a : ℕ → X → X → ℝ) (d : ℕ → X → ℝ)
    (M n a₀ a₁ d₀ d₁ : ℝ)
    (hn : (Fintype.card X : ℝ)=n) (hnpos : 0<n)
    (ha₀ : 0<a₀) (ha₁ : 0<a₁) (hd₀ : 0<d₀) (hd₁ : 0<d₁)
    (hms : ∀ i, ∑ x, d i x=M)
    (hd : ∀ i x, d₀*n ≤ d i x ∧ d i x ≤ d₁*n)
    (i k : ℕ) (hk : 0<k) (p : Fin (k+1) → X)
    (ha : ∀ j : Fin k, a₀ ≤ a (i+j.val) (p j.castSucc) (p j.succ) ∧
      a (i+j.val) (p j.castSucc) (p j.succ) ≤ a₁)
    (hmix : |transitionWalk (capacityTransition a d) i k (p 0) (p (Fin.last k))-
      capacityProfile d M (i+k) (p (Fin.last k))| ≤
      (1/10)*capacityProfile d M (i+k) (p (Fin.last k))) :
    conditionalPathLower a₀ d₀ d₁ k/n^(k-1) ≤
      transitionPathWeight (capacityTransition a d) i k p /
        transitionWalk (capacityTransition a d) i k (p 0) (p (Fin.last k)) ∧
    transitionPathWeight (capacityTransition a d) i k p /
        transitionWalk (capacityTransition a d) i k (p 0) (p (Fin.last k)) ≤
      conditionalPathUpper a₁ d₀ d₁ k/n^(k-1) := by
  exact conditional_path_scale_bounds (capacityTransition a d) i k p n a₀ a₁ d₀ d₁ _
    hnpos hk ha₀ ha₁ hd₀ hd₁
    (fun j => capacity_transition_scale a d n a₀ a₁ d₀ d₁ hnpos ha₀ hd₀ _ _ _ (ha j) (hd _ _))
    (mixed_capacity_transition_scale d M n d₀ d₁ hn hnpos hd₀ hd₁ hms hd _ _ _ hmix)

end Oberwolfach
