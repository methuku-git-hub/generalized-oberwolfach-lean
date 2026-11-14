module

public import Oberwolfach.ProfileSampleOrderMargins
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

@[expose] public section

/-! The bounded sample order is fixed before the forbidden-set bound
or separation graph is given. Only the ambient threshold depends on
those later inputs. All numerical margins are explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem finite_real_common_upper_bound {I : Type*} [Finite I] (f : I → ℝ) :
    ∃ K : ℝ,1<K ∧ ∀ i,f i≤K := by
  obtain ⟨M,hM⟩ := (Set.finite_range f).bddAbove
  refine ⟨max 2 M,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro i
  exact (hM (Set.mem_range_self i)).trans (le_max_right _ _)

theorem profile_sampling_numerical_margins (c : ℕ) (hc : 2≤c)
    (A Dₐ α ξ : ℝ) (hA : 0≤A) (hDₐ : 0≤Dₐ) (hα : 0<α) (hξ : 0<ξ) (hξ1 : ξ≤1) :
    ∃ N : ℕ,c+c*c≤N ∧ ∀ t : ℕ,N≤t → ∀ F₀ D : ℝ,0≤F₀ → 0≤D →
      ∃ k₀ : ℝ,1<k₀ ∧ ∀ k : ℝ,k₀≤k →
        0<k ∧ 2*(t:ℝ)≤k ∧ 2*F₀≤k ∧
        2*(c-1:ℕ)*(F₀+1+(c-1:ℕ))≤k ∧
        2*(c*c:ℕ)*(F₀+c+(c*c:ℕ))≤k ∧
        ((ξ/4)+F₀*(A/k))+(1+(ξ/4)+F₀*(A/k))*
          (2*(c-1:ℕ)*(((1:ℝ)+(c-1:ℕ))/t+(F₀+1+(c-1:ℕ))/k))≤ξ ∧
        2*(c*c:ℕ)*(((c:ℝ)+(c*c:ℕ))/t+(F₀+c+(c*c:ℕ))/k)≤1/4 ∧
        4*(F₀+c)*Dₐ≤α*k ∧ 4*D*(t:ℝ)^2/k≤1/4 := by
  let H : ℝ := (c-1:ℕ)
  let h : ℝ := (c*c:ℕ)
  obtain ⟨N,hN⟩ := exists_nat_gt (max ((c+c*c:ℕ):ℝ) (max (16*H*(1+H)/ξ) (16*h*((c:ℝ)+h))))
  have hNc : c+c*c≤N := by
    have hh : ((c+c*c:ℕ):ℝ)<N := (le_max_left _ _).trans_lt hN
    exact_mod_cast hh.le
  refine ⟨N,hNc,?_⟩
  intro t ht F₀ D hF₀ hD
  have htR : (N:ℝ)≤t := by exact_mod_cast ht
  have htpos : (0:ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have htv : 16*H*(1+H)≤ξ*t := by
    have hbound : 16*H*(1+H)/ξ≤(t:ℝ) :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (hN.le.trans htR))
    nlinarith [(div_le_iff₀ hξ).mp hbound]
  have htr : 16*h*((c:ℝ)+h)≤t :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (hN.le.trans htR))
  let f : Fin 9 → ℝ := ![2*t,2*F₀,2*H*(F₀+1+H),2*h*(F₀+c+h),
    16*H*(F₀+1+H)/ξ,16*h*(F₀+c+h),4*F₀*A/ξ,4*(F₀+c)*Dₐ/α,16*D*t^2]
  obtain ⟨k₀,hk₀,hf⟩ := finite_real_common_upper_bound f
  refine ⟨k₀,hk₀,?_⟩
  intro k hk
  have hb (i : Fin 9) : f i≤k := (hf i).trans hk
  have hkpos : 0<k := lt_of_lt_of_le (by linarith) hk
  have h0 : 2*(t:ℝ)≤k := by simpa only [f,Matrix.cons_val_zero] using hb 0
  have h1 : 2*F₀≤k := by simpa [f] using hb 1
  have h2 : 2*H*(F₀+1+H)≤k := by simpa [f] using hb 2
  have h3 : 2*h*(F₀+c+h)≤k := by simpa [f] using hb 3
  have h4 : 16*H*(F₀+1+H)≤ξ*k := by
    have hh : 16*H*(F₀+1+H)/ξ≤k := by simpa [f] using hb 4
    nlinarith [(div_le_iff₀ hξ).mp hh]
  have h5 : 16*h*(F₀+c+h)≤k := by simpa [f] using hb 5
  have h6 : 4*F₀*A≤ξ*k := by
    have hh : 4*F₀*A/ξ≤k := by simpa [f] using hb 6
    nlinarith [(div_le_iff₀ hξ).mp hh]
  have h7 : 4*(F₀+c)*Dₐ≤α*k := by
    have hh : 4*(F₀+c)*Dₐ/α≤k := by simpa [f] using hb 7
    nlinarith [(div_le_iff₀ hα).mp hh]
  have h8 : 16*D*(t:ℝ)^2≤k := by simpa [f] using hb 8
  have hloss : F₀*(A/k)≤ξ/4 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hkpos).mpr
    nlinarith
  have hv₁ : 2*H*((1+H)/(t:ℝ))≤ξ/8 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ htpos).mpr
    nlinarith
  have hv₂ : 2*H*((F₀+1+H)/k)≤ξ/8 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hkpos).mpr
    nlinarith
  have hδ : 2*H*((1+H)/(t:ℝ)+(F₀+1+H)/k)≤ξ/4 := by nlinarith
  have hδ0 : 0≤2*H*((1+H)/(t:ℝ)+(F₀+1+H)/k) := by dsimp [H];positivity
  have hv : ((ξ/4)+F₀*(A/k))+(1+(ξ/4)+F₀*(A/k))*
      (2*H*((1+H)/(t:ℝ)+(F₀+1+H)/k))≤ξ := by
    have hcoef : 1+ξ/4+F₀*(A/k)≤2 := by linarith
    have hh := mul_le_mul_of_nonneg_right hcoef hδ0
    linarith
  have hr₁ : 2*h*(((c:ℝ)+h)/(t:ℝ))≤1/8 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ htpos).mpr
    nlinarith
  have hr₂ : 2*h*((F₀+c+h)/k)≤1/8 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hkpos).mpr
    nlinarith
  have hr : 2*h*(((c:ℝ)+h)/(t:ℝ)+(F₀+c+h)/k)≤1/4 := by nlinarith
  have hsep : 4*D*(t:ℝ)^2/k≤1/4 := by apply (div_le_iff₀ hkpos).mpr;nlinarith
  exact ⟨hkpos,h0,h1,h2,h3,hv,hr,h7,hsep⟩

end Oberwolfach
