module

public import Oberwolfach.FiniteCoordinateEvents

@[expose] public section

/-! Perturbing products of probabilities. All factors are bounded by one,
so each individual loss is charged once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_product_perturbation {J : Type*} (S : Finset J) (x y : J → ℝ)
    (h : ∀ j∈S,0≤y j ∧ y j≤x j ∧ x j≤1) :
    0≤(∏ j∈S,x j)-(∏ j∈S,y j) ∧
      (∏ j∈S,x j)-(∏ j∈S,y j)≤∑ j∈S,(x j-y j) := by
  classical
  have hnonneg : 0≤(∏ j∈S,x j)-(∏ j∈S,y j) :=
    sub_nonneg.mpr (Finset.prod_le_prod₀ (fun j hj=>(h j hj).1) (fun j hj=>(h j hj).2.1))
  refine ⟨hnonneg,?_⟩
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    have hS : ∀ i∈S,0≤y i ∧ y i≤x i ∧ x i≤1 := fun i hi=>h i (Finset.mem_insert_of_mem hi)
    have hh := h j (Finset.mem_insert_self _ _)
    have hprod0 : 0≤∏ i∈S,y i := Finset.prod_nonneg (fun i hi=>(hS i hi).1)
    have hprod1 : (∏ i∈S,x i)≤1 := Finset.prod_le_one₀ (fun i hi=>(hS i hi).1.trans (hS i hi).2.1)
      (fun i hi=>(hS i hi).2.2)
    have hdiff : 0≤(∏ i∈S,x i)-(∏ i∈S,y i) :=
      sub_nonneg.mpr (Finset.prod_le_prod₀ (fun i hi=>(hS i hi).1) (fun i hi=>(hS i hi).2.1))
    have hind := ih hS hdiff
    rw [Finset.prod_insert hj,Finset.prod_insert hj,Finset.sum_insert hj]
    have h₁ := mul_le_mul_of_nonneg_left hprod1 (sub_nonneg.mpr hh.2.1)
    have h₂ := mul_le_mul_of_nonneg_right (hh.2.1.trans hh.2.2) hdiff
    nlinarith

theorem normalized_tuple_mass_le_one {n s l : ℕ} (hl : 0<l) (hs : s≤l)
    {ρ : ℝ} (hρ : 0≤ρ ∧ ρ≤1) :
    (s : ℝ)^n*(ρ/(l : ℝ))^n≤1 := by
  rw [← mul_pow]
  apply pow_le_one₀
  · exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg hρ.1 (Nat.cast_nonneg _))
  · have hlr : (0 : ℝ)<l := by exact_mod_cast hl
    have hsr : (s : ℝ)≤l := by exact_mod_cast hs
    have hsr0 : (0 : ℝ)≤s := Nat.cast_nonneg _
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hlr).mpr
    calc
      (s : ℝ)*ρ ≤ (s : ℝ)*1 := mul_le_mul_of_nonneg_left hρ.2 hsr0
      _ ≤ 1*(l : ℝ) := by simpa using hsr

theorem normalized_tuple_conflict_le {n s l A : ℕ} (hl : 0<l) (hs : s≤l)
    {ρ : ℝ} (hρ : 0≤ρ ∧ ρ≤1) :
    ((n^2*A*s^(n-1) : ℕ) : ℝ)*(ρ/(l : ℝ))^n≤
      ((n^2*A : ℕ) : ℝ)/(l : ℝ) := by
  by_cases hn : n=0
  · simp [hn]
  have hn1 : 1≤n := by omega
  have hexp : n=(n-1)+1 := by omega
  have hp := normalized_tuple_mass_le_one (n:=n-1) hl hs hρ
  have hlr : (0 : ℝ)<l := by exact_mod_cast hl
  have hratio : ρ/(l : ℝ)≤1/(l : ℝ) := div_le_div_of_nonneg_right hρ.2 hlr.le
  have hratio0 : 0≤ρ/(l : ℝ) := div_nonneg hρ.1 hlr.le
  have hsmall : (s : ℝ)^(n-1)*(ρ/(l : ℝ))^n≤1/(l : ℝ) := by
    have hpow : (ρ/(l : ℝ))^n=(ρ/(l : ℝ))^(n-1)*(ρ/(l : ℝ)) := by
      calc
        _ = (ρ/(l : ℝ))^((n-1)+1) := congrArg (fun a=>(ρ/(l : ℝ))^a) hexp
        _ = _ := pow_succ _ _
    rw [hpow]
    calc
      _ = ((s : ℝ)^(n-1)*(ρ/(l : ℝ))^(n-1))*(ρ/(l : ℝ)) := by ring
      _ ≤ 1*(ρ/(l : ℝ)) := mul_le_mul_of_nonneg_right hp hratio0
      _ ≤ _ := by simpa using hratio
  calc
    _ = ((n^2*A : ℕ) : ℝ)*((s : ℝ)^(n-1)*(ρ/(l : ℝ))^n) := by push_cast;ring
    _ ≤ ((n^2*A : ℕ) : ℝ)*(1/(l : ℝ)) := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg _)
    _ = _ := by ring

end Oberwolfach
