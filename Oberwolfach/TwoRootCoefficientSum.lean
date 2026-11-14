module

public import Oberwolfach.OrdinaryCycleRootCounts

@[expose] public section

/-! Summing the coefficient cost of an isolator over all ordered endpoints.
The two endpoints are distinct; each adds one power of n precisely when it
lies outside the fixed rim. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem two_root_coefficient_factor {V : Type*} [DecidableEq V]
    (S : Finset V) {r : ℕ} (hr : 1≤r) (hS : S.card=r)
    (x y : V) (hxy : x≠y) (n γ : ℝ) (hn : n≠0) :
    1/(γ*n^((S∪{x,y}).card-1))=
      (1/(γ*n^(r-1)))*(if x∈S then 1 else 1/n)*(if y∈S then 1 else 1/n) := by
  have he : S∪{x,y}=insert x (insert y S) := by
    ext z
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  rw [he]
  by_cases hx : x∈S <;> by_cases hy : y∈S
  · simp [hx,hy,hS]
  · have hx' : x∈insert y S := Finset.mem_insert_of_mem hx
    rw [Finset.insert_eq_of_mem hx',Finset.card_insert_of_notMem hy,hS]
    simp only [hx,hy,if_true,if_false,mul_one,Nat.add_sub_cancel]
    have hp : n^r=n^(r-1)*n := by rw [← pow_succ,show r-1+1=r by omega]
    rw [hp];field_simp
  · have hx' : x∉insert y S := by simp [hx,hxy]
    rw [Finset.card_insert_of_notMem hx',Finset.insert_eq_of_mem hy,hS]
    simp only [hx,hy,if_true,if_false,mul_one,Nat.add_sub_cancel]
    have hp : n^r=n^(r-1)*n := by rw [← pow_succ,show r-1+1=r by omega]
    rw [hp];field_simp
  · have hx' : x∉insert y S := by simp [hx,hxy]
    rw [Finset.card_insert_of_notMem hx',Finset.card_insert_of_notMem hy,hS]
    simp only [hx,hy,if_true,if_false,Nat.add_sub_cancel]
    have hp : n^(r+1)=n^(r-1)*n*n := by
      rw [← pow_succ,← pow_succ,show r-1+1+1=r+1 by omega]
    rw [hp];field_simp

theorem root_discount_sum {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (hn : 0<Fintype.card V) :
    (∑ x : V,if x∈S then (1:ℝ) else 1/Fintype.card V)≤S.card+1 := by
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hfirst : (∑ x : V,if x∈S then (1:ℝ) else 0)=(S.card:ℝ) := by
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun x => x∈S)=S := by ext;simp
    rw [hf,Finset.sum_const,nsmul_eq_mul,mul_one]
  calc
    _ ≤ ∑ x : V,((if x∈S then (1:ℝ) else 0)+1/Fintype.card V) := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs
      · exact le_add_of_nonneg_right (by positivity)
      · simp
    _ = _ := by
      rw [Finset.sum_add_distrib,hfirst,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      field_simp

theorem two_root_coefficient_sum {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) {r : ℕ} (hr : 1≤r) (hS : S.card=r)
    (γ : ℝ) (hγ : 0<γ) (hn : 0<Fintype.card V)
    (a : V → V → ℝ) (ha : ∀ x y,0≤a x y)
    (hdiag : ∀ x,a x x=0)
    (hb : ∀ x y,x≠y → a x y≤1/(γ*(Fintype.card V:ℝ)^((S∪{x,y}).card-1))) :
    (∑ x,∑ y,a x y)≤(r+1)^2/(γ*(Fintype.card V:ℝ)^(r-1)) := by
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  let b (x : V) : ℝ := if x∈S then 1 else 1/Fintype.card V
  let C : ℝ := 1/(γ*(Fintype.card V:ℝ)^(r-1))
  have hC : 0≤C := by dsimp [C];positivity
  have hb0 (x : V) : 0≤b x := by dsimp [b];split_ifs <;> positivity
  have hsum : (∑ x,b x)≤r+1 := by simpa only [hS] using root_discount_sum S hn
  have hterm (x y : V) : a x y≤C*b x*b y := by
    by_cases hxy : x=y
    · subst y;rw [hdiag];positivity
    · have hh := hb x y hxy
      rw [two_root_coefficient_factor S hr hS x y hxy _ γ hn'.ne'] at hh
      exact hh
  calc
    _ ≤ ∑ x,∑ y,C*b x*b y := Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hterm x y))
    _ = C*(∑ x,b x)*(∑ x,b x) := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul,← Finset.mul_sum]
    _ ≤ C*(r+1)*(r+1) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hsum hC
      · exact hsum
      · exact Finset.sum_nonneg (fun x _ => hb0 x)
      · positivity
    _ = _ := by dsimp [C];ring

end Oberwolfach
