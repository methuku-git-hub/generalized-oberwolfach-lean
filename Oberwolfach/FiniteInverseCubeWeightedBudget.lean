module

public import Oberwolfach.FiniteInverseCubeTail

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem inverse_cube_distinct_scales_weighted_budget (C δ:ℝ) (hC:0≤C) (hδ:0<δ):
    ∃m:ℕ,1≤m ∧ ∀(I:Type) (T:Finset I) (a:I→ℕ),
    (∀i∈T,m≤a i) → Set.InjOn a T → C*(∑i∈T,(1:ℝ)/(a i:ℝ)^3)≤δ:=by
  obtain ⟨M,hM⟩:=exists_nat_gt (8*C/δ)
  let m:=max M 1
  have hm1:1≤m:=le_max_right _ _
  have hmpos:(0:ℝ)<m:=by exact_mod_cast (show 0<m by omega)
  have hMle:M≤m:=le_max_left _ _
  have hsmall:C*(8/(m:ℝ))≤δ:=by
    have hgt:(8*C/δ:ℝ)<m:=lt_of_lt_of_le hM (by exact_mod_cast hMle)
    have hh:8*C<(m:ℝ)*δ:=(div_lt_iff₀ hδ).1 hgt
    have he:C*(8/(m:ℝ))=(8*C)/(m:ℝ):=by ring
    rw [he]
    apply (div_le_iff₀ hmpos).2
    linarith only [hh]
  refine ⟨m,hm1,?_⟩
  intro I T a hmin hinj
  have ht:∀k∈T.image a,m≤k:=by
    intro k hk
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hk
    exact hmin i hi
  have htail:=inverse_cube_finset_tail_bound (T.image a) m hm1 ht
  have heq:(∑k∈T.image a,(1:ℝ)/(k:ℝ)^3)=∑i∈T,(1:ℝ)/(a i:ℝ)^3:=
    Finset.sum_image (f:=fun k:ℕ=>(1:ℝ)/(k:ℝ)^3) hinj
  rw [heq] at htail
  exact (mul_le_mul_of_nonneg_left htail hC).trans hsmall
end Oberwolfach
