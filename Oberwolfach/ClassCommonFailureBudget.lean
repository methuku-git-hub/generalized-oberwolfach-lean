module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! A failure parameter may be chosen after the fixed class cutoff, and one
order threshold controls the union bound for every later class count. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem class_common_failure_budget (K:ℕ):
    ∃ χ:ℝ,0<χ ∧ ∃ N:ℕ,∀ k n:ℕ,k≤K+1→N≤n→
      (1/2:ℝ)+(∑ _i:Fin k,(100*χ+100/(n:ℝ)))<1:=by
  let χ:ℝ:=1/(800*((K:ℝ)+1))
  let N:=800*(K+1)
  have hK:(0:ℝ)<(K:ℝ)+1:=by positivity
  have hχ:0<χ:=by dsimp [χ];positivity
  refine ⟨χ,hχ,N,?_⟩
  intro k n hk hn
  have hn0:0<n:=by dsimp [N] at hn;omega
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn0
  have hNR:(800:ℝ)*((K:ℝ)+1)≤n:=by dsimp [N] at hn;exact_mod_cast hn
  have hχbound:100*χ=1/(8*((K:ℝ)+1)):=by dsimp [χ];field_simp <;> ring
  have hnBound:(100:ℝ)/n≤1/(8*((K:ℝ)+1)):=by
    apply (div_le_div_iff₀ hnR (by positivity:0<8*((K:ℝ)+1))).2
    nlinarith
  have htwo:1/(8*((K:ℝ)+1))+1/(8*((K:ℝ)+1))=1/(4*((K:ℝ)+1)):=by field_simp <;> ring
  have hunit:100*χ+100/(n:ℝ)≤1/(4*((K:ℝ)+1)):=by rw [hχbound];linarith
  have hkR:(k:ℝ)≤(K:ℝ)+1:=by exact_mod_cast hk
  have he:0≤100*χ+100/(n:ℝ):=by positivity
  have hsum:(∑ _i:Fin k,(100*χ+100/(n:ℝ)))≤((K:ℝ)+1)*(1/(4*((K:ℝ)+1))):=by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    calc
      _ ≤ ((K:ℝ)+1)*(100*χ+100/(n:ℝ)):=mul_le_mul_of_nonneg_right hkR he
      _ ≤ ((K:ℝ)+1)*(1/(4*((K:ℝ)+1))):=mul_le_mul_of_nonneg_left hunit hK.le
  have htotal:((K:ℝ)+1)*(1/(4*((K:ℝ)+1)))=1/4:=by field_simp
  linarith
end Oberwolfach
