module

public import Oberwolfach.LongPrescribedLoadMargins

@[expose] public section
/-! Choose the cycle spacing after the list and residual constants. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem absorber_spacing_parameter_choice
    (β b:ℝ) (hβ:0<β) (hb:0<b):
    ∃M:ℕ,∀m:ℕ,M≤m→0<m ∧ 4/(m:ℝ)≤b/2 ∧ 1/(100*(m:ℝ))≤β/4 ∧
      ∃N:ℕ,∀n:ℕ,N≤n→4*(n:ℝ)^(3/4:ℝ)≤b*n/2:=by
  let δ:=min (2*b) β
  have hδ:0<δ:=lt_min (by positivity) hβ
  have hδb:δ≤2*b:=min_le_left _ _
  have hδβ:δ≤β:=min_le_right _ _
  obtain ⟨M,hM⟩:=long_prescribed_load_margins δ hδ
  refine ⟨max M 1,?_⟩
  intro m hm
  have hmM:M≤m:=le_trans (le_max_left _ _) hm
  have hmpos:0<m:=by omega
  obtain ⟨hsmall,N,hN⟩:=hM m hmM
  have hmR:0<(m:ℝ):=by exact_mod_cast hmpos
  refine ⟨hmpos,?_,?_,N,?_⟩
  · linarith
  · have hh:1/(100*(m:ℝ))≤4/(m:ℝ):=by
      apply (div_le_iff₀ (by positivity : 0<100*(m:ℝ))).2
      field_simp
      nlinarith
    linarith
  · intro n hn
    have hh:=hN n hn
    have hscale:=mul_le_mul_of_nonneg_right hδb (Nat.cast_nonneg n)
    nlinarith
end Oberwolfach
