module

public import Oberwolfach.PrescribedBoundaryMarginsAsymptotic

@[expose] public section
/-! A large fixed wheel parameter and then a large order supply the two
sampled-occupancy margins used by residual placement. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_occupancy_margins_eventually (δ:ℝ) (hδ:0<δ):
    ∃m₀ N:ℕ,7≤m₀ ∧ ∀m≥m₀, ∀n≥N,
      0<((m:ℝ)+1) ∧ 4/((m:ℝ)+1)≤δ/4 ∧
      4*(n:ℝ)^(3/4:ℝ)≤δ*n/4:=by
  obtain ⟨d₀,N,hd₀,hN,hh⟩:=prescribed_boundary_margins_eventually δ hδ
  refine ⟨max d₀ 7,N,le_max_right _ _,?_⟩
  intro m hm n hn
  have hm0:0<(m:ℝ):=by exact_mod_cast (show 0<m by omega)
  obtain ⟨h1,h2⟩:=hh m (by omega) n hn
  have hm1:4/((m:ℝ)+1)≤4/(m:ℝ):=by
    apply div_le_div_of_nonneg_left (by norm_num) hm0
    linarith
  have hdn:0≤δ*(n:ℝ):=mul_nonneg hδ.le (by positivity)
  refine ⟨by positivity,?_,?_⟩ <;> linarith
end Oberwolfach
