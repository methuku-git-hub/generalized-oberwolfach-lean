module

public import Oberwolfach.OrdinaryAbundanceCandidateCutoff

@[expose] public section
/-! Choose one cutoff before the graph, large enough both for the original
abundant length to be a candidate and for the reserved-path capacity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach

theorem ordinary_abundance_capacity_cutoff
    (β θ:ℝ) (hβ:0<β) (hθ:0<θ) (r m d:ℕ)
    (hbase:5/(((m:ℝ)+1)*(d:ℝ)+5)<θ/2):
    ∃K:ℕ,3≤K ∧ r≤K ∧ 1/(2*(K:ℝ))≤β ∧
      5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2:=by
  obtain ⟨K₀,hK₀,hr,hβK⟩:=ordinary_abundance_candidate_cutoff β hβ r
  let a:ℝ:=((m:ℝ)+1)*(d:ℝ)
  let gap:ℝ:=θ/2-5/(a+5)
  have hgap:0<gap:=by dsimp [gap,a];linarith
  obtain ⟨N,hN⟩:=exists_nat_gt (a/gap)
  let K:=max K₀ N
  have hK₀K:K₀≤K:=le_max_left _ _
  have hNK:N≤K:=le_max_right _ _
  have hK3:3≤K:=hK₀.trans hK₀K
  have hK0:(0:ℝ)<K:=by exact_mod_cast (show 0<K by omega)
  have hK₀0:(0:ℝ)<K₀:=by exact_mod_cast (show 0<K₀ by omega)
  have hβK':1/(2*(K:ℝ))≤β:=by
    apply (div_le_div_of_nonneg_left (by norm_num:0≤(1:ℝ)) (by positivity:0<2*(K₀:ℝ)) ?_).trans hβK
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hK₀K) (by norm_num)
  have hbound:a/gap≤(K:ℝ):=hN.le.trans (Nat.cast_le.mpr hNK)
  have hmul:a≤(K:ℝ)*gap:=(div_le_iff₀ hgap).mp hbound
  have hdiv:a/(K:ℝ)≤gap:=(div_le_iff₀ hK0).2 (by nlinarith only [hmul])
  refine ⟨K,hK3,hr.trans hK₀K,hβK',?_⟩
  dsimp only [a,gap] at hdiv
  linarith only [hdiv]
end Oberwolfach
