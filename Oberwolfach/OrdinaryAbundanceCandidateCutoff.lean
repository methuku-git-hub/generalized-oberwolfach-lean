module

public import Oberwolfach.OrdinaryAbundanceCandidate

@[expose] public section
/-! The short-length cutoff can be chosen from the original abundance
    parameter, before the number of vertices or factors is known. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_abundance_candidate_cutoff (β:ℝ) (hβ:0<β) (r:ℕ):
    ∃K:ℕ,3≤K ∧ r≤K ∧ 1/(2*(K:ℝ))≤β:=by
  obtain ⟨N,hN⟩:=exists_nat_gt (1/(2*β))
  let K:=max 3 (max r N)
  have hK3:3≤K:=le_max_left _ _
  have hr:r≤K:=(le_max_left _ _).trans (le_max_right _ _)
  have hNK:N≤K:=(le_max_right _ _).trans (le_max_right _ _)
  have hKR:0<(K:ℝ):=by exact_mod_cast (show 0<K by omega)
  have hNR:(N:ℝ)≤K:=by exact_mod_cast hNK
  have hhalf:1/(2*β)≤(K:ℝ):=le_trans hN.le hNR
  have hmult:= (div_le_iff₀ (by positivity:0<2*β)).mp hhalf
  refine ⟨K,hK3,hr,?_⟩
  apply (div_le_iff₀ (by positivity:0<2*(K:ℝ))).2
  nlinarith
end Oberwolfach
