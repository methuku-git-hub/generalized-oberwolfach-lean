module

public import Oberwolfach.OrdinarySampledProfileMarginsFixedBeta
public import Oberwolfach.OrdinarySampledTriangleMarginsFixedBeta

@[expose] public section
/-! The profile slack may be decreased before the remaining tolerances are chosen. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem ordinary_sampled_profile_margins_smaller_beta (r:ℕ) (α pmin smin β η b L:ℝ)
    (hα:0<α) (hp:0<pmin) (hs:0<smin) (hβ:0<β)
    (hβmax:β≤α*pmin^2*smin^2) (hη:0<η) (hb:0≤b) (hL:0≤L):
    ∃ rowErr t ε:ℝ,0<rowErr∧0<t∧0<ε ∧
    ∃ N:ℕ,∀ n:ℕ,(N:ℝ)≤n → ∀ D:ℝ,(n:ℝ)/2≤D →
      β*n≤(pmin^2*smin^2)*(2*α)*n-rowErr*n-2*L ∧
      t/(pmin^r*(smin*smin)^(r-1))+(6*(r:ℝ)^4*b*L+ε*n)/D≤η := by
  obtain ⟨_,ρ,t,ε,hρ,ht,hε,N,hN⟩:=ordinary_sampled_profile_margins_fixed_beta r α pmin smin η b L hα hp hs hη hb hL
  refine ⟨ρ,t,ε,hρ,ht,hε,N,?_⟩
  intro n hn D hD
  obtain ⟨hrow,hload⟩:=hN n hn D hD
  exact ⟨(mul_le_mul_of_nonneg_right hβmax (by positivity)).trans hrow,hload⟩

theorem ordinary_sampled_triangle_margins_smaller_beta (α pmin smin β η b L:ℝ)
    (hα:0<α) (hp:0<pmin) (hs:0<smin) (hβ:0<β)
    (hβmax:β≤2*(min α (1/4))*pmin^4*smin^4) (hη:0<η) (hb:0≤b) (hL:0≤L):
    ∃ rowErr t ε:ℝ,0<rowErr∧0<t∧0<ε ∧
    ∃ N:ℕ,∀ n:ℕ,(N:ℝ)≤n → ∀ D:ℝ,(n:ℝ)/2≤D →
      β*n≤(pmin^4*smin^4)*(4*(min α (1/4)))*n-rowErr*n-4*L ∧
      t/(pmin^3*(smin*smin)^2)+(6*(3:ℝ)^4*b*L+ε*n)/D≤η := by
  obtain ⟨_,ρ,t,ε,hρ,ht,hε,N,hN⟩:=ordinary_sampled_triangle_margins_fixed_beta α pmin smin η b L hα hp hs hη hb hL
  refine ⟨ρ,t,ε,hρ,ht,hε,N,?_⟩
  intro n hn D hD
  obtain ⟨hrow,hload⟩:=hN n hn D hD
  exact ⟨(mul_le_mul_of_nonneg_right hβmax (by positivity)).trans hrow,hload⟩
end Oberwolfach
