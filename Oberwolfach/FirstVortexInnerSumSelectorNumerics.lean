module

public import Oberwolfach.FirstVortexInnerSumPreSpacingNumerics
public import Oberwolfach.FirstVortexInnerSumSelectorRates

@[expose] public section
/-! Instantiate the ordered local numerics with the matching selector's
actual seed and deletion formulas. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem first_vortex_inner_sum_selector_numerics
    (ε c rho eta cap:ℝ) (hε:0<ε) (hc:0<c) (hrho:0<rho) (heta:0<eta) (hcap:0<cap):
    ∃t s:ℝ,0<t ∧ 0<s ∧ t≤cap ∧
    ∀d:ℕ,0<d→∃N:ℕ,∀n:ℕ,N≤n→∀K:ℕ,0<K→∀I θ lam eps Δ ξPart boundary κ ζret ηBalance:ℝ,
      0≤I→I≤n→ε*n/2≤I→
      0<θ→θ≤1→0<lam→0<eps→0≤Δ→0≤ξPart→0≤boundary→0≤κ→0≤ζret→0≤ηBalance→
      θ≤s→lam≤s→3*eps≤lam*(θ/(100*(K:ℝ)^2))→Δ≤eps/8→
      ξPart≤s→boundary≤s*n→κ≤s→ζret≤s→ηBalance≤s→
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    ∃lossInside inside loc:ℝ,0≤lossInside ∧ 0≤ inside ∧ 0≤loc ∧ loc≤eta*n ∧ inside≤I*eta*n ∧
      0≤2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1)) ∧
      I*(Δ*n+2*((6*d+2:ℕ):ℝ))+(n:ℝ)*
        (2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1)))≤lossInside ∧
      I*((n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ))+lossInside≤ inside ∧
      (n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ)+
        (Δ*n+2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1))+(6*d+2:ℕ))≤loc ∧
      ((2*θ+2*max a (4*γ)+2*ξPart)*n+2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1))+
        (n:ℝ)^(3/5:ℝ)+2*Δ*n+2*(6*d+2:ℕ)+loc+(inside/n+loc)/rho+1)≤c*I ∧
      2*(ζret*n+(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1)))+
        (ηBalance*n+2*((2*θ+2*max a (4*γ)+2*ξPart)*n+2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1))+
          (n:ℝ)^(3/5:ℝ)+2*Δ*n+2*(6*d+2:ℕ)+loc+(inside/n+loc)/rho+1))≤c*I :=by
  obtain ⟨t,s,ht,hs,htcap,hNum⟩:=first_vortex_inner_sum_pre_spacing_numerics ε c rho eta cap hε hc hrho heta hcap
  refine ⟨t,s,ht,hs,htcap,?_⟩
  intro d hd
  obtain ⟨N,hN⟩:=hNum d
  refine ⟨N,?_⟩
  intro n hn K hK I θ lam eps Δ ξPart boundary κ ζret ηBalance hI hIN hsize hθ0 hθ1 hlam heps hΔ0 hξ0 hboundary0 hκ0 hret0 hbal0 hθ hlamS hepsRate hΔ hξ hboundary hκ hret hbal a γ
  obtain ⟨ha,has,hγ,hγs,hΔs⟩:=first_vortex_inner_sum_selector_rates d K s θ lam eps Δ hd hK hs hθ0 hθ1 hlam heps hlamS hepsRate hΔ
  exact hN n hn I θ a γ ξPart boundary κ Δ ζret ηBalance hI hIN hsize hθ0.le ha.le hγ.le hξ0 hboundary0 hκ0 hΔ0 hret0 hbal0 hθ has hγs hξ hboundary hκ hΔs hret hbal
end Oberwolfach
