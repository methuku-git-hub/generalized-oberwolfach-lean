module

public import Oberwolfach.FirstVortexInnerSumSelectorNumerics
public import Oberwolfach.FirstVortexInnerSumSpacingAfterRates

@[expose] public section
/-! Choose the local rates, matching spacing and class cutoff in order, then
instantiate the actual all-hub boundary in the selected-seed numerics. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem first_vortex_inner_sum_selector_relative_spacing_hierarchy
    (r:ℕ) (ε c rho eta cap θcap active factor:ℝ)
    (hε:0<ε) (hc:0<c) (hrho:0<rho) (heta:0<eta) (hcap:0<cap)
    (hθcap:0<θcap) (hθcap1:θcap≤1) (hactive:0<active) (hfactor:0<factor):
    ∃t s θ:ℝ,0<t ∧ 0<s ∧ t≤cap ∧ 0<θ ∧ θ≤s ∧ θ≤factor*s ∧ θ≤θcap ∧
    ∃dMin:ℕ,∀d:ℕ,dMin≤d→3≤d ∧ (r+4)+2≤d ∧
      1/(d:ℝ)≤θ/1024 ∧ 1/(d:ℝ)≤(active*ε/128)/10 ∧
      (1/(((r+4:ℕ):ℝ)+1))/(d:ℝ)≤θ ∧
    ∃KMin N:ℕ,∀K:ℕ,KMin≤K→3≤K ∧
      5/((((r+4:ℕ):ℝ)+1)*(d:ℝ)+5)+(((r+4:ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
    ∀n:ℕ,N≤n→∀u:ℕ,u≤n→∀I lam eps Δ ξPart κ ζret ηBalance:ℝ,
      0≤I→I≤n→ε*n/2≤I→0<lam→0<eps→0≤Δ→0≤ξPart→0≤κ→0≤ζret→0≤ηBalance→
      lam≤s→3*eps≤lam*(θ/(100*(K:ℝ)^2))→Δ≤eps/8→
      ξPart≤s→κ≤s→ζret≤s→ηBalance≤s→
    let boundary:ℝ:=4*(u:ℝ)/d+4*(n:ℝ)^(3/4:ℝ)
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
  obtain ⟨t,s,ht,hs,htcap,hNum⟩:=first_vortex_inner_sum_selector_numerics ε c rho eta cap hε hc hrho heta hcap
  let small:=min s (factor*s)
  have hsmall:0<small:=by dsimp [small];positivity
  have hsmalls:small≤s:=min_le_left _ _
  have hsmallfactor:small≤factor*s:=min_le_right _ _
  obtain ⟨θ,hθ,hθsmall,hθcap',dMin,hd⟩:=first_vortex_inner_sum_spacing_after_rates r small θcap ε active hsmall hθcap hε hactive
  have hθs:θ≤s:=hθsmall.trans hsmalls
  have hθfactor:θ≤factor*s:=hθsmall.trans hsmallfactor
  refine ⟨t,s,θ,ht,hs,htcap,hθ,hθs,hθfactor,hθcap',dMin,?_⟩
  intro d hdmin
  obtain ⟨hd3,hdr,hspace,haspace,hcut,⟨Nbound,hBound⟩,KMin,hK⟩:=hd d hdmin
  have hd0:0<d:=by omega
  obtain ⟨Nnum,hNnum⟩:=hNum d hd0
  refine ⟨hd3,hdr,hspace,haspace,hcut,KMin,max Nbound Nnum,?_⟩
  intro K hKmin
  obtain ⟨hK3,hKcut⟩:=hK K hKmin
  refine ⟨hK3,hKcut,?_⟩
  intro n hn u hu I lam eps Δ ξPart κ ζret ηBalance hI hIN hsize hlam heps hΔ0 hξ0 hκ0 hret0 hbal0 hlamS hepsRate hΔ hξ hκ hret hbal boundary a γ
  have hnBound:Nbound≤n:=le_trans (le_max_left _ _) hn
  have hnNum:Nnum≤n:=le_trans (le_max_right _ _) hn
  have hBoundary:boundary≤s*n:=(hBound n hnBound u hu).trans (mul_le_mul_of_nonneg_right hsmalls (Nat.cast_nonneg n))
  have hBoundary0:0≤boundary:=by dsimp [boundary];positivity
  exact hNnum n hnNum K (by omega) I θ lam eps Δ ξPart boundary κ ζret ηBalance hI hIN hsize hθ (hθcap'.trans hθcap1) hlam heps hΔ0 hξ0 hBoundary0 hκ0 hret0 hbal0 hθs hlamS hepsRate hΔ hξ hBoundary hκ hret hbal
end Oberwolfach
