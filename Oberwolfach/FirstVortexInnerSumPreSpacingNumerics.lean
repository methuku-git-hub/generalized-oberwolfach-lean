module

public import Oberwolfach.FirstVortexInnerSumPreSpacingRates
public import Oberwolfach.FirstVortexInnerSumActualMargins
public import Oberwolfach.FirstVortexInnerSumComponentRates
public import Oberwolfach.FirstVortexLocalChainInnerSumBudget

@[expose] public section
/-! Simultaneous ordered choices for the summed correction and both local
balance-transfer margins, with the global matching loss fixed earlier. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach

theorem first_vortex_inner_sum_pre_spacing_numerics
    (ε c rho eta cap:ℝ) (hε:0<ε) (hc:0<c) (hrho:0<rho) (heta:0<eta) (hcap:0<cap):
    ∃t s:ℝ,0<t ∧ 0<s ∧ t≤cap ∧
    ∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→∀I θ a γ ξPart boundary κ Δ ζret ηBalance:ℝ,
      0≤I→I≤n→ε*n/2≤I→
      0≤θ→0≤a→0≤γ→0≤ξPart→0≤boundary→0≤κ→0≤Δ→0≤ζret→0≤ηBalance→
      θ≤s→a≤s→γ≤s→ξPart≤s→boundary≤s*n→κ≤s→Δ≤s→ζret≤s→ηBalance≤s→
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
  have hcap':0<min cap (eta/2):=lt_min hcap (by positivity)
  obtain ⟨t,s,ht,htcap,hs,h32,hglobal,hlocal,htransfer,hNall⟩:=
    first_vortex_inner_sum_pre_spacing_rates ε c rho eta (min cap (eta/2)) hε hc hrho heta hcap'
  refine ⟨t,s,ht,hs,htcap.trans (min_le_left _ _),?_⟩
  intro d
  obtain ⟨N,hN⟩:=hNall d
  refine ⟨N,?_⟩
  intro n hn I θ a γ ξPart boundary κ Δ ζret ηBalance hI hIN hsize hθ0 ha0 hγ0 hξ0 hboundary0 hκ0 hΔ0 hret0 hbal0 hθ ha hγ hξ hboundary hκ hΔ hret hbal
  obtain ⟨hn0,hfixed,hunit,hunitT,hpowSum,hpow⟩:=hN n hn
  have hnR:0<(n:ℝ):=by exact_mod_cast hn0
  have hs0:0≤s:=hs.le
  have ht0:0≤t:=ht.le
  have h16:16*s≤t:=by linarith
  have h12:12*s≤t:=by linarith
  have hmax:max a γ≤s:=max_le ha hγ
  have hq0:0≤(n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ):=by positivity
  have hpowSumT:(n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ)≤t*n:=by
    have hh:=mul_le_mul_of_nonneg_right (show t/4≤t by linarith) hnR.le
    exact hpowSum.trans hh
  obtain ⟨lossInside,inside,hLoss,hinside,hOuter,hBound,hBudget,hGlobal,hLocal⟩:=
    first_vortex_inner_sum_actual_margins n d I ε c rho eta t s Δ boundary a γ κ hn0 hI hIN hε.le hc.le hrho.le heta.le ht0 hs0 hsize hΔ0 hboundary0 ha0 hγ0 hκ0 hΔ hboundary hmax hκ hfixed hunit h12 hpowSumT hglobal hlocal
  have hOuterRate:2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1))≤12*s*n:=by
    have hmaxn:=mul_le_mul_of_nonneg_right hmax hnR.le
    have hκn:=mul_le_mul_of_nonneg_right hκ hnR.le
    nlinarith
  let loc:ℝ:=(n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ)+
    (Δ*n+2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1))+(6*d+2:ℕ))
  have hloc0:0≤loc:=by dsimp [loc];positivity
  have hlocT:loc≤t*n:=by
    have hΔn:=mul_le_mul_of_nonneg_right hΔ hnR.le
    have h32n:=mul_le_mul_of_nonneg_right h32 hnR.le
    dsimp [loc]
    push_cast at *
    nlinarith
  have hteta:t≤eta:=by
    have hh:=htcap.trans (min_le_right cap (eta/2))
    linarith
  have hlocEta:loc≤eta*n:=hlocT.trans (mul_le_mul_of_nonneg_right hteta hnR.le)
  obtain ⟨hA,hB,hE,hRet,hBal⟩:=first_vortex_inner_sum_component_rates n d t s θ a γ ξPart boundary κ Δ ζret ηBalance
    ht0 hs0 hθ ha hγ hξ hboundary hκ hΔ hret hbal hfixed hunit h16 hpow
  have hAn:=mul_le_mul_of_nonneg_right hA hnR.le
  have hRetn:=mul_le_mul_of_nonneg_right hRet hnR.le
  have hBaln:=mul_le_mul_of_nonneg_right hBal hnR.le
  have hh:=first_vortex_local_chain_inner_sum_budget (n:ℝ) I c ε rho t inside loc
    ((2*θ+2*max a (4*γ)+2*ξPart)*n)
    (boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1))
    ((n:ℝ)^(3/5:ℝ)+2*Δ*n+2*(6*d+2:ℕ)) (ζret*n) (ηBalance*n)
    hnR hI hc.le hε.le hrho ht0 hinside hLocal hsize hAn hB hE hRetn hBaln hlocT hunitT htransfer
  refine ⟨lossInside,inside,loc,hLoss,hinside,hloc0,hlocEta,hGlobal,hOuter,hBound,hBudget,le_rfl,?_,?_⟩
  · convert hh.1 using 1 <;> ring
  · convert hh.2 using 1 <;> ring
end Oberwolfach
