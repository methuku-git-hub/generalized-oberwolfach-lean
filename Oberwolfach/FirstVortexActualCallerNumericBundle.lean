module

public import Oberwolfach.FirstVortexActualSelectorBudgetBundle
public import Oberwolfach.FirstVortexCallerHostThreshold

@[expose] public section
/-! Combine the actual-vortex selector budgets with the host thresholds of
the same-sample level-chain caller. -/
set_option autoImplicit false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_actual_caller_numeric_bundle
    (r d K Nlocal:ℕ) (ρ₀ cap βglobal rho eta ζmax Δmax δLoss εInner δglobal θmax t:ℝ)
    (ε cLocal s active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal:ℝ)
    (hβfinal:0<βfinal) (hβeq:βglobal=βfinal/2) (hδ:0<δglobal)
    (hθδ:10*θ≤δglobal) (hκlower:10*θ≤κPack*(βfinal/4))
    (hData:FirstVortexAmbientGlobalData r ρ₀ cap βglobal rho eta ζmax Δmax δLoss εInner δglobal θmax t)
    (hLocal:FirstVortexActualSummedLossNumerics r d K Nlocal ε cLocal rho eta s θ)
    (hd:0<d) (hK:1≤K) (hρ₀:0<ρ₀) (hε:0<ε) (hεInner:ε≤εInner) (hactive:0<active)
    (hs:0<s) (hθ:0<θ) (hθ1:θ≤1) (hθmax:θ≤θmax) (hlam:0<lam) (hlamθ:lam≤θ) (heps:0<eps)
    (hlams:lam≤s) (hlamcap:lam≤min t (3*min ζmax Δmax))
    (hepsRate:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hΔ0:0≤Δ) (hΔ:Δ≤eps/8)
    (hξ0:0≤ξPart) (hξs:ξPart≤s) (hξ:ξPart≤t) (hκ0:0≤κPack) (hκs:κPack≤s)
    (hκroot:κPack≤Real.sqrt δglobal/4) (hκ:κPack≤min cap (1:ℝ)/1024)
    (hζ0:0≤ζret) (hζs:ζret≤s) (hζ:ζret≤min cap (1:ℝ)/1024)
    (hbal0:0≤ηBalance) (hbals:ηBalance≤s) (hbal:ηBalance≤min cap (1:ℝ)/1024)
    (hspacing:1/(d:ℝ)≤θ/1024) (hactiveSpacing:1/(d:ℝ)≤(active*ε/128)/10)
    (hcoeff:8*(θ*ε^2+lamAssign*ε)/((ρ₀/4)/40000)<active*ε/128):
    let cGlobal:=min cap (1:ℝ)
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    Δ+δLoss<eta ∧ rho+Δ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ)) ∧ δglobal≤(βfinal/200)^2 ∧
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n))
      (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),0<m→Fintype.card U≤n→
    let I:ℝ:=(Q.extendedVertices 1).card
    let boundary:ℝ:=4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ);
      0<n ∧ 100/βfinal≤(n:ℝ) ∧ 200/βfinal≤(n:ℝ) ∧ 2/Real.sqrt δglobal≤(n:ℝ) ∧
      Classical.choose (first_vortex_all_hub_small_load_from_tests δglobal θ d hδ hθ hθδ hspacing)≤n ∧
      10*θ≤κPack*(βfinal/4) ∧
      δglobal+κPack≤Real.sqrt δglobal ∧
      2*(δglobal*n+(κPack*n+1))≤δLoss*n ∧
      εInner*n+((6*d+2:ℕ):ℝ)≤δglobal*n/4 ∧ I≤εInner*n ∧
      max a γ*n≤(θ/4096)*n ∧
      (2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max a γ*n≤active*(ε*n)/128) ∧
      (∀E:ℕ,(E:ℝ)≤(θ*ε^2+lamAssign*ε)*(n:ℝ)^2+24*d*n→
        2*(⌈4*(E:ℝ)/(((ρ₀/4)/40000)*n)⌉₊:ℕ)≤active*(ε*n)/128) ∧
      2*(ζret*n+(δglobal*n+(Real.sqrt δglobal*n+1)))+
        (ηBalance*n+2*(((2*θ+2*max a (4*γ)+2*ξPart)*n+2*(δglobal*n+(κPack*n+1)))+
          (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+((1+2/rho)*eta*n+1)))≤(cGlobal/2)*n ∧
      2*(ζret*n+10*θ*n)+ηBalance*n≤(cGlobal/2)*n ∧
      FirstVortexSummedLossWitness n d I cLocal rho eta θ a γ ξPart κPack Δ ζret ηBalance boundary :=by
  intro cGlobal a γ
  have hδbound:δglobal≤(βfinal/200)^2:=by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hbound,_,_,_,_,_,_,_,_⟩:=hData
    rw [hβeq] at hbound
    convert hbound using 1 <;> congr 1 <;> ring
  obtain ⟨hbudget,hsupply,Nb,hNb⟩:=
    first_vortex_actual_selector_budget_bundle r d K Nlocal ρ₀ cap βglobal rho eta ζmax Δmax δLoss εInner δglobal θmax t
      ε cLocal s active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack hData hLocal hd hK hρ₀ hε hεInner hactive
      hs hθ hθ1 hθmax hlam hlamθ heps hlams hlamcap hepsRate hΔ0 hΔ hξ0 hξs hξ hκ0 hκs hκroot hκ hζ0 hζs hζ
      hbal0 hbals hbal hspacing hactiveSpacing hcoeff
  obtain ⟨Nh,hNh⟩:=first_vortex_caller_host_threshold βfinal δglobal θ d hβfinal hδ hθ hθδ hspacing
  refine ⟨hbudget,hsupply,hδbound,max Nb Nh,?_⟩
  intro n hn U _ G D m β Q hm hu I boundary
  have hnb:Nb≤n:=le_trans (le_max_left _ _) hn
  have hnh:Nh≤n:=le_trans (le_max_right _ _) hn
  obtain ⟨hn0,h100,h200,hroot,hall⟩:=hNh n hnh
  exact ⟨hn0,h100,h200,hroot,hall,hκlower,hNb n hnb U G D m β Q hm hu⟩
end Oberwolfach
