module

public import Oberwolfach.FirstVortexActualSelectorGlobalBudgets
public import Oberwolfach.FirstVortexSelectorActiveBudgets
public import Oberwolfach.MarkedInitialInnerVertexBound

@[expose] public section
/-! Discharge the numerical loss, active-level and global-change hypotheses
for an actual vortex using the selector's exact rates. -/
set_option autoImplicit false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexSummedLossWitness
    (n d:ℕ) (I c rho eta θ a γ ξPart κ Δ ζret ηBalance boundary:ℝ):Prop :=
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
          (n:ℝ)^(3/5:ℝ)+2*Δ*n+2*(6*d+2:ℕ)+loc+(inside/n+loc)/rho+1))≤c*I

theorem first_vortex_actual_selector_budget_bundle
    (r d K Nlocal:ℕ) (ρ₀ cap βglobal rho eta ζmax Δmax δLoss εInner δglobal θmax t:ℝ)
    (ε cLocal s active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack:ℝ)
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
    Δ+δLoss<eta ∧ rho+Δ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ)) ∧
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n))
      (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),0<m→Fintype.card U≤n→
    let I:ℝ:=(Q.extendedVertices 1).card
    let boundary:ℝ:=4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ);
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
  obtain ⟨hbudget,hsupply,ha,has,hat,hγ,hγs,hγt,hΔs,Ng,hNg⟩:=
    first_vortex_actual_selector_global_budgets r d K ρ₀ cap βglobal rho eta ζmax Δmax δLoss εInner δglobal θmax t
      s θ lam eps Δ ξPart ζret ηBalance κPack hData hd hK hs hθ hθ1 hθmax hlam heps hlams hlamcap hepsRate hΔ0 hΔ
      hξ hζ hbal hκ
  have hlam1:lam≤1:=hlamθ.trans hθ1
  obtain ⟨Na,hNa⟩:=first_vortex_selector_active_budgets d K ρ₀ ε active θ lamAssign lam eps hd hρ₀ hε hactive hlam1 hactiveSpacing hcoeff
  have hinc:=first_vortex_selector_incidence_small d K θ lam eps hd hθ hθ1 hlam.le hlamθ hspacing
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hAmbient⟩:=hData
  obtain ⟨Nb,hNb⟩:=hAmbient d
  refine ⟨hbudget,hsupply,max Nlocal (max Ng (max Na Nb)),?_⟩
  intro n hn U _ G D m β Q hm hu I boundary
  have hnlocal:Nlocal≤n:=le_trans (le_max_left _ _) hn
  have hng:Ng≤n:=by omega
  have hna:Na≤n:=by omega
  have hnb:Nb≤n:=by omega
  obtain ⟨hδκ,hloss,hinner⟩:=hNb n hnb κPack hκ0 hκroot
  have hI:I≤εInner*n:=by
    have hfirst:((Q.extendedVertices 1).card:ℝ)≤ε*n:=by
      simpa only [Fintype.card_fin] using marked_initial_inner_vertex_bound Q hε.le
    have hm:=mul_le_mul_of_nonneg_right hεInner (Nat.cast_nonneg n)
    exact hfirst.trans hm
  have hincn:max a γ*n≤(θ/4096)*n:=mul_le_mul_of_nonneg_right hinc (Nat.cast_nonneg n)
  obtain ⟨hactiveBound,hceiling⟩:=hNa n hna
  obtain ⟨hrow,hcol⟩:=hNg n hng
  have hlocal:=hLocal n hnlocal U G D m β Q hm (Fintype.card U) hu lam eps Δ ξPart κPack ζret ηBalance
    hlam heps hΔ0 hξ0 hκ0 hζ0 hbal0 hlams hepsRate hΔ hξs hκs hζs hbals
  exact ⟨hδκ,hloss,hinner,hI,hincn,hactiveBound,hceiling,hrow,hcol,hlocal⟩
end Oberwolfach
