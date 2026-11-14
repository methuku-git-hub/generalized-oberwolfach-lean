module

public import Oberwolfach.FirstVortexActualCallerNumericResult
public import Oberwolfach.FirstVortexSummedLossCallerTransport

@[expose] public section
/-! The actual caller's global and first-inner numeric inputs, obtained from
the early smaller local budget without changing its witnesses. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_caller_resolved_numerics
    (r d K:ℕ) (ρ₀ cap rho eta δLoss εInner δglobal:ℝ)
    (ε cSmall cLocal active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal:ℝ)
    (hδ:0<δglobal) (hθ:0<θ) (hθδ:10*θ≤δglobal) (hspacing:1/(d:ℝ)≤θ/1024)
    (hβ:0<βfinal) (hc:cSmall≤cLocal)
    (h:FirstVortexActualCallerNumericResult r d K ρ₀ cap rho eta δLoss εInner δglobal
      ε cSmall active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal hδ hθ hθδ hspacing):
    let cGlobal:=min cap (1:ℝ)
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    Δ+δLoss<eta ∧ rho+Δ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ)) ∧
    δglobal≤(βfinal/200)^2 ∧ δglobal≤(βfinal/100)^2 ∧
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U] (G:SimpleGraph (Fin n))
      (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),0<m→Fintype.card U≤n→
    let I:ℝ:=(markedVortexInnerVertices Q 0).card
    let boundary:ℝ:=4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ);
      0<n ∧ 100/βfinal≤(n:ℝ) ∧ 200/βfinal≤(n:ℝ) ∧ 2/Real.sqrt δglobal≤(n:ℝ) ∧
      Classical.choose (first_vortex_all_hub_small_load_from_tests δglobal θ d hδ hθ hθδ hspacing)≤n ∧
      10*θ≤κPack*(βfinal/4) ∧ δglobal+κPack≤Real.sqrt δglobal ∧
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
  obtain ⟨hbudget,hsupply,hδstrong,N,hN⟩:=h
  have hδweak:δglobal≤(βfinal/100)^2:=by nlinarith [sq_nonneg βfinal]
  refine ⟨hbudget,hsupply,hδstrong,hδweak,N,?_⟩
  intro n hn U _ _ G D m β Q hm hU I boundary
  obtain ⟨hn0,h100,h200,hsqrt,hNsmall,hsharp,hroot,hloss,hinner,hI,hscale,hactive,hceil,hglobal,hret,hWitness⟩:=
    hN n hn U G D m β Q hm hU
  have hcard:(markedVortexInnerVertices Q 0).card=(Q.extendedVertices 1).card:=by
    simpa only [Nat.zero_add] using (marked_vortex_inner_cardinalities Q 0).1
  have hI':I≤εInner*n:=by dsimp only [I];rw [hcard];exact hI
  have hWitness':FirstVortexSummedLossWitness n d I cLocal rho eta θ a γ ξPart κPack Δ ζret ηBalance boundary:=by
    dsimp only [I,boundary]
    exact first_vortex_summed_loss_caller_transport G β ε Q d cSmall cLocal rho eta θ a γ ξPart κPack Δ ζret ηBalance _ hc hWitness
  exact ⟨hn0,h100,h200,hsqrt,hNsmall,hsharp,hroot,hloss,hinner,hI',hscale,hactive,hceil,hglobal,hret,hWitness'⟩
end Oberwolfach
