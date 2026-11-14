module

public import Oberwolfach.FirstVortexActualCallerNumericResult
public import Oberwolfach.FirstVortexSummedLossMonotone

@[expose] public section
/-! The selected local numeric budget can be used at any larger caller
threshold; the same vortex and the same loss witnesses are retained. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_caller_local_cap_mono
    (r d K:ℕ) (ρ₀ cap rho eta δLoss εInner δglobal:ℝ)
    (ε c₁ c₂ active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal:ℝ)
    (hδ:0<δglobal) (hθ:0<θ) (hθδ:10*θ≤δglobal) (hspacing:1/(d:ℝ)≤θ/1024)
    (hc:c₁≤c₂)
    (h:FirstVortexActualCallerNumericResult r d K ρ₀ cap rho eta δLoss εInner δglobal
      ε c₁ active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal hδ hθ hθδ hspacing):
    FirstVortexActualCallerNumericResult r d K ρ₀ cap rho eta δLoss εInner δglobal
      ε c₂ active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal hδ hθ hθδ hspacing :=by
  obtain ⟨hbudget,hsupply,hδbound,N,hN⟩:=h
  refine ⟨hbudget,hsupply,hδbound,N,?_⟩
  intro n hn U _ G D m β Q hm hU
  obtain ⟨hn0,h100,h200,hsqrt,hNsmall,hsharp,hroot,hloss,hinner,hI,hscale,hactive,hceil,hglobal,hret,hWitness⟩:=hN n hn U G D m β Q hm hU
  refine ⟨hn0,h100,h200,hsqrt,hNsmall,hsharp,hroot,hloss,hinner,hI,hscale,hactive,hceil,hglobal,hret,?_⟩
  apply first_vortex_summed_loss_mono n d ((Q.extendedVertices 1).card:ℝ) c₁ c₂ rho eta θ
    (min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2)))
    (min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))) ξPart κPack Δ ζret ηBalance
    (4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ)) (by positivity) hc
  exact hWitness
end Oberwolfach
