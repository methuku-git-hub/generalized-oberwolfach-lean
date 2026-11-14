module

public import Oberwolfach.FirstVortexActualCallerNumericBundle

@[expose] public section
/-! The exact numerical conclusion of the caller budget bundle, named so it
can be carried through the ordered selector hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexActualCallerNumericResult
    (r d K:ℕ) (ρ₀ cap rho eta δLoss εInner δglobal:ℝ)
    (ε cLocal active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal:ℝ)
    (hδ:0<δglobal) (hθ:0<θ) (hθδ:10*θ≤δglobal) (hspacing:1/(d:ℝ)≤θ/1024):Prop :=
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
      FirstVortexSummedLossWitness n d I cLocal rho eta θ a γ ξPart κPack Δ ζret ηBalance boundary
end Oberwolfach
