module

public import Oberwolfach.FirstVortexLocalChainRateBudget
public import Oberwolfach.MarkedFixedVortexSizes

@[expose] public section
/-! The local chain margins reduce to explicit component-rate bounds and
the lower size of the first inner vortex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_actual_local_chain_rates_geometry
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (D mm d:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε mm)
    (hε:0<ε) (hmm:0<mm)
    (c rho t eta loc θ a γ ξPart boundary κ Δ ζret ηBalance:ℝ)
    (hc:0≤c) (hrho:0<rho) (ht:0≤t) (heta:0≤eta) (hetat:eta≤t)
    (hrate:(17+4/rho)*t≤c*ε/2)
    (hA:2*θ+2*max a (4*γ)+2*ξPart≤t)
    (hB:boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1)≤t*n)
    (hE:(n:ℝ)^(3/5:ℝ)+2*Δ*n+2*(6*d+2:ℕ)≤t*n)
    (hret:ζret≤t) (hbal:ηBalance≤t) (hloc:loc≤t*n) (hunit:1≤t*n):
    ((2*θ+2*max a (4*γ)+2*ξPart)*n+2*((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1))+
      (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+(loc+(((Q.extendedVertices 1).card:ℝ)*eta+loc)/rho+1))≤c*((markedVortexInnerVertices Q 0).card:ℝ) ∧
    (2*(ζret*n+((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1)))+
      (ηBalance*n+2*((2*θ+2*max a (4*γ)+2*ξPart)*n+2*((boundary+2*(max a γ*n))+((6*d+2:ℕ):ℝ)+(κ*n+1))+
        (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+(loc+(((Q.extendedVertices 1).card:ℝ)*eta+loc)/rho+1))))≤c*((markedVortexInnerVertices Q 0).card:ℝ) :=by
  have hsize:=Q.first_inner_vertex_size_lower_of_positive_terminal_size hε hmm
  have hIle:((Q.extendedVertices 1).card:ℝ)≤n:=by
    exact_mod_cast (show (Q.extendedVertices 1).card≤n by simpa using Finset.card_le_univ (Q.extendedVertices 1))
  have hInner:((markedVortexInnerVertices Q 0).card:ℝ)=((Q.extendedVertices 1).card:ℝ):=by
    exact_mod_cast (marked_vortex_inner_cardinalities Q 0).1
  have hn:(0:ℝ)≤n:=Nat.cast_nonneg _
  have hAn:=mul_le_mul_of_nonneg_right hA hn
  have hretN:=mul_le_mul_of_nonneg_right hret hn
  have hbalN:=mul_le_mul_of_nonneg_right hbal hn
  have hbudget:=first_vortex_local_chain_rate_budget (n:ℝ) ((Q.extendedVertices 1).card:ℝ) c ε rho t eta loc
    ((2*θ+2*max a (4*γ)+2*ξPart)*n)
    (boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1))
    ((n:ℝ)^(3/5:ℝ)+2*Δ*n+2*(6*d+2:ℕ)) (ζret*n) (ηBalance*n)
    hn (Nat.cast_nonneg _) hIle hc hε.le hrho ht heta hetat (by simpa only [Fintype.card_fin] using hsize)
    hAn hB hE hretN hbalN hloc hunit hrate
  rw [hInner]
  constructor <;> nlinarith [hbudget.1,hbudget.2]
end Oberwolfach
