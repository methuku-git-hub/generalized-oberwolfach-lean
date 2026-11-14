module

public import Oberwolfach.FirstVortexOrderedGeometryHierarchy
public import Oberwolfach.FirstVortexGlobalGeometryBeforeSpacing
public import Oberwolfach.FirstVortexOrderedGeometryRates
public import Oberwolfach.FirstVortexGlobalGeometryOrderedChoice
public import Oberwolfach.FirstVortexLocalChainRateChoice

@[expose] public section
/-! A single ordered selection fixes global load scales, then the vortex
scale and host threshold, before the later local balance tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_ordered_geometry_hierarchy_before_spacing
    (cap rho upper εcap:ℝ)
    (hcap:0<cap) (hrho:0<rho) (hupper:0<upper) (hεcap:0<εcap):
    ∃δsmall δspoke ε:ℝ,0<δsmall ∧ 0<δspoke ∧ δsmall≤upper ∧
      0<ε ∧ ε≤εcap ∧ ε<δsmall/4 ∧
    (∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U] (P S Sel Used:SimpleGraph (Fin n))
      (D m:ℕ) (β:ℝ) (Q:Vortex U P D β ε m) (π:Equiv.Perm (Fin n))
      (Req:Fin n→Fin n→Prop) (Pack:Finset (Sym2 (Fin n))),
      let I:=Q.extendedVertices 1
      let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
      let Kplus:=longClassInnerRequiredRepair S Used K I Pack;
      ((I.card:ℝ)≤ε*n) ∧ ∀v,((Kplus.degree v:ℝ)≤δsmall*n/4)) ∧
    ∀c:ℝ,0<c→∃tLocal:ℝ,0<tLocal ∧ (17+4/rho)*tLocal≤c*ε/2 ∧
      ∃eta s:ℝ,0<eta ∧ eta≤tLocal ∧ 0<s ∧ s≤upper ∧
      ∀ζret ηBalance θ a γ ξPart κ Δ b:ℝ,
        ζret≤s→ηBalance≤s→θ≤s→a≤s→γ≤s→ξPart≤s→κ≤s→Δ≤s→b≤s→
        FirstVortexLocalGeometryRateBounds cap rho tLocal eta δsmall δspoke ζret ηBalance θ a γ ξPart κ Δ b :=by
  obtain ⟨δsmall,δspoke,hδ,hspoke,hδupper,hlater⟩:=first_vortex_ordered_geometry_rates cap rho upper hcap hrho hupper
  obtain ⟨ε,hε,hεupper,hεgap,hglobal⟩:=first_vortex_global_geometry_before_spacing δsmall εcap hδ hεcap
  refine ⟨δsmall,δspoke,ε,hδ,hspoke,hδupper,hε,hεupper,hεgap,hglobal,?_⟩
  intro c hc
  obtain ⟨t,ht,_,hrate⟩:=first_vortex_local_chain_rate_choice upper c ε rho hupper hc hε hrho
  obtain ⟨eta,s,heta,hetat,hs,hsupper,hlocal⟩:=hlater t ht
  refine ⟨t,ht,hrate,eta,s,heta,hetat,hs,hsupper,?_⟩
  intro ζret ηBalance θ a γ ξPart κ Δ b hζ hbal hθ ha hγ hξ hκ hΔ hb
  exact hlocal ζret ηBalance θ a γ ξPart κ Δ b hζ hbal hθ ha hγ hξ hκ hΔ hb
end Oberwolfach
