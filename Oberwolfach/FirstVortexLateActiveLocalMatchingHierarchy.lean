module

public import Oberwolfach.FirstVortexFlexibleGlobalGeometry
public import Oberwolfach.FirstVortexOrderedGeometryRates
public import Oberwolfach.FirstVortexOrderedGeometryHierarchy
public import Oberwolfach.FirstVortexLocalChainRateChoice
public import Oberwolfach.FirstVortexLateActiveMatchingChoices

@[expose] public section
/-! Fix global scales first, accept the actual vortex scale, then choose the
local and matching rates after the active and local tolerances are known. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_late_active_local_matching_hierarchy
    (globalCap rho upper α δold δlocal δglobal ρmatch:ℝ)
    (hglobal:0<globalCap) (hrho:0<rho) (hupper:0<upper) (hα:0<α)
    (hδold:0<δold) (hgap:δold<δlocal) (hδglobal:0<δglobal) (hρmatch:0<ρmatch):
    ∃δsmall δspoke:ℝ,0<δsmall ∧ 0<δspoke ∧ δsmall≤upper ∧
    ∀ε:ℝ,0<ε→ε<δsmall/4→
    (∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U] (P S Sel Used:SimpleGraph (Fin n))
      (D m:ℕ) (β:ℝ) (Q:Vortex U P D β ε m) (π:Equiv.Perm (Fin n))
      (Req:Fin n→Fin n→Prop) (Pack:Finset (Sym2 (Fin n))),
      let I:=Q.extendedVertices 1
      let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
      let Kplus:=longClassInnerRequiredRepair S Used K I Pack;
      ((I.card:ℝ)≤ε*n) ∧ ∀v,((Kplus.degree v:ℝ)≤δsmall*n/4)) ∧
    ∀cLocal active:ℝ,0<cLocal→0<active→
    ∃tLocal eta s θ lamAssign lam ξCap:ℝ,
      0<tLocal ∧ (17+4/rho)*tLocal≤cLocal*ε/2 ∧
      0<eta ∧ eta≤tLocal ∧ 0<s ∧ s≤upper ∧
      0<θ ∧ θ≤s ∧ 0<lamAssign ∧ lamAssign≤s ∧
      10*θ≤δold ∧ θ≤δold/32 ∧ θ≤1/100 ∧ 10*θ≤δglobal ∧
      8*(θ*ε^2+lamAssign*ε)/((ρmatch/4)/40000)<active*ε/128 ∧
      0<lam ∧ 0<ξCap ∧ lam≤θ ∧ lam≤α/128 ∧ lam≤δold*ε/32 ∧
      (∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρmatch/4)/40000)*θ/4096 ∧
        ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
        ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
          (Q:Vortex U G D β ε mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ)) ∧
      ∀ζret ηBalance θ' a γ ξPart κ' Δ b:ℝ,
        ζret≤s→ηBalance≤s→θ'≤s→a≤s→γ≤s→ξPart≤s→κ'≤s→Δ≤s→b≤s→
        FirstVortexLocalGeometryRateBounds globalCap rho tLocal eta δsmall δspoke ζret ηBalance θ' a γ ξPart κ' Δ b :=by
  obtain ⟨δsmall,δspoke,hδ,hspoke,hδupper,hlater⟩:=
    first_vortex_ordered_geometry_rates globalCap rho upper hglobal hrho hupper
  refine ⟨δsmall,δspoke,hδ,hspoke,hδupper,?_⟩
  intro ε hε hεgap
  refine ⟨first_vortex_flexible_global_geometry δsmall ε hε hεgap,?_⟩
  intro cLocal active hc hactive
  obtain ⟨t,ht,_,htLocal⟩:=first_vortex_local_chain_rate_choice upper cLocal ε rho hupper hc hε hrho
  obtain ⟨eta,s,heta,hetat,hs,hsupper,hlocal⟩:=hlater t ht
  obtain ⟨θ,lamAssign,lam,ξCap,hθ,hAssign,hθs,hAssigns,hθold,hθlocal,hθone,hθglobal,
    hRate,hlam,hξ,hlamθ,hlamα,hlamδ,hCap⟩:=
      first_vortex_late_active_matching_choices α ε δold δlocal δglobal ρmatch active s
        hα hε hδold hgap hδglobal hρmatch hactive hs
  exact ⟨t,eta,s,θ,lamAssign,lam,ξCap,ht,htLocal,heta,hetat,hs,hsupper,hθ,hθs,hAssign,hAssigns,
    hθold,hθlocal,hθone,hθglobal,hRate,hlam,hξ,hlamθ,hlamα,hlamδ,hCap,hlocal⟩
end Oberwolfach
