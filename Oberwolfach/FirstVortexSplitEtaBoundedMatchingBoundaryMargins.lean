module

public import Oberwolfach.FirstVortexSplitEtaLateMatchingBoundaryMargins

@[expose] public section
/-! Bound the active cap while keeping the global and outside-change
matching errors separate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_split_eta_bounded_matching_boundary_margins
    (globalCap rho upper α δold δlocal δglobal ρmatch βfinal:ℝ)
    (hglobal:0<globalCap) (hrho:0<rho) (hupper:0<upper) (hα:0<α)
    (hδold:0<δold) (hgap:δold<δlocal) (hδglobal:0<δglobal) (hρmatch:0<ρmatch) (hβfinal:0<βfinal):
    ∃δsmall δspoke:ℝ,0<δsmall ∧ 0<δspoke ∧ δsmall≤upper ∧
    ∀ε:ℝ,0<ε→ε<δsmall/4→
    (∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U] (P S Sel Used:SimpleGraph (Fin n))
      (D m:ℕ) (β:ℝ) (Q:Vortex U P D β ε m) (π:Equiv.Perm (Fin n))
      (Req:Fin n→Fin n→Prop) (Pack:Finset (Sym2 (Fin n))),
      let I:=Q.extendedVertices 1
      let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
      let Kplus:=longClassInnerRequiredRepair S Used K I Pack;
      ((I.card:ℝ)≤ε*n) ∧ ∀v,((Kplus.degree v:ℝ)≤δsmall*n/4)) ∧
    ∀cLocal etaGlobal activeBound:ℝ,0<cLocal→0<etaGlobal→etaGlobal≤cLocal*rho/4→0<activeBound→
    ∃active:ℝ,0<active ∧ active≤globalCap ∧ active≤cLocal ∧ active≤activeBound ∧
    ∃tLocal eta s κMatch θ lamAssign lam ξCap:ℝ,
      0<tLocal ∧ (17+2/rho)*tLocal≤cLocal*ε/4 ∧
      0<eta ∧ eta≤tLocal ∧ eta≤etaGlobal ∧ 0<s ∧ s≤upper ∧
      0<κMatch ∧ κMatch≤s ∧ 0<θ ∧ θ≤s ∧ 10*θ≤κMatch*(βfinal/4) ∧ 0<lamAssign ∧ lamAssign≤s ∧
      10*θ≤δold ∧ θ≤δold/32 ∧ θ≤1/100 ∧ 10*θ≤δglobal ∧ 10*θ≤δsmall ∧
      8*(θ*ε^2+lamAssign*ε)/((ρmatch/4)/40000)<active*ε/128 ∧
      0<lam ∧ 0<ξCap ∧ ξCap≤s ∧ lam≤θ ∧ lam≤α/128 ∧ lam≤δold*ε/32 ∧
      (∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρmatch/4)/40000)*θ/4096 ∧
        ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
        ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
          (Q:Vortex U G D β ε mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ)) ∧
      ∀ζret ηBalance θ' a γ ξPart κ' Δ b:ℝ,
        ζret≤s→ηBalance≤s→θ'≤s→a≤s→γ≤s→ξPart≤s→κ'≤s→Δ≤s→b≤s→
        FirstVortexLocalGeometryRateBounds (globalCap/2) rho tLocal eta δsmall δspoke ζret ηBalance θ' a γ ξPart κ' Δ b :=by
  obtain ⟨δsmall,δspoke,hδ,hspoke,hδupper,hLater⟩:=
    first_vortex_split_eta_late_matching_boundary_margins globalCap rho upper α δold δlocal δglobal ρmatch βfinal
      hglobal hrho hupper hα hδold hgap hδglobal hρmatch hβfinal
  refine ⟨δsmall,δspoke,hδ,hspoke,hδupper,?_⟩
  intro ε hε hεgap
  obtain ⟨hGeometry,hLocal⟩:=hLater ε hε hεgap
  refine ⟨hGeometry,?_⟩
  intro cLocal etaGlobal activeBound hc hη hηcap hbound
  let active:=min (globalCap/2) (min (cLocal/2) (activeBound/2))
  have ha:0<active:=by dsimp [active];positivity
  have hag:active≤globalCap:=by dsimp [active];have h:=min_le_left (globalCap/2) (min (cLocal/2) (activeBound/2));linarith
  have hac:active≤cLocal:=by dsimp [active];have h: min (globalCap/2) (min (cLocal/2) (activeBound/2))≤cLocal/2:=(min_le_right _ _).trans (min_le_left _ _);linarith
  have hab:active≤activeBound:=by dsimp [active];have h: min (globalCap/2) (min (cLocal/2) (activeBound/2))≤activeBound/2:=(min_le_right _ _).trans (min_le_right _ _);linarith
  exact ⟨active,ha,hag,hac,hab,hLocal cLocal etaGlobal active hc hη hηcap ha⟩
end Oberwolfach
