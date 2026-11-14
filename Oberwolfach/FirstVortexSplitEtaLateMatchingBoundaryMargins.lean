module

public import Oberwolfach.FirstVortexFlexibleGlobalGeometry
public import Oberwolfach.FirstVortexOrderedGeometryRates
public import Oberwolfach.FirstVortexOrderedGeometryHierarchy
public import Oberwolfach.FirstVortexSeparateEtaRateChoice
public import Oberwolfach.FirstVortexLocalRatesShrinkEta
public import Oberwolfach.FirstVortexLateActiveMatchingChoices

@[expose] public section
/-! Fix global scales first, accept the actual vortex scale, then choose the
local and matching rates after the active and local tolerances are known. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_split_eta_late_matching_boundary_margins
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
    ∀cLocal etaGlobal active:ℝ,0<cLocal→0<etaGlobal→etaGlobal≤cLocal*rho/4→0<active→
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
  obtain ⟨δsmall,δspoke,hδ,hspoke,hδupper,hlater⟩:=
    first_vortex_ordered_geometry_rates (globalCap/2) rho upper (by positivity) hrho hupper
  refine ⟨δsmall,δspoke,hδ,hspoke,hδupper,?_⟩
  intro ε hε hεgap
  refine ⟨first_vortex_flexible_global_geometry δsmall ε hε hεgap,?_⟩
  intro cLocal etaGlobal active hc hηGlobal hηcap hactive
  obtain ⟨t,ht,_,htLocal⟩:=first_vortex_separate_eta_local_rate_choice upper cLocal ε rho hupper hc hε hrho
  obtain ⟨etaOld,sOld,hOld,hOldt,hOldS,hOldUpper,hOldLocal⟩:=hlater t ht
  let eta:=min etaOld (etaGlobal/2)
  have heta:0<eta:=by dsimp [eta];positivity
  have hetaOld:eta≤etaOld:=min_le_left _ _
  have hetat:eta≤t:=hetaOld.trans hOldt
  have hetaGlobal:eta≤etaGlobal:=by have hh:eta≤etaGlobal/2:=min_le_right _ _;linarith
  let s:=min sOld (eta/200)
  have hs:0<s:=by dsimp [s];positivity
  have hsOld:s≤sOld:=min_le_left _ _
  have hsupper:s≤upper:=hsOld.trans hOldUpper
  have hsEta:100*s≤eta:=by have hh:s≤eta/200:=min_le_right _ _;linarith
  have hlocal:=first_vortex_local_rates_shrink_eta (globalCap/2) rho t etaOld eta δsmall δspoke sOld s
    hrho heta hetaOld hs.le hsOld hsEta hOldLocal
  let κMatch:=s/2
  have hκMatch:0<κMatch:=by dsimp [κMatch];positivity
  have hκMatchs:κMatch≤s:=by dsimp [κMatch];linarith
  let rateBound:=min s (min (δsmall/20) (s*βfinal/160))
  have hRateBound:0<rateBound:=by dsimp [rateBound];positivity
  obtain ⟨θ,lamAssign,lam,ξCap,hθ,hAssign,hθbound,hAssignBound,hθold,hθlocal,hθone,hθglobal,
    hRate,hlam,hξ,hlamθ,hlamα,hlamδ,hCap⟩:=
      first_vortex_late_active_matching_choices α ε δold δlocal δglobal ρmatch active rateBound
        hα hε hδold hgap hδglobal hρmatch hactive hRateBound
  have hθs:θ≤s:=hθbound.trans (min_le_left _ _)
  have hAssigns:lamAssign≤s:=hAssignBound.trans (min_le_left _ _)
  have hθsmall:10*θ≤δsmall:=by
    have hh:θ≤δsmall/20:=hθbound.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hθκ:10*θ≤κMatch*(βfinal/4):=by
    have hh:θ≤s*βfinal/160:=hθbound.trans ((min_le_right _ _).trans (min_le_right _ _))
    dsimp [κMatch];nlinarith
  let ξBound:=min ξCap (s/2)
  have hξBound:0<ξBound:=by dsimp [ξBound];positivity
  have hξBoundS:ξBound≤s:=by dsimp [ξBound];have hh:=min_le_right ξCap (s/2);linarith
  have hCapBound:∀ξ':ℝ,ξ'≤ξBound→lam+ξ'≤((ρmatch/4)/40000)*θ/4096 ∧
        ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
        ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
          (Q:Vortex U G D β ε mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ):=by
    intro ξ' hξ'
    exact hCap ξ' (hξ'.trans (min_le_left _ _))
  exact ⟨t,eta,s,κMatch,θ,lamAssign,lam,ξBound,ht,htLocal,heta,hetat,hetaGlobal,hs,hsupper,hκMatch,hκMatchs,hθ,hθs,hθκ,hAssign,hAssigns,
    hθold,hθlocal,hθone,hθglobal,hθsmall,hRate,hlam,hξBound,hξBoundS,hlamθ,hlamα,hlamδ,hCapBound,hlocal⟩
end Oberwolfach
