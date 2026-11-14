module

public import Oberwolfach.FirstVortexNoMarkedCompleteScales
public import Oberwolfach.FirstVortexFixedErrorJointSpacing
public import Oberwolfach.FirstVortexNoMarkedOrderedChoices

@[expose] public section
/-! Choose compatible first-vortex list, load, matching and density scales
before spacing, without any lower bound on the cycle parameter. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_no_marked_spacing_complete_scales
    (γList pstar ρ₀ C₀:ℝ) (K:ℕ)
    (hγ:0<γList) (hp:0<pstar) (hρ:0<ρ₀) (hC:1≤C₀) (hK:0<K):
    ∃βlist lamList ζList βfinal δglobal δold δlocal θ bmatch αMatch εQ lam lamAssign eps ξ ρscale:ℝ,
      0<βlist ∧ βlist≤1 ∧ 0<lamList ∧ lamList≤1/100 ∧ 0<ζList ∧
      0<βfinal ∧ βfinal≤lamList/4 ∧ βfinal≤1 ∧
      0<δglobal ∧ δglobal≤(βfinal/100)^2 ∧ δglobal≤1/100 ∧
      0<δold ∧ δold<δlocal ∧ 0<θ ∧ θ≤1/100 ∧ 10*θ≤δold ∧ θ≤δold/32 ∧ 10*θ≤δglobal ∧
      0<bmatch ∧ bmatch≤((ρ₀/4)/40000)/16 ∧
      0<αMatch ∧ (2*αMatch)/16≤bmatch ∧
      (2*αMatch)/16≤((ρ₀/4)/40000)*θ/1024 ∧ 2*αMatch≤4*δglobal ∧
      0<εQ ∧ εQ≤δglobal ∧ βfinal+εQ≤lamList ∧
      εQ≤αMatch/(1000*C₀) ∧ εQ≤(ρ₀/4)/80000 ∧
      0<lam ∧ lam≤θ ∧ lam≤αMatch/128 ∧ lam≤δold*εQ/32 ∧ lam<lamAssign ∧
      0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
      0<ξ ∧ 4*ξ≤eps/2 ∧
      0<ρscale ∧ ρscale≤θ/4096 ∧
    ∃dMin:ℕ,∀d:ℕ,dMin≤d→2≤d→∃a γ:ℝ,
      0<a ∧ a≤lam/(10*d) ∧ a≤θ/(200*(K:ℝ)^2) ∧
      0<γ ∧ γ≤eps ∧ γ≤eps/2 ∧ γ≤1/2 ∧ γ≤lam/(10*d) ∧ γ≤lam/10 ∧
      (∀(n A:ℕ), εQ*n/2≤A→max a γ*n≤ρscale*A ∧ 2*(max a γ*n)≤δold*A/4) ∧
    ∃N:ℕ,∀n≥N,
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstar^2*n ∧
      βlist*n+(n:ℝ)^(3/4:ℝ)≤γList*pstar^2*n*(1/100:ℝ) ∧
      (lamList+2*ζList)*n≤βlist*n :=by
  obtain ⟨βlist,lamList,ζList,βfinal,δglobal,δold,δlocal,θ,bmatch,αMatch,εQ,lam,lamAssign,eps,ξ,
    hβ,hβ1,hlamList,hlamList1,hζ,hβfinal,hβbound,hβfinal1,hδglobal,hδbound,hδ1,
    hδold,hgap,hθ,hθ1,hθδ,hθlocal,hθglobal,hb,hbd,hα,hαb,hαsmall,hαglobal,hε,hεδ,htrim,hεα,hερ,
    hlam,hlamθ,hlamα,hlamδ,hlamAssign,heps,heps1,hepsrate,hξ,hξeps,dMin,hList⟩:=
    first_vortex_no_marked_complete_scales γList pstar ρ₀ C₀ K hγ hp hρ hC hK
  obtain ⟨ρscale,hρscale,hρscaleθ,hRates⟩:=first_vortex_fixed_error_joint_spacing K lam θ εQ δold eps hK hlam hθ hε hδold heps
  refine ⟨βlist,lamList,ζList,βfinal,δglobal,δold,δlocal,θ,bmatch,αMatch,εQ,lam,lamAssign,eps,ξ,ρscale,
    hβ,hβ1,hlamList,hlamList1,hζ,hβfinal,hβbound,hβfinal1,hδglobal,hδbound,hδ1,
    hδold,hgap,hθ,hθ1,hθδ,hθlocal,hθglobal,hb,hbd,hα,hαb,hαsmall,hαglobal,hε,hεδ,htrim,hεα,hερ,
    hlam,hlamθ,hlamα,hlamδ,hlamAssign,heps,heps1,hepsrate,hξ,hξeps,hρscale,hρscaleθ,dMin,?_⟩
  intro d hd hd2
  obtain ⟨a,γ,ha,haD,haθ,hγ,hγε,hγε2,hγhalf,hγD,hγlam,hscale⟩:=hRates d (by omega)
  exact ⟨a,γ,ha,haD,haθ,hγ,hγε,hγε2,hγhalf,hγD,hγlam,hscale,hList d hd hd2⟩
end Oberwolfach
