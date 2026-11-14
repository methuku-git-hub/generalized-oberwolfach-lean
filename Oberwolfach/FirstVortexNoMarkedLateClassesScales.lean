module

public import Oberwolfach.FirstVortexNoMarkedOrderedChoices
public import Oberwolfach.FirstVortexFixedErrorJointSpacing

@[expose] public section
/-! Choose list, density and host spacing before the number of classes;
then choose the matching error and incidence rates. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_no_marked_scales_late_classes
    (γList pstar ρ₀ C₀:ℝ)
    (hγ:0<γList) (hp:0<pstar) (hρ:0<ρ₀) (hC:1≤C₀):
    ∃βlist lamList ζList βfinal δglobal δold δlocal θ bmatch αMatch εQ lam lamAssign:ℝ,
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
    ∃dMin:ℕ,∀d:ℕ,dMin≤d→2≤d→
      (∃N:ℕ,∀n≥N,
        (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstar^2*n ∧
        βlist*n+(n:ℝ)^(3/4:ℝ)≤γList*pstar^2*n*(1/100:ℝ) ∧
        (lamList+2*ζList)*n≤βlist*n) ∧
      ∀K:ℕ,0<K→∃eps ξ ρscale a γ:ℝ,
        0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
        0<ξ ∧ 4*ξ≤eps/2 ∧ 0<ρscale ∧ ρscale≤θ/4096 ∧
        0<a ∧ a≤lam/(10*d) ∧ a≤θ/(200*(K:ℝ)^2) ∧
        0<γ ∧ γ≤eps ∧ γ≤eps/2 ∧ γ≤1/2 ∧ γ≤lam/(10*d) ∧ γ≤lam/10 ∧
        (∀(n A:ℕ), εQ*n/2≤A→max a γ*n≤ρscale*A ∧ 2*(max a γ*n)≤δold*A/4) :=by
  obtain ⟨βlist,lamList,ζList,βfinal,δglobal,hβ,hβ1,hlamList,hlamList1,hζ,hβfinal,hβbound,hβfinal1,hδglobal,hδbound,hδ1,⟨dMin,hList⟩,hchoose⟩:=
    first_vortex_no_marked_ordered_choices γList pstar hγ hp
  let δold:=δglobal/2
  let δlocal:=δglobal
  let θ:=δglobal/128
  let bmatch:=((ρ₀/4)/40000)/32
  have hδold:0<δold:=by dsimp [δold];positivity
  have hgap:δold<δlocal:=by dsimp [δold,δlocal];linarith
  have hθ:0<θ:=by dsimp [θ];positivity
  have hb:0<bmatch:=by dsimp [bmatch];positivity
  obtain ⟨αMatch,εQ,lam,lamAssign,hα,hαb,hαsmall,hαglobal,hε,hεδ,htrim,hεα,hερ,hlam,hlamθ,hlamα,hlamδ,hlamAssign⟩:=
    hchoose bmatch ρ₀ θ δold C₀ hb hρ hθ hδold hC
  refine ⟨βlist,lamList,ζList,βfinal,δglobal,δold,δlocal,θ,bmatch,αMatch,εQ,lam,lamAssign,
    hβ,hβ1,hlamList,hlamList1,hζ,hβfinal,hβbound,hβfinal1,hδglobal,hδbound,hδ1,
    hδold,hgap,hθ,?_,?_,?_,?_,hb,?_,hα,hαb,hαsmall,hαglobal,hε,hεδ,htrim,hεα,hερ,
    hlam,hlamθ,hlamα,hlamδ,hlamAssign,dMin,?_⟩
  · dsimp [θ]; linarith
  · dsimp [θ,δold]; linarith
  · dsimp [θ,δold]; linarith
  · dsimp [θ]; linarith
  · dsimp [bmatch]; linarith
  intro d hdMin hd
  refine ⟨hList d hdMin hd,?_⟩
  intro K hK
  let eps:=min (1:ℝ) (lam*θ/(600*(K:ℝ)^2))
  let ξ:=eps/16
  have hKpos:(0:ℝ)<K:=by exact_mod_cast hK
  have heps:0<eps:=by dsimp [eps];positivity
  have heps1:eps≤1:=min_le_left _ _
  have heps2:eps≤lam*θ/(600*(K:ℝ)^2):=min_le_right _ _
  have hξ:0<ξ:=by dsimp [ξ];positivity
  have hepsrate:3*eps≤lam*(θ/(100*(K:ℝ)^2)):=by
    have hh:(lam*θ/(600*(K:ℝ)^2))*3≤lam*(θ/(100*(K:ℝ)^2)):=by
      field_simp
      nlinarith
    nlinarith [heps2]
  have hξeps:4*ξ≤eps/2:=by dsimp [ξ];linarith
  obtain ⟨ρscale,hρscale,hρscaleθ,hRates⟩:=first_vortex_fixed_error_joint_spacing K lam θ εQ δold eps hK hlam hθ hε hδold heps
  obtain ⟨a,γ,ha,haD,haθ,hγ,hγε,hγε2,hγhalf,hγD,hγlam,hscale⟩:=hRates d (by omega)
  exact ⟨eps,ξ,ρscale,a,γ,heps,heps1,hepsrate,hξ,hξeps,hρscale,hρscaleθ,ha,haD,haθ,hγ,hγε,hγε2,hγhalf,hγD,hγlam,hscale⟩
end Oberwolfach
