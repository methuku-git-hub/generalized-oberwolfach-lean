module

public import Oberwolfach.FirstVortexEarlyHostFinalCap
public import Oberwolfach.FirstVortexSpacingClassRetentionChoices
public import Oberwolfach.FirstVortexNoMarkedCappedOrderedChoices

@[expose] public section
/-! Fix list and spacing scales before the host event; choose the vortex
rate afterward below any positive event-supplied cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_early_host_geometry_with_final_cap
    (r:ℕ) (γList pstar ρ₀ βFinalCap:ℝ) (hγ:0<γList) (hp:0<pstar) (hρ:0<ρ₀) (hCap:0<βFinalCap):
    ∃βlist lamList ζList βfinal δglobal δold δlocal θ bmatch:ℝ,
      0<βlist ∧ βlist≤1 ∧ 0<lamList ∧ lamList≤1/100 ∧ 0<ζList ∧
      0<βfinal ∧ βfinal≤lamList/4 ∧ βfinal≤1 ∧ βfinal≤βFinalCap ∧
      0<δglobal ∧ δglobal≤(βfinal/100)^2 ∧ δglobal≤1/100 ∧
      0<δold ∧ δold<δlocal ∧ 0<θ ∧ θ≤1/100 ∧ 10*θ≤δold ∧ θ≤δold/32 ∧ 10*θ≤δglobal ∧
      0<bmatch ∧ bmatch≤((ρ₀/4)/40000)/16 ∧
      ∃d K:ℕ, 3≤d ∧ (r+4)+2≤d ∧ 3≤K ∧
        1/(d:ℝ)≤θ/1024 ∧ (1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ ∧
        5/(((((r+4):ℕ):ℝ)+1)*(d:ℝ)+5)+((((r+4):ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
      ∃ζret:ℝ,0<ζret ∧ ζret≤θ/4096 ∧ ∃Nret Nlist:ℕ,
        (∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
          q≤1/((((r+4):ℕ):ℝ)+1)→errOrd≤θ*n→
          (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n) ∧
        (∀n≥Nlist,
          (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstar^2*n ∧
          βlist*n+(n:ℝ)^(3/4:ℝ)≤γList*pstar^2*n*(1/100:ℝ) ∧
          (lamList+2*ζList)*n≤βlist*n) ∧
      ∀C₀ εAbs εRob γRich kstar tstar βList εMax:ℝ,1≤C₀→0<εAbs→0<εRob→0<γRich→0<kstar→0<tstar→0<βList→0<εMax→∃αMatch εQ lam lamAssign:ℝ,
        0<αMatch ∧ (2*αMatch)/16≤bmatch ∧
        (2*αMatch)/16≤((ρ₀/4)/40000)*θ/1024 ∧ 2*αMatch≤4*δglobal ∧
        0<εQ ∧ εQ≤εAbs ∧ εQ≤εRob ∧ εQ≤min ((γRich/2)*kstar) tstar/128 ∧ εQ≤βList/32 ∧ εQ≤εMax ∧ εQ<1/4 ∧ εQ≤δglobal ∧ βfinal+εQ≤lamList ∧
        εQ≤αMatch/(1000*C₀) ∧ εQ≤(ρ₀/4)/80000 ∧
        0<lam ∧ lam≤θ ∧ lam≤αMatch/128 ∧ lam≤δold*εQ/32 ∧ lam<lamAssign :=by
  obtain ⟨βlist,lamList,ζList,βfinal,δglobal,δold,δlocal,θ,bmatch,
    hβ,hβ1,hlamList,hlamList1,hζ,hβfinal,hβbound,hβfinal1,hβcap,hδglobal,hδbound,hδ1,
    hδold,hgap,hθ,hθ1,hθold,hθold32,hθglobal,hb,hbb,d,K,hd3,hdlarge,hK,hspacing,hcut,hcutHost,
    ζret,hζret,hζretBound,Nret,Nlist,hNret,hNlist,hchoose⟩:=
      first_vortex_early_host_parameters_with_final_cap r γList pstar ρ₀ βFinalCap hγ hp hρ hCap
  refine ⟨βlist,lamList,ζList,βfinal,δglobal,δold,δlocal,θ,bmatch,
    hβ,hβ1,hlamList,hlamList1,hζ,hβfinal,hβbound,hβfinal1,hβcap,hδglobal,hδbound,hδ1,
    hδold,hgap,hθ,hθ1,hθold,hθold32,hθglobal,hb,hbb,d,K,hd3,hdlarge,hK,hspacing,hcut,hcutHost,
    ζret,hζret,hζretBound,Nret,Nlist,hNret,hNlist,?_⟩
  intro C₀ εAbs εRob γRich kstar tstar βList εMax hC hAbs hRob hRich hk ht hList hMax
  let cap:=min εRob (min ((min ((γRich/2)*kstar) tstar)/128) (min (βList/32) εMax))
  have hcap:0<cap:=by dsimp [cap];positivity
  obtain ⟨αMatch,εQ,lam,lamAssign,hα,hαb,hαsmall,hαglobal,hε,hεAbs,hεcap,hεquarter,hεδ,htrim,hεα,hερ,hlam,hlamθ,hlamα,hlamδ,hlamAssign⟩:=
    hchoose C₀ εAbs cap hC hAbs hcap
  have hRobCap:εQ≤εRob:=hεcap.trans (min_le_left _ _)
  have hmid:=hεcap.trans (min_le_right _ _)
  have hsmall:εQ≤min ((γRich/2)*kstar) tstar/128:=hmid.trans (min_le_left _ _)
  have hlast:=hmid.trans (min_le_right _ _)
  exact ⟨αMatch,εQ,lam,lamAssign,hα,hαb,hαsmall,hαglobal,hε,hεAbs,hRobCap,hsmall,
    hlast.trans (min_le_left _ _),hlast.trans (min_le_right _ _),hεquarter,hεδ,htrim,hεα,hερ,hlam,hlamθ,hlamα,hlamδ,hlamAssign⟩
end Oberwolfach
