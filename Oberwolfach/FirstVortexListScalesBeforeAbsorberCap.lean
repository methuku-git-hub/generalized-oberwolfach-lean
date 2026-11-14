module

public import Oberwolfach.FirstVortexNoMarkedCappedOrderedChoices

@[expose] public section
/-! Fix list and spacing scales before the host event; choose the vortex
rate afterward below any positive event-supplied cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_list_scales_before_absorber_cap
    (γList pstar ρ₀:ℝ) (hγ:0<γList) (hp:0<pstar) (hρ:0<ρ₀):
    ∃βlist lamList ζList βfinal δglobal δold δlocal θ bmatch:ℝ,
      0<βlist ∧ βlist≤1 ∧ 0<lamList ∧ lamList≤1/100 ∧ 0<ζList ∧
      0<βfinal ∧ βfinal≤lamList/4 ∧ βfinal≤1 ∧
      0<δglobal ∧ δglobal≤(βfinal/100)^2 ∧ δglobal≤1/100 ∧
      0<δold ∧ δold<δlocal ∧ 0<θ ∧ θ≤1/100 ∧ 10*θ≤δold ∧ θ≤δold/32 ∧ 10*θ≤δglobal ∧
      0<bmatch ∧ bmatch≤((ρ₀/4)/40000)/16 ∧
      (∃dMin:ℕ,∀d:ℕ,dMin≤d→2≤d→∃N:ℕ,∀n≥N,
        (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstar^2*n ∧
        βlist*n+(n:ℝ)^(3/4:ℝ)≤γList*pstar^2*n*(1/100:ℝ) ∧
        (lamList+2*ζList)*n≤βlist*n) ∧
      ∀C₀ εAbs:ℝ,1≤C₀→0<εAbs→∃αMatch εQ lam lamAssign:ℝ,
        0<αMatch ∧ (2*αMatch)/16≤bmatch ∧
        (2*αMatch)/16≤((ρ₀/4)/40000)*θ/1024 ∧ 2*αMatch≤4*δglobal ∧
        0<εQ ∧ εQ≤εAbs ∧ εQ<1/4 ∧ εQ≤δglobal ∧ βfinal+εQ≤lamList ∧
        εQ≤αMatch/(1000*C₀) ∧ εQ≤(ρ₀/4)/80000 ∧
        0<lam ∧ lam≤θ ∧ lam≤αMatch/128 ∧ lam≤δold*εQ/32 ∧ lam<lamAssign :=by
  obtain ⟨βlist,lamList,ζList,βfinal,δglobal,hβ,hβ1,hlamList,hlamList1,hζ,hβfinal,hβbound,hβfinal1,hδglobal,hδbound,hδ1,hList,hchoose⟩:=
    first_vortex_no_marked_ordered_choices_capped γList pstar hγ hp
  let δold:=δglobal/2
  let δlocal:=δglobal
  let θ:=δglobal/128
  let bmatch:=((ρ₀/4)/40000)/32
  have hδold:0<δold:=by dsimp [δold];positivity
  have hgap:δold<δlocal:=by dsimp [δold,δlocal];linarith
  have hθ:0<θ:=by dsimp [θ];positivity
  have hb:0<bmatch:=by dsimp [bmatch];positivity
  refine ⟨βlist,lamList,ζList,βfinal,δglobal,δold,δlocal,θ,bmatch,
    hβ,hβ1,hlamList,hlamList1,hζ,hβfinal,hβbound,hβfinal1,hδglobal,hδbound,hδ1,
    hδold,hgap,hθ,?_,?_,?_,?_,hb,?_,hList,?_⟩
  · dsimp [θ]; linarith
  · dsimp [θ,δold]; linarith
  · dsimp [θ,δold]; linarith
  · dsimp [θ]; linarith
  · dsimp [bmatch]; linarith
  intro C₀ εAbs hC hAbs
  let εcap:=min εAbs (1/8:ℝ)
  have hcap:0<εcap:=by dsimp [εcap];positivity
  obtain ⟨αMatch,εQ,lam,lamAssign,hα,hαb,hαsmall,hαglobal,hε,hεcap,hεδ,htrim,hεα,hερ,hlam,hlamθ,hlamα,hlamδ,hlamAssign⟩:=
    hchoose bmatch ρ₀ θ δold C₀ εcap hb hρ hθ hδold hC hcap
  have hεAbs:εQ≤εAbs:=hεcap.trans (min_le_left _ _)
  have hεsmall:εQ<1/4:=by
    have hh:εQ≤(1/8:ℝ):=hεcap.trans (min_le_right _ _)
    linarith
  exact ⟨αMatch,εQ,lam,lamAssign,hα,hαb,hαsmall,hαglobal,hε,hεAbs,hεsmall,hεδ,htrim,hεα,hερ,hlam,hlamθ,hlamα,hlamδ,hlamAssign⟩
end Oberwolfach
