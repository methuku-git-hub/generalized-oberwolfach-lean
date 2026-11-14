module

public import Oberwolfach.FirstVortexSpacingClassRetentionChoices
public import Oberwolfach.FirstVortexNoMarkedFinalCap
public import Oberwolfach.FirstVortexMatchingClassCapWithUpper

@[expose] public section
/-! Fix list and spacing scales before the host event; choose the vortex
rate afterward below any positive event-supplied cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_early_host_parameters_with_prepared_cap
    (r:ℕ) (γList pstar ρ₀ βFinalCap:ℝ) (hγ:0<γList) (hp:0<pstar) (hρ:0<ρ₀) (hCap:0<βFinalCap):
    ∃βlist lamList ζList βfinal δglobal δold δlocal θ bmatch:ℝ,
      0<βlist ∧ βlist≤1 ∧ 0<lamList ∧ lamList≤1/100 ∧ 0<ζList ∧
      0<βfinal ∧ βfinal≤lamList/4 ∧ βfinal≤1 ∧ βfinal≤βFinalCap ∧
      0<δglobal ∧ δglobal≤(βfinal/200)^2 ∧ δglobal≤(βfinal/100)^2 ∧ δglobal≤1/100 ∧
      0<δold ∧ δold≤1 ∧ δold<δlocal ∧ 0<θ ∧ θ≤1/100 ∧ 10*θ≤δold ∧ θ≤δold/32 ∧ 10*θ≤δglobal ∧
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
      ∀C₀ εAbs εOther ξUpper:ℝ,1≤C₀→0<εAbs→0<εOther→0<ξUpper→∃αMatch εQ lam lamAssign ξCap:ℝ,
        0<αMatch ∧ (2*αMatch)/16≤bmatch ∧
        (2*αMatch)/16≤((ρ₀/4)/40000)*θ/1024 ∧ 2*αMatch≤4*δglobal ∧
        0<εQ ∧ εQ≤εAbs ∧ εQ≤εOther ∧ εQ<1/4 ∧ εQ≤δglobal ∧ βfinal+εQ≤lamList ∧
        εQ≤αMatch/(1000*C₀) ∧ εQ≤αMatch/1000 ∧ εQ≤(ρ₀/4)/80000 ∧ εQ≤((ρ₀/4)/40000)/8192 ∧
        0<lam ∧ lam≤θ ∧ lam≤αMatch/128 ∧ lam≤δold*εQ/32 ∧ lam<lamAssign ∧
        0<ξCap ∧ ξCap≤ξUpper ∧
        (∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρ₀/4)/40000)*θ/4096 ∧
          ξ'/2≤(lamAssign-lam)*εQ ∧ ξ'≤αMatch/32 ∧
          ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
            (Q:Vortex U G D β εQ mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ)) :=by
  obtain ⟨βlist,lamList,ζList,βfinal,δbase,hβ,hβ1,hlamList,hlamList1,hζ,hβfinal,hβbound,hβfinal1,hβcap,hδbase,hδbaseBound,hδbase1,hList,hchooseBase⟩:=
    first_vortex_no_marked_ordered_choices_final_cap γList pstar βFinalCap hγ hp hCap
  let δglobal:=min δbase ((βfinal/200)^2)/2
  have hδglobal:0<δglobal:=by dsimp [δglobal];positivity
  have hδbaseLe:δglobal≤δbase:=by
    have h:=min_le_left δbase ((βfinal/200)^2)
    dsimp [δglobal];linarith
  have hδstrong:δglobal≤(βfinal/200)^2:=by
    have h:=min_le_right δbase ((βfinal/200)^2)
    have hs:0≤(βfinal/200)^2:=sq_nonneg _
    dsimp [δglobal];linarith
  have hδbound:δglobal≤(βfinal/100)^2:=hδbaseLe.trans hδbaseBound
  have hδ1:δglobal≤1/100:=hδbaseLe.trans hδbase1
  let δold:=δglobal/2
  let δlocal:=δglobal
  let θ:=δglobal/128
  let bmatch:=((ρ₀/4)/40000)/32
  have hδold:0<δold:=by dsimp [δold];positivity
  have hgap:δold<δlocal:=by dsimp [δold,δlocal];linarith
  have hθ:0<θ:=by dsimp [θ];positivity
  have hb:0<bmatch:=by dsimp [bmatch];positivity
  obtain ⟨dMin,hList⟩:=hList
  obtain ⟨d,K,hd3,hdMin,hdlarge,hK,hspacing,hcut,hcutHost,ζret,hζret,hζretBound,Nret,hNret⟩:=
    first_vortex_spacing_class_retention_choices r dMin θ hθ
  obtain ⟨Nlist,hNlist⟩:=hList d hdMin (by omega)
  refine ⟨βlist,lamList,ζList,βfinal,δglobal,δold,δlocal,θ,bmatch,
    hβ,hβ1,hlamList,hlamList1,hζ,hβfinal,hβbound,hβfinal1,hβcap,hδglobal,hδstrong,hδbound,hδ1,
    hδold,?_,hgap,hθ,?_,?_,?_,?_,hb,?_,d,K,hd3,hdlarge,hK,hspacing,hcut,hcutHost,ζret,hζret,hζretBound,Nret,Nlist,hNret,hNlist,?_⟩
  · dsimp [δold]; linarith
  · dsimp [θ]; linarith
  · dsimp [θ,δold]; linarith
  · dsimp [θ,δold]; linarith
  · dsimp [θ]; linarith
  · dsimp [bmatch]; linarith
  intro C₀ εAbs εOther ξUpper hC hAbs hOther hξUpper
  let precise:=((ρ₀/4)/40000)/8192
  let εcap:=min εAbs (min εOther (min (1/8:ℝ) precise))
  have hcap:0<εcap:=by dsimp [εcap,precise];positivity
  obtain ⟨αMatch,εQ,lamOld,lamAssign,hα,hαb,hαsmall,hαglobal,hε,hεcap,hεδ,htrim,hεα,hερ,hlamOld,hlamθOld,hlamαOld,hlamδOld,hAssignOld⟩:=
    first_vortex_no_marked_parameter_choices_capped bmatch ρ₀ θ δold δglobal lamList βfinal C₀ εcap
      hb hρ hθ hδold hδglobal hcap hlamList hβfinal.le hβbound hC
  have hεAbs:εQ≤εAbs:=hεcap.trans (min_le_left _ _)
  have hεOther:εQ≤εOther:=hεcap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεsmall:εQ<1/4:=by
    have hh:εQ≤(1/8:ℝ):=hεcap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hεprecise:εQ≤((ρ₀/4)/40000)/8192:=by
    exact hεcap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hεαsimple:εQ≤αMatch/1000:=by
    have hp:0<(1000:ℝ)*C₀:=by positivity
    have hh:εQ*(1000*C₀)≤αMatch:=(le_div_iff₀ hp).mp hεα
    have hm:0≤εQ*(C₀-1):=mul_nonneg hε.le (by linarith)
    nlinarith
  have hAssign:0<lamAssign:=by linarith
  obtain ⟨lam,ξCap,hlam,hξ,hlamUpper,hξUpper',hlamθ,hlamα,hlamδ,hCap⟩:=
    first_vortex_matching_class_cap_with_upper αMatch lamAssign εQ δold δlocal θ ρ₀ lamOld ξUpper
      hα hAssign hε hδold hgap hθ hρ hlamOld hξUpper
  have hAssign':lam<lamAssign:=lt_of_le_of_lt hlamUpper hAssignOld
  exact ⟨αMatch,εQ,lam,lamAssign,ξCap,hα,hαb,hαsmall,hαglobal,hε,hεAbs,hεOther,hεsmall,hεδ,htrim,hεα,hεαsimple,hερ,hεprecise,hlam,hlamθ,hlamα,hlamδ,hAssign',hξ,hξUpper',hCap⟩
end Oberwolfach
