module

public import Oberwolfach.FirstVortexEarlyAlphaVortexCap

@[expose] public section
/-! Choose the matching robustness and one vortex scale below the level,
selector, balance and ambient caps, before the later matching spacing. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_initial_matching_vortex_choice
    (ρ₀ δglobal βList βfinal εLevel εInner εAbs εRob γRich kstar tstar hostCap:ℝ)
    (hρ:0<ρ₀) (hδ:0<δglobal) (hList:0<βList) (hβ:0≤βfinal) (hβList:βfinal≤βList/4)
    (hLevel:0<εLevel) (hInner:0<εInner) (hAbs:0<εAbs) (hRob:0<εRob)
    (hγ:0<γRich) (hk:0<kstar) (ht:0<tstar) (hHost:0<hostCap):
    ∃bmatch α ε:ℝ,0<bmatch ∧ bmatch≤((ρ₀/4)/40000)/16 ∧
      0<α ∧ (2*α)/16≤bmatch ∧ 2*α≤4*δglobal ∧
      0<ε ∧ ε<1/4 ∧ ε≤εLevel ∧ ε≤εInner ∧ ε≤εAbs ∧ ε≤εRob ∧ ε≤hostCap ∧
      ε≤min ((γRich/2)*kstar) tstar/128 ∧ ε≤(2*α)/100000 ∧
      ε≤α/1000 ∧ ε≤(ρ₀/4)/80000 ∧ ε≤((ρ₀/4)/40000)/8192 ∧
      ε≤δglobal ∧ βfinal+ε≤βList :=by
  let bmatch:=((ρ₀/4)/40000)/32
  have hb:0<bmatch:=by dsimp [bmatch];positivity
  have hbcap:bmatch≤((ρ₀/4)/40000)/16:=by dsimp [bmatch];linarith
  let small:=min ((γRich/2)*kstar) tstar/128
  have hsmall:0<small:=by dsimp [small];positivity
  let cap:=min εLevel (min εInner (min εAbs (min εRob (min hostCap small))))
  have hcap:0<cap:=by dsimp [cap];positivity
  obtain ⟨α,εupper,hα,hαb,hαδ,hupper,hupperCap,hupperδ,hupperList,hupperα,hupperρ,hupperPrecise⟩:=
    first_vortex_early_alpha_vortex_cap bmatch ρ₀ δglobal βList βfinal cap hb hρ hδ hList hβ hβList hcap
  let ε:=min εupper (min (α/50000) (1/8:ℝ))
  have hε:0<ε:=by dsimp [ε];positivity
  have hεupper:ε≤εupper:=min_le_left _ _
  have hεα:ε≤α/50000:=(min_le_right _ _).trans (min_le_left _ _)
  have hε8:ε≤1/8:=(min_le_right _ _).trans (min_le_right _ _)
  have hεcap:ε≤cap:=hεupper.trans hupperCap
  have hεLevel:ε≤εLevel:=hεcap.trans (min_le_left _ _)
  have hεInner:ε≤εInner:=hεcap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεAbs:ε≤εAbs:=hεcap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεRob:ε≤εRob:=hεcap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hεHost:ε≤hostCap:=hεcap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hεsmall:ε≤small:=hεcap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  refine ⟨bmatch,α,ε,hb,hbcap,hα,hαb,hαδ,hε,by linarith,hεLevel,hεInner,hεAbs,hεRob,hεHost,hεsmall,?_,
    hεupper.trans hupperα,hεupper.trans hupperρ,hεupper.trans hupperPrecise,hεupper.trans hupperδ,?_⟩ <;> linarith
end Oberwolfach
