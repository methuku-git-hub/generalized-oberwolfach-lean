module

public import Oberwolfach.OrdinaryVortexTwoStepSharpGeometryAtRatesBeforeSampling
public import Oberwolfach.OrdinarySharpFineBalanceRatesChoice
public import Oberwolfach.OrdinarySharpBufferedRootScaleChoiceBeforeSampling

@[expose] public section
/-! Select the root scale before the vortex, and the fine cover scale only
after the packing error is known; all later-parent geometry is then uniform. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_two_step_sharp_geometry_hierarchy_before_sampling
    (mWheel d k:ℕ) (hk:4≤k) (ρ₀ βparent b B εparent gap cap δcut:ℝ)
    (hρ₀:0<ρ₀) (hβparent:0<βparent) (hb:0<b) (hB:0≤B) (hgap:0<gap) (hcap:0<cap) (hδcut:0<δcut):
    ∃βout ξreserve ζout edit:ℝ,0<βout ∧ βout=βparent/2 ∧ 0<ξreserve ∧ 0<ζout ∧ 0<edit ∧ ξreserve≤cap ∧ ζout≤cap ∧
    ∀root βe βh εcap:ℝ,0<root→0<βe→0<βh→0<εcap→
    ∃lam ε:ℝ,0<lam ∧ lam≤root ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧
      lam≤βe/4 ∧ lam≤βh/2 ∧ 3*lam≤edit/4 ∧ lam*((mWheel:ℝ)+1)≤edit/4 ∧
      0<ε ∧ ε≤εcap ∧ ε<1/4 ∧ ε≤ξreserve/2 ∧ ε≤ξreserve*(ρ₀/8)/2 ∧ 2*ε^2≤lam ∧
    ∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
    ∀ηpack loadCap:ℝ,0<ηpack→0<loadCap→∃εout γ aLoad ξroot η₀ ηbal ηInitial βcap δcap:ℝ,
      0<εout ∧ εout≤1 ∧ 0<γ ∧ 0<aLoad ∧ aLoad≤1 ∧ aLoad≤γ/1000 ∧
      aLoad≤edit/(72*((mWheel:ℝ)+2)) ∧ aLoad≤loadCap ∧ ξroot=min (ε/200) (aLoad^2/160) ∧
      0<ξroot ∧ ξroot≤ε/100 ∧ ξroot≤γ/160000 ∧ 80*ξroot≤aLoad^2 ∧
      η₀=δcut*(ρ₀/8)*ξroot/1000 ∧ 0<η₀ ∧ 0<ηbal ∧ ηbal≤η₀ ∧ ηbal≤γ/1000 ∧
      0<ηInitial ∧ ηInitial≤ηbal ∧ 0<βcap ∧ βcap≤1/4 ∧ βcap≤γ/1000 ∧ 0<δcap ∧ δcap≤γ/1000 ∧
    ∀(β εR εH pH:ℝ),0≤β→β≤βcap→0≤εR→εR≤δcap→0≤εH→εH≤δcap→0≤pH→pH≤1→
      OrdinaryVortexTwoStepSharpGeometryAtRatesBeforeSampling mWheel d k β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γ edit p βe βh pH εR εH
        βparent b B εparent gap βout ζout ηpack εout :=by
  obtain ⟨βout,ξreserve,ζout,edit,hβout,hβeq,hξreserve,hζout,hedit,hξcap,hζcap,hgeom⟩:=
    ordinary_vortex_buffered_root_static_geometry_separate_at_scale_choice (mWheel+1) k 2 (by omega)
      ρ₀ βparent b B εparent gap cap hk hρ₀ hβparent hb hB hgap hcap
  refine ⟨βout,ξreserve,ζout,edit,hβout,hβeq,hξreserve,hζout,hedit,hξcap,hζcap,?_⟩
  intro root βe βh εcap hroot hβe hβh hεcap
  let rootCap:ℝ:=min root ((ρ₀/8)/2)
  have hrootCap:0<rootCap:=by dsimp [rootCap];positivity
  obtain ⟨lam,hlam,hlamCap,hlam1,hlame,hlamh,hrow,hlevel,hvortex⟩:=
    ordinary_sharp_buffered_root_scale_choice_before_sampling mWheel rootCap edit βe βh hrootCap hedit hβe hβh
  let epsCap:ℝ:=min εcap (min (ξreserve/2) (ξreserve*(ρ₀/8)/2))
  have hepsCap:0<epsCap:=by dsimp [epsCap];positivity
  obtain ⟨ε,hε,hεcap,hε1,hεroot⟩:=hvortex epsCap hepsCap
  have hlamroot:lam≤root:=hlamCap.trans (min_le_left _ _)
  have hlamρ:lam≤(ρ₀/8)/2:=hlamCap.trans (min_le_right _ _)
  have hεcap':ε≤εcap:=hεcap.trans (min_le_left _ _)
  have hεξ:ε≤ξreserve/2:=hεcap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hερ:ε≤ξreserve*(ρ₀/8)/2:=hεcap.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨lam,ε,hlam,hlamroot,hlam1,hlamρ,hlame,hlamh,hrow,hlevel,hε,hεcap',hε1,hεξ,hερ,hεroot,?_⟩
  intro pcap hpcap
  obtain ⟨p,hp,hp1,hpcap,hgeom⟩:=hgeom pcap hpcap
  refine ⟨p,hp,hp1,hpcap,?_⟩
  intro ηpack loadCap hηpack hloadCap
  obtain ⟨εout,γ,hεout,hεout1,hγ,hgeom⟩:=hgeom ηpack hηpack
  let aCap:ℝ:=min (edit/(72*((mWheel:ℝ)+2))) loadCap
  have haCap:0<aCap:=by dsimp [aCap];positivity
  obtain ⟨aLoad,ξroot,η₀,ηbal,ηInitial,ha,ha1,hacap,haγ,hξeq,hξ,hξγ,hηeq,hη₀,hηbal,hηbalcap,hηγ,hηInitial,hηInitialCap,hsmall,hsmall'⟩:=
    ordinary_sharp_fine_balance_rates_choice ε δcut ρ₀ γ aCap hε hδcut hρ₀ hγ haCap
  have hacapEdit:aLoad≤edit/(72*((mWheel:ℝ)+2)):=hacap.trans (min_le_left _ _)
  have hacapLoad:aLoad≤loadCap:=hacap.trans (min_le_right _ _)
  have hξeps:ξroot≤ε/100:=by rw [hξeq];have hh:=min_le_left (ε/200) (aLoad^2/160);linarith
  have hξload:80*ξroot≤aLoad^2:=by rw [hξeq];have hh:=min_le_right (ε/200) (aLoad^2/160);nlinarith [sq_nonneg aLoad]
  let βcap:ℝ:=min (1/8:ℝ) (γ/2000)
  let δcap:ℝ:=γ/2000
  have hβcap:0<βcap:=by dsimp [βcap];positivity
  have hβcap1:βcap≤1/4:=by have hh:=min_le_left (1/8:ℝ) (γ/2000);dsimp [βcap];linarith
  have hβcapγ:βcap≤γ/1000:=by have hh:=min_le_right (1/8:ℝ) (γ/2000);dsimp [βcap];linarith
  have hδcap:0<δcap:=by dsimp [δcap];positivity
  have hδcapγ:δcap≤γ/1000:=by dsimp [δcap];linarith
  refine ⟨εout,γ,aLoad,ξroot,η₀,ηbal,ηInitial,βcap,δcap,hεout,hεout1,hγ,ha,ha1,haγ,hacapEdit,hacapLoad,hξeq,hξ,hξeps,hξγ,hξload,
    hηeq,hη₀,hηbal,hηbalcap,hηγ,hηInitial,hηInitialCap,hβcap,hβcap1,hβcapγ,hδcap,hδcapγ,?_⟩
  intro β εR εH pH hβ hβsmall hεR hεRsmall hεH hεHsmall hpH hpH1
  exact ordinary_vortex_two_step_sharp_geometry_from_rates_before_sampling mWheel d k β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γ edit p βe βh pH εR εH
    βparent b B εparent gap βout ζout ηpack εout hgeom hβ (hβsmall.trans hβcap1) hε hε1 hρ₀ hγ hlam.le hlam1 hlamρ hξreserve.le hεξ hερ hεroot
    hβe.le hβh.le hp.le hpH hpH1 hεR hεH hξ.le ha.le hηbal.le hηInitial.le hedit (hβsmall.trans hβcapγ)
    (hεRsmall.trans hδcapγ) (hεHsmall.trans hδcapγ) hξγ haγ hηγ hηInitialCap hrow hlevel hacapEdit hlame hlamh
end Oberwolfach
