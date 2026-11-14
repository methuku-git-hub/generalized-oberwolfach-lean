module

public import Oberwolfach.OrdinaryOriginalPreSampleScaledThresholdsAt
public import Oberwolfach.OrdinaryOriginalPreSampleScaledEditRatesAt

@[expose] public section
/-! After the shared vortex size and failure allowances are fixed, choose
all matching and correction thresholds from the already selected rates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach

theorem ordinary_presample_choose_scaled_thresholds
    (L rstar d m k dMin:ℕ) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hρ1:ρ₀≤1) (hα:0<α) (hθhost:1/2≤θhost)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv:ℝ)
    (hpre:OrdinaryOriginalPreSampleScaledEditRatesAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv)
    (hε:0<εvortex) (habs:εvortex≤εabs) (hv:εvortex≤εv)
    (mv mAbs q₀:ℕ) (ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol:ℝ)
    (hζ:0<ζ) (hχpair:0<χpair) (hχlist:0<χlist) (hχbal:0<χbal) (hχbd:0<χbd)
    (hχnbr:0<χnbr) (hχpairR:0<χpairR) (hχpath:0<χpath) (hχlocal:0<χlocal)
    (hχglobal:0<χglobal) (hχhub:0<χhub) (hχcol:0<χcol):
    OrdinaryOriginalPreSampleScaledThresholdsAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv
      mv mAbs q₀ ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol :=by
  obtain ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,hεchosen,hδcap,hαcap,hearlycap,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    ξedit,ξAbs,hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,htracked,hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt⟩:=hpre
  have hθ:0<θ:=by obtain ⟨_,_,_,_,hθ,_⟩:=hStage; exact hθ
  have hσ:0<σ:=by obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hσ,_⟩:=hStage; exact hσ
  obtain ⟨aAbs,bAbs,hcorr⟩:=hcorrAt mAbs
  obtain ⟨aEvent,haEvent,Nsel,Ncorr,Nc,Ng,Nh,Ncol,Ngeom,hNcorr,hNc,hNg,hNh,hNcol,hNgeom,hsel,hlocal,hgeom⟩:=
    ordinary_matching_correction_common_thresholds rstar m k d K hd βfreq ρ₀ α θ θhost lamMatch aRow γrow ζSel lamSel ζSel smin
      τ tMatch ξMatch bMatch BO hChoice ζ χpair χlist σ χbal χbd χnbr χpairR χpath
      hζ hχpair hχlist hσ hχbal hχbd hχnbr hχpairR hχpath
      mAbs aAbs bAbs (2*mv) mv q₀ αcorr pstar ω εabs εv (2*((3*d:ℕ):ℝ)) ξAbs εvortex hcorr
      hθhost hα hρ₀ hρ1 hβfreq hβ1 hε habs hv (θ/2) χlocal χglobal χhub χcol (2/εvortex)
      (by positivity) hχlocal hχglobal hχhub hχcol (by positivity)
  exact ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,hεchosen,hδcap,hαcap,hearlycap,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    ξedit,ξAbs,hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,htracked,hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt,
    aAbs,bAbs,aEvent,haEvent,Nsel,Ncorr,Nc,Ng,Nh,Ncol,Ngeom,hNcorr,hNc,hNg,hNh,hNcol,hNgeom,hsel,hlocal,hgeom⟩
end Oberwolfach
