module

public import Oberwolfach.OrdinaryDeepCommonRatesBeforeFailureScaled
public import Oberwolfach.OrdinaryOriginalPreSampleFixedJointRatesAt

@[expose] public section
/-! The nontriangle deep-event cap, matching edit rate and correction rate
are selected together before failure allowances, retaining the same early
placement witnesses and both distinct list parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_joint_early_matching_rates
    (L rstar mWheel Kdeep d m k dMin:ℕ) (hd:2≤d) (hr:3≤rstar)
    (βfreq ρ₀ αOriginal γList capInner capEdit θhost:ℝ)
    (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hαOriginal:0<αOriginal)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hTail:OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ αOriginal γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly)
    (αdeep pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (hdeep:OrdinaryDeepRowsCutsEarlyBeforeFailure mWheel Kdeep αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep)
    (aLoad ε ξdeep bHub Bweight ηHub Kdom eParent hParent εR εH ηBudget:ℝ)
    (haLoad:0<aLoad) (haLoadA:aLoad≤a) (hε:0<ε) (hε1:ε<1/4) (hεa:ε≤a) (hερ:ε≤ρ₀/16)
    (hξ:0<ξdeep) (hK:2/ε≤Kdom) (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom)
    (hb:bHub≤c) (hB:(4*C/pmin^(3*mWheel+1))*Kdom^mWheel≤Bweight)
    (he:0<eParent) (hh:0<hParent) (hεR:0<εR) (hεH:0<εH) (hηBudget:0<ηBudget)
    (αcorr pstar ω δAbs hAbs εabs εv:ℝ)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly rstar αcorr pstar ω δAbs hAbs εabs εv):
    ∃t eEvent hEvent cap ξedit ξAbs:ℝ,
      0<t ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧ eEvent≤eParent ∧ hEvent≤hParent ∧
      (∀χinner χdeep χone χtwo χcut:ℝ,0<χinner→0<χdeep→0<χone→0<χtwo→0<χcut→
        OrdinaryDeepRowsCutsAfterParameters mWheel Kdeep αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
          aLoad ε ξdeep bHub Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap) ∧
      OrdinaryOriginalPreSampleFixedJointRatesAt L rstar d m k dMin βfreq ρ₀ αOriginal γList capInner capEdit θhost
        hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly ε cap ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs :=by
  obtain ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd',hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns⟩:=hTail
  have hσ:0<σ:=by obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hσ,_⟩:=hStage;exact hσ
  let αCap:=5*ρ₀*(βfreq/200)^2/128
  let cBudget:=min (1/1024:ℝ) (min (αCap/4096) (1/2:ℝ)/8)
  let capExtra:=min σ (ηBudget/1000)
  have hExtra:0<capExtra:=by dsimp [capExtra];positivity
  obtain ⟨t,eEvent,hEvent,cap,ξedit,ξAbs,ht,hevent,hhevent,hcap,hebound,hhbound,
    hξedit,hξcap,hξscale,hξextra,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbscap,hξAbsscale,hξAbsextra,hξAbsh,hcorrAt,hselect⟩:=
    ordinary_deep_common_rates_before_failure_scaled rstar mWheel Kdeep d m hd αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep hdeep
      aLoad ε ξdeep bHub Bweight ηHub Kdom eParent hParent εR εH haLoad haLoadA hε hε1 hεa hερ hξ hK hKdom hb hB he hh hεR hεH
      lamPlace ζPlace b εearly cBudget θ z δ aRow γrow (θ/2) bMatch αCap hColumns
      αcorr pstar ω δAbs hAbs εabs εv capExtra hExtra hcorr
  have hξσ:ξedit≤σ:=hξextra.trans (min_le_left _ _)
  have hξη:ξedit≤ηBudget/1000:=hξextra.trans (min_le_right _ _)
  have hξAbsσ:ξAbs≤σ:=hξAbsextra.trans (min_le_left _ _)
  have hξAbsη:ξAbs≤ηBudget/1000:=hξAbsextra.trans (min_le_right _ _)
  refine ⟨t,eEvent,hEvent,cap,ξedit,ξAbs,ht,hevent,hhevent,hcap,hebound,hhbound,hselect,?_⟩
  exact ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd',hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    hξedit,hξscale,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbsscale,hξAbsη,hξAbsσ,hξAbsh,hcorrAt⟩
end Oberwolfach
