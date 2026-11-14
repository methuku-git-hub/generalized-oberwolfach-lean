module

public import Oberwolfach.OrdinaryOriginalPreSampleFixedBundleAt
public import Oberwolfach.OrdinaryOriginalPreSampleFixedPreparationBundleAt
public import Oberwolfach.OrdinaryOriginalTerminalConditionalPreparationNamed
public import Oberwolfach.OrdinarySelectedUniformEditBeforeAbsorber

@[expose] public section
/-! Retain the original same-sample conditional preparation callback beside
the selected correction, parent and balance probability bundle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_presample_attach_fixed_conditional_preparation
    (L rstar d m k dMin:ℕ) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α)
    (βPlace lamPlace ζPlace ε:ℝ)
    (εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv:ℝ)
    (mv mAbs q₀:ℕ) (ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol:ℝ)
    (βv:ℝ) (Kdeep:ℕ) (αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep:ℝ)
    (kParent:ℕ) (hmParent:3≤rstar-1) (βP ηP row ηH βH cParent Bparent εTri χhost δref href χref:ℝ)
    (hpstar:0<ρ₀*(βfreq/200)/2) (χthree:ℝ)
    (rate ξroot ξedit:ℝ) (hθhost:(1/2:ℝ)≤θhost) (hε:0<εvortex) (hεearly:εvortex≤ε)
    (hrate:0≤rate) (hξroot:0≤ξroot)
    (hAt:OrdinaryOriginalThresholdFamilyAt L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα m k)
    (hEarly:OrdinaryPlacementEarlyRateData (α/2) ρ₀ (βfreq/200) capInner βPlace lamPlace ζPlace ε dMin)
    (hBundle:OrdinaryOriginalPreSampleFixedBundleAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace ε εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv
      mv mAbs q₀ ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol
      βv Kdeep αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep
      kParent hmParent βP ηP row ηH βH cParent Bparent εTri χhost δref href χref hpstar χthree ξedit):
    OrdinaryOriginalPreSampleFixedPreparationBundleAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace ε εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv
      mv mAbs q₀ ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol
      βv Kdeep αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep
      kParent hmParent βP ηP row ηH βH cParent Bparent εTri χhost δref href χref hpstar χthree rate ξroot ξedit :=by
  obtain ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    ξAbs,hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt,
    aAbs,bAbs,aEvent,haEvent,Nsel,Ncorr,Nc,Ng,Nh,Ncol,Ngeom,hNcorr,hNc,hNg,hNh,hNcol,hNgeom,hsel,hlocal,hgeom,
    Nhost,h2,hselN,hcorrN,hgeomN,hmvN,hhost⟩:=hBundle
  have hm:7≤m:=hAt.2.1
  have hSpacingKeep:=hSpacing
  obtain ⟨_,_,_,_,_,_,hdMin,_,_,hK,_,_,_,_,hda,_,_,_⟩:=hSpacing
  have hprep:=ordinary_original_terminal_conditional_preparation_named rstar m k d K dMin dNeed N hm hd (by omega) hdMin
    βfreq ρ₀ α θhost capInner βPlace lamPlace ζPlace ε εvortex βv hβfreq hρ₀ hα hθhost hε hεearly hEarly
    capEdit δ θ κ b z matchErr σ κ' ζret lamMatch aRow γrow ξedit bMatch hStage hAfter hMatching hda hcolumnsAt
    hξedit (by omega) rate ξroot hrate hξroot mAbs (2*mv) aAbs bAbs
  exact ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacingKeep,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    ξAbs,hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt,
    aAbs,bAbs,aEvent,haEvent,Nsel,Ncorr,Nc,Ng,Nh,Ncol,Ngeom,hNcorr,hNc,hNg,hNh,hNcol,hNgeom,hsel,hlocal,hgeom,hprep,
    Nhost,h2,hselN,hcorrN,hgeomN,hmvN,hhost⟩
end Oberwolfach
