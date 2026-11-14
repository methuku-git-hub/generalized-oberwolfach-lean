module

public import Oberwolfach.OrdinaryOriginalPreSampleStrongHostAt
public import Oberwolfach.OrdinaryDeepParentVortexBalanceOriginalProbability
public import Oberwolfach.OriginalRegularHostFactorCount

@[expose] public section
/-! The original regular host assumptions and one shared failure allowance
supply the matching-correction-parent-balance bundle at the original bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_presample_strong_original_host
    (L rstar d m k dMin:ℕ) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α) (hθhost:1/2≤θhost)
    (βPlace lamPlace ζPlace ε:ℝ)
    (εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv:ℝ)
    (mv mAbs:ℕ) (t χ:ℝ)
    (βv:ℝ) (Kdeep:ℕ) (αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom eParent hParent εR εH capDeep:ℝ)
    (kParent:ℕ) (hmParent:3≤rstar-1) (βP ηP row ηH βH cParent Bparent εTri δref href:ℝ)
    (hpstar:0<ρ₀*(βfreq/200)/2)
    (Nbudget:ℕ)
    (hbudget:∀n:ℕ,Nbudget≤n→∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (E:Ω→Prop),
      1-(23*t+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2))≤μ.probability E→
      1-χ-1/(n:ℝ)^10≤μ.probability E)
    (hpre:OrdinaryOriginalPreSampleWithBundleAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace ε εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv
      mv mAbs 10 t t t t t t t t t t t t
      βv Kdeep αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom t t eParent hParent εR εH t t t capDeep
      kParent hmParent βP ηP row ηH βH cParent Bparent εTri t δref href t hpstar t):
    OrdinaryOriginalPreSampleStrongHostAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace ε εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv
      mv mAbs 10 t t t t t t t t t t t t
      βv Kdeep αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom t t eParent hParent εR εH t t t capDeep
      kParent hmParent βP ηP row ηH βH cParent Bparent εTri t δref href t hpstar t χ :=by
  obtain ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    ξedit,ξAbs,hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt,
    aAbs,bAbs,aEvent,haEvent,Nsel,Ncorr,Nc,Ng,Nh,Ncol,Ngeom,hNcorr,hNc,hNg,hNh,hNcol,hNgeom,hsel,hlocal,hgeom,
    Nhost,h2,hselN,hcorrN,hgeomN,hmvN,huse⟩:=hpre
  let Nall:=max Nhost Nbudget
  refine ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    ξedit,ξAbs,hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt,
    aAbs,bAbs,aEvent,haEvent,Nsel,Ncorr,Nc,Ng,Nh,Ncol,Ngeom,hNcorr,hNc,hNg,hNh,hNcol,hNgeom,hsel,hlocal,hgeom,
    Nall,by omega,by omega,by omega,by omega,by omega,?_⟩
  intro n qCount D hn F hF habundance hρlo hρhi hthreshold P hreg hdegree
  have hnpos:0<n:=by omega
  have hρhi':2*(qCount:ℝ)/(D:ℝ)≤1:=by simpa [initialIndexDensity] using hρhi
  have hq:qCount≤n:=(original_regular_host_factor_count hnpos P hreg θhost α hθhost hα hdegree hρhi').2.2
  have hraw:=huse n qCount D (by omega) hq F hF habundance hρlo hρhi hthreshold P hreg hdegree
  exact ordinary_deep_parent_vortex_balance_original_probability n qCount D rstar m k d K mv mAbs aAbs bAbs Nc Ng Nh Ncol hd
    βfreq ρ₀ α θ θhost lamMatch aRow γrow ζSel lamSel ζSel τ tMatch ξMatch bMatch σ aEvent εvortex εabs εv βv ξAbs
    BO F hF P Kdeep αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom eParent hParent εR εH capDeep
    kParent hmParent βP ηP row ηH βH cParent Bparent εTri δref href hpstar t χ (hbudget n (by omega)) hraw
end Oberwolfach
