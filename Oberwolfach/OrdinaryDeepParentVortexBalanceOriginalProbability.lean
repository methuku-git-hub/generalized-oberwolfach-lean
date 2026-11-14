module

public import Oberwolfach.OrdinaryDeepParentVortexBalanceStrongAt
public import Oberwolfach.OrdinaryOriginalDeepParentVortexBalanceBundleAt
public import Oberwolfach.OrdinaryDeepParentEqualFailureAllowances

@[expose] public section
/-! Upgrade the actual common-sample event to the original probability
bound after selecting the positive failure allowances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_parent_vortex_balance_original_probability
    (n qCount D rstar m k d K mv mAbs aAbs bAbs Nc Ng Nh Ncol:ℕ) (hd:2≤d)
    (βfreq ρ₀ α θ θhost lam aRow γ cap lamList ζDel τ tMatch ξMatch bMatch σ aEvent ε εabs εv βv ξAbs:ℝ)
    (BO:Fin K→ℝ)
    (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (P:SimpleGraph (Fin n))
    (Kdeep:ℕ) (αcut c C a ε₀ ρdeep θdeep aLoad ξdeep b Bweight ηHub Kdom eParent hParent εR εH capDeep:ℝ)
    (kParent:ℕ) (hmParent:3≤rstar-1)
    (βP ηP row ηH βH cParent Bparent εTri δref href:ℝ)
    (hpstar:0<ρ₀*(βfreq/200)/2) (t χ:ℝ)
    (hbudget:∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (E:Ω→Prop),
      1-(23*t+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2))≤μ.probability E→
      1-χ-1/(n:ℝ)^10≤μ.probability E)
    (hBundle:OrdinaryOriginalDeepParentVortexBalanceBundleAt n qCount D rstar m k d K mv mAbs aAbs bAbs 10 Nc Ng Nh Ncol hd
      βfreq ρ₀ α θ θhost lam aRow γ cap lamList ζDel τ tMatch ξMatch bMatch σ t t t t t t t t aEvent ε εabs εv βv ξAbs t t t t
      BO F hF P Kdeep αcut c C a ε₀ ρdeep θdeep aLoad ξdeep b Bweight ηHub Kdom t t eParent hParent εR εH t t t capDeep
      kParent hmParent βP ηP row ηH βH cParent Bparent εTri t δref href t hpstar t):
    OrdinaryOriginalDeepParentVortexBalanceStrongAt n qCount D rstar m k d K mv mAbs aAbs bAbs 10 Nc Ng Nh Ncol hd
      βfreq ρ₀ α θ θhost lam aRow γ cap lamList ζDel τ tMatch ξMatch bMatch σ t t t t t t t t aEvent ε εabs εv βv ξAbs t t t t
      BO F hF P Kdeep αcut c C a ε₀ ρdeep θdeep aLoad ξdeep b Bweight ηHub Kdom t t eParent hParent εR εH t t t capDeep
      kParent hmParent βP ηP row ηH βH cParent Bparent εTri t δref href t hpstar t χ :=by
  obtain ⟨Qlook,π,hπ,hshort,hall⟩:=hBundle
  refine ⟨Qlook,π,hπ,hshort,?_⟩
  intro density tR tH Q
  obtain ⟨i₀,rsv,Cres,sampling,w,seed,hmatch,hcorr,hlevel,selection,hprob⟩:=hall density tR tH
  refine ⟨i₀,rsv,Cres,sampling,w,seed,hmatch,hcorr,hlevel,selection,?_⟩
  intro R _ ν p p₂ q s μ E loss0 loss Good All
  obtain ⟨weight,hweight,hbound⟩:=hprob (R:=R) ν
  refine ⟨weight,hweight,?_⟩
  apply hbudget _ _ _
  linarith only [hbound]
end Oberwolfach
