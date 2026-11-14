module

public import Oberwolfach.OrdinaryOriginalPreSampleJointShape

@[expose] public section
/-! Complete the joint parameter selection by fixing the matching deletion
budget and one edit rate before absorber sizes, factors and the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach

theorem ordinary_original_presample_from_joint
    (L rstar:ℕ) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3 ≤ rstar) (hβfreq:0<βfreq) (hβ1:βfreq ≤ 1) (hρ₀:0<ρ₀) (hα:0<α)
    (hJoint:OrdinaryOriginalSelectorPlacementJointShape L rstar βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα):
    OrdinaryOriginalPreSampleJointShape L rstar βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα :=by
  obtain ⟨m,k,βPlace,lamPlace,ζPlace,ε,dMin,hAt,hEarly,δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,
    βSel,lamSel,ζSel,smin,d,K,rank,hSpacing,ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect⟩:=hJoint
  obtain ⟨τ,tMatch,ξMatch,bMatch,hChoice⟩:=ordinary_original_threshold_choose_match_core
    rstar m k d K hd βfreq ρ₀ α θ θhost lamMatch aRow γrow ζSel lamSel ζSel smin BO hSelect
  have hbMatch:0<bMatch:=hChoice.2.2.2.1
  have hEdit:=ordinary_selected_uniform_edit_before_absorber L rstar m k dNeed dMin d K rank
    βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα hAt γList (βfreq/200) capInner βPlace lamPlace ζPlace ε hEarly
    capEdit δ θ κ b z matchErr σ κ' hStage βSel lamSel ζSel smin hSpacing lamMatch aRow γrow hMatching bMatch hbMatch
  exact ⟨m,k,βPlace,lamPlace,ζPlace,ε,dMin,hAt,hEarly,δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,
    βSel,lamSel,ζSel,smin,d,K,rank,hSpacing,ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,
    τ,tMatch,ξMatch,bMatch,hChoice,hEdit⟩
end Oberwolfach
