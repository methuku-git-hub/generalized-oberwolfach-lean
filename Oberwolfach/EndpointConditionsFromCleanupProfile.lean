module

public import Oberwolfach.EndpointPhysicalEditedConditions
public import Oberwolfach.OrdinaryPhysicalFullChangeBounds
public import Oberwolfach.OrdinaryPhysicalConflictDegree
public import Oberwolfach.EndpointBalanceFromDifference

@[expose] public section
/-! The physical endpoint edit and balance inputs follow from the same
cleanup profile and the original additive parent balance estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem endpoint_conditions_from_cleanup_profile
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (κ p pR pH density tR tH L Ledit βe βh δ e:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH Ledit βe βh s j σ)
    (hA:0<A.card) (hQ:Q≤P\F) (hκ:0<κ) (hp:0<p) (hL:0≤L) (hLedit:0≤Ledit) (hδ:0≤δ)
    (hB:κ*A.card≤(B.card:ℝ)) (hBA:B.card≤A.card)
    (hpR:p≤pR) (hpR1:pR≤1) (hpH:p≤pH) (hpH1:pH≤1)
    (hF:∀v,(F.degree v:ℝ)≤L)
    (hparent:∀v,|pR*(A∩P.neighborFinset v).card-2*pH*B.card|≤e)
    (hmargin:e≤δ*(2*B.card*pH)):
    EndpointPhysicalEditedConditions P Q F H A B Aᶜ π d j κ p pR pH L Ledit δ σ:=by
  have hedit:=ordinary_physical_full_change_bounds (rawWheelGraph P σ) Q (rawWheelSpokes π d σ j) H Ledit
    hLedit profile.rim_edit profile.spoke_row_edit profile.spoke_column_edit
  have hconf:=ordinary_physical_conflict_degree (U:=U) F L hL hF
  have hsub:(ordinaryPhysicalGraph (U:=U) Q (fun _ _=>False))≤
      (ordinaryPhysicalGraph P (fun _ _=>False))\(ordinaryPhysicalGraph F (fun _ _=>False)):=by
    intro x y hxy
    cases x <;> cases y <;> simp only [ordinaryPhysicalGraph,SimpleGraph.sdiff_adj] at *
    exact hQ hxy
  have ha0:(0:ℝ)<A.card:=Nat.cast_pos.mpr hA
  have hb0:(0:ℝ)<B.card:=(mul_pos hκ ha0).trans_le hB
  have hpH0:0<pH:=hp.trans_le hpH
  refine ⟨hA,hsub,hκ,hp,hL,hLedit,hδ,hB,hBA,hpR,hpR1,hpH,hpH1,hconf,?_,hedit.1,hedit.2⟩
  intro x hx
  apply endpoint_balance_from_difference _ _ e δ (by positivity) _ hmargin
  simpa only [show 2*(B.card:ℝ)*pH=2*pH*B.card by ring] using hparent x
end Oberwolfach
