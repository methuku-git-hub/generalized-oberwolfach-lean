module

public import Oberwolfach.MarkedCommonConfigurationHostInclusion
public import Oberwolfach.MarkedRimTypedIntersection
public import Oberwolfach.MarkedSpokeCommonSubhost
public import Oberwolfach.MarkedTypedLossFromSymmetricChanges

@[expose] public section
/-! Common configurations survive realized physical changes, including
additions, through the original-sample/modified-host typed intersection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_common_configurations_error_mono
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (β ζ ζ':ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (hζ:ζ≤ζ')
    (hc:MarkedCommonConfigurationsWithSpokes r P π d β ζ σ H):
    MarkedCommonConfigurationsWithSpokes r P π d β ζ' σ H :=by
  have hn:0≤(Fintype.card V:ℝ):=by positivity
  have ha:(r+5:ℝ)*ζ≤(r+5:ℝ)*ζ':=mul_le_mul_of_nonneg_left hζ (by positivity)
  have hb:(r+4:ℝ)*ζ≤(r+4:ℝ)*ζ':=mul_le_mul_of_nonneg_left hζ (by positivity)
  refine ⟨?_,?_,?_⟩
  · intro C hC
    have hh:=hc.1 C hC
    have hc':(32*β-(r+5:ℝ)*ζ')*(Fintype.card V:ℝ)≤(32*β-(r+5:ℝ)*ζ)*(Fintype.card V:ℝ):=
      mul_le_mul_of_nonneg_right (by linarith) hn
    push_cast at hh ⊢
    exact hc'.trans hh
  · intro u hu
    have hh:=hc.2.1 u hu
    have hc':(16*β-2*(r+5:ℝ)*ζ')*(Fintype.card V:ℝ)^(r+5)≤
        (16*β-2*(r+5:ℝ)*ζ)*(Fintype.card V:ℝ)^(r+5):=
      mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hn _)
    push_cast at hh ⊢
    exact hc'.trans hh
  · intro v v' hv u hu j
    have hh:=hc.2.2 v v' hv u hu j
    have hc':(16*β-2*(r+4:ℝ)*ζ')*(Fintype.card V:ℝ)^(r+4)≤
        (16*β-2*(r+4:ℝ)*ζ)*(Fintype.card V:ℝ)^(r+4):=
      mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hn _)
    push_cast at hh ⊢
    exact hc'.trans hh

theorem marked_common_configurations_after_host_change
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (β ξ ζ:ℝ)
    (hζ:0≤ζ) (hn:0<Fintype.card V)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hRim:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈FR.edgeFinset)
    (hSpoke:∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hDR:∀ v,(FR.degree v:ℝ)≤ζ*Fintype.card V)
    (hDS:∀ z,(FS.degree z:ℝ)≤ζ*Fintype.card V)
    (htypes:∀ v u,¬(H false v u∧H true v u))
    (hc:MarkedCommonConfigurationsWithSpokes r P π d β ξ σ H):
    MarkedCommonConfigurationsWithSpokes r P π d β (ξ+4*ζ) τ H' :=by
  obtain ⟨DR,_,hRdeg,hRsub⟩:=marked_rim_typed_intersection_deletion P π d σ τ
  obtain ⟨DS,hSsub,_,hSrow,hScol⟩:=marked_spoke_common_subhost_deletion H H' ∅ ∅ htypes (by simp)
  have hRloss:=marked_removed_typed_rim_from_pair_change P FR π d σ τ hRim
  have hSloss:=marked_missing_spoke_from_pair_change FS H H' hSpoke
  obtain ⟨hrow,hcol⟩:=marked_spoke_host_change_counts FS H H' hSloss
  have hDR':∀ v,(DR.degree v:ℝ)≤ζ*Fintype.card V:=by
    intro v
    rw [hRdeg v]
    have hh:(((Finset.univ.filter (fun y=>v≠y∧markedRemovedPhysicalRim P π d σ τ s(v,y))).card):ℝ)≤FR.degree v:=by
      exact_mod_cast marked_removed_typed_rim_count_of_change_graph P FR π d σ τ hRloss v
    exact hh.trans (hDR v)
  have hDS':∀ z,(DS.degree z:ℝ)≤ζ*Fintype.card V:=by
    intro z
    cases z with
    | inl v=>
      rw [hSrow v]
      have hh:(((Finset.univ.filter (fun u=>∃ b,H b v u∧¬H' b v u)).card):ℝ)≤FS.degree (Sum.inl v):=by exact_mod_cast hrow v
      exact hh.trans (hDS (Sum.inl v))
    | inr u=>
      rw [hScol u]
      have hh:(((Finset.univ.filter (fun v=>∃ b,H b v u∧¬H' b v u)).card):ℝ)≤FS.degree (Sum.inr u):=by exact_mod_cast hcol u
      exact hh.trans (hDS (Sum.inr u))
  have hδ:0≤ζ*Fintype.card V:=mul_nonneg hζ (Nat.cast_nonneg _)
  have hcommon:=marked_common_configurations_after_physical_deletion r P π d β ξ (ζ*Fintype.card V)
    hδ hn σ H DR DS hDR' hDS' hc
  have htarget:=marked_common_configurations_under_host_inclusion r P π d β
    (ξ+4*(ζ*Fintype.card V)/Fintype.card V) (rawMarkedDeleteRims σ DR.edgeFinset)
    τ (markedDeletePhysicalSpokes H DS) H' (fun b x y h=>(hRsub b x y).mp h |>.2)
    (fun b v u h=>(hSsub b v u).mp h |>.2) hcommon
  have hn0:(Fintype.card V:ℝ)≠0:=by exact_mod_cast Nat.ne_of_gt hn
  have he:(ξ+4*(ζ*Fintype.card V)/Fintype.card V)=ξ+4*ζ:=by field_simp
  simpa only [he] using htarget
end Oberwolfach
