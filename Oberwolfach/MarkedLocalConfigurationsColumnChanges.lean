module

public import Oberwolfach.MarkedLocalConfigurationsHostInclusion
public import Oberwolfach.MarkedCommonConfigurationsAfterHostChange

@[expose] public section
/-! Local marked cycle and root-omitted path counts after physical changes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_local_configurations_after_host_change_column_only
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (βC βP ζ:ℝ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hRim:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈FR.edgeFinset)
    (hSpoke:∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hDR:∀ v,(FR.degree v:ℝ)≤ζ*Fintype.card V)
    (hDS:∀ u,(FS.degree (Sum.inr u):ℝ)≤ζ*Fintype.card V)
    (htypes:∀ v u,¬(H false v u∧H true v u))
    (hc:MarkedLocalConfigurationsWithSpokes r P π d Finset.univ βC βP σ H):
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ
      (βC-(r+5:ℕ)*(ζ+ζ)) (βP-(r+7:ℕ)*ζ-(r+4:ℕ)*ζ) τ H' :=by
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
  have hDScol:∀u,(DS.degree (Sum.inr u):ℝ)≤ζ*Fintype.card V:=by
    intro u
    rw [hScol u]
    have hh:(((Finset.univ.filter (fun v=>∃b,H b v u∧¬H' b v u)).card):ℝ)≤FS.degree (Sum.inr u):=by exact_mod_cast hcol u
    exact hh.trans (hDS u)
  have hcommon:=marked_local_configurations_after_physical_deletion r P π d βC βP ζ ζ σ H hc DR DS
    hDR' hDScol
  have hrim:=marked_local_configurations_rim_inclusion r P π d
    (βC-(r+5:ℕ)*(ζ+ζ)) (βP-(r+7:ℕ)*ζ-(r+4:ℕ)*ζ)
    (rawMarkedDeleteRims σ DR.edgeFinset) τ (markedDeletePhysicalSpokes H DS)
    (fun b x y h=>(hRsub b x y).mp h |>.2) hcommon
  exact marked_local_configurations_spoke_inclusion r P π d
    (βC-(r+5:ℕ)*(ζ+ζ)) (βP-(r+7:ℕ)*ζ-(r+4:ℕ)*ζ)
    τ (markedDeletePhysicalSpokes H DS) H' (fun b v u h=>(hSsub b v u).mp h |>.2) hrim
end Oberwolfach
