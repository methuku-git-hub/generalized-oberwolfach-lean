module

public import Oberwolfach.MarkedLocalSpokeLoadsAfterChanges
public import Oberwolfach.MarkedLocalEstimateMonotonicity

@[expose] public section
/-! The fixed-weight local spoke-load estimate on the same physical change
budgets as the marked reference configurations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_local_spoke_loads_from_shared_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:3≤m) (hn:0<Fintype.card V)
    (D τ A B:ℝ) (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (p k s₀ pstar:ℝ) (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀)
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀≤1) (hB:0≤B)
    (weight:(Fin (m+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (eps ζ target:ℝ) (hζ:0≤ζ)
    (σ σ':RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hload:MarkedLocalSpokeLoadsWithSpokes P π d m D p k s₀ weight eps σ H)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hRim:∀ e,¬(rawMarkedPairRims P π d σ e↔rawMarkedPairRims P π d σ' e)→
      markedPairPhysical π e∈FR.edgeFinset)
    (hSpoke:∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hdegR:∀ v,(FR.degree v:ℝ)≤ζ*Fintype.card V)
    (hdegS:∀ z,(FS.degree z:ℝ)≤ζ*Fintype.card V)
    (hbudget:eps+15*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*ζ≤target):
    MarkedLocalSpokeLoadsWithSpokes P π d m D p k s₀ weight target σ' H' :=by
  have hδ:0≤ζ*(Fintype.card V:ℝ):=mul_nonneg hζ (Nat.cast_nonneg _)
  have hh:=marked_local_spoke_loads_after_physical_changes P π d m hm hn D τ A B hDlo hDhi
    p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB weight hw eps
    (ζ*Fintype.card V) (ζ*Fintype.card V) hδ hδ σ σ' H H' hload FR FS
    hRim hSpoke hdegR (fun v=>hdegS (Sum.inl v)) (fun u=>hdegS (Sum.inr u))
  have hn0:(Fintype.card V:ℝ)≠0:=by exact_mod_cast (ne_of_gt hn)
  have he:eps+5*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*
      (2*(ζ*Fintype.card V)+ζ*Fintype.card V)/Fintype.card V=
      eps+15*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*ζ:=by field_simp;ring
  rw [he] at hh
  exact markedLocalSpokeLoads_mono P π d m D p k s₀ weight _ _ hbudget σ' H' hh
end Oberwolfach
