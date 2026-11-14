module

public import Oberwolfach.MarkedLocalSpokeLoadSharedChanges

@[expose] public section
/-! The reference-level deep spoke-load field, with the exact fixed weight,
normalization, roots and displayed numerical margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_deep_loads_after_changes
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (hn:0<Fintype.card V)
    (rho t τ A B pstar eps ζ thetaDeep:ℝ) (hζ:0≤ζ) (hB:0≤B) (hpstar:0<pstar)
    (weight:(Fin (r+4+1)→V)→ℝ)
    (σ σ':RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hRim:∀ e,¬(rawMarkedPairRims P π d σ e↔rawMarkedPairRims P π d σ' e)→
      markedPairPhysical π e∈FR.edgeFinset)
    (hSpoke:∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hdegR:∀ v,(FR.degree v:ℝ)≤ζ*Fintype.card V)
    (hdegS:∀ z,(FS.degree z:ℝ)≤ζ*Fintype.card V):
    let DRef:=2*Fintype.card U/rho
    let pRef:=rho*(r+4:ℝ)*t/2
    let kRef:=pRef/(r+4:ℝ)
    let sRef:=(r+4:ℝ)*t
    (Fintype.card V:ℝ)/2≤DRef → DRef≤2*Fintype.card V →
    pstar≤pRef → pstar≤kRef → pstar≤sRef → pRef≤1 → kRef≤1 → sRef≤1 →
    SuccessorSequenceWeightConditions P π (3*d) DRef τ A B weight →
    MarkedLocalSpokeLoadsWithSpokes P π d (r+4) DRef pRef kRef sRef weight eps σ H →
    eps+15*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))*ζ≤thetaDeep/4 →
    MarkedLocalSpokeLoadsWithSpokes P π d (r+4) DRef pRef kRef sRef weight (thetaDeep/4) σ' H' :=by
  intro DRef pRef kRef sRef hDlo hDhi hp hk hs hp1 hk1 hs1 hw hload hbudget
  exact marked_local_spoke_loads_from_shared_changes P π d (r+4) (by omega) hn
    DRef τ A B hDlo hDhi pRef kRef sRef pstar hpstar hp hk hs hp1 hk1 hs1 hB
    weight hw eps ζ (thetaDeep/4) hζ σ σ' H H' hload FR FS hRim hSpoke hdegR hdegS (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hbudget)
end Oberwolfach
