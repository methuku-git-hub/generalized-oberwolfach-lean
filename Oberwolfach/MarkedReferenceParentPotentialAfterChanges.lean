module

public import Oberwolfach.MarkedReferenceWeightedLoadScaledChanges
public import Oberwolfach.MarkedPotentialPhysicalDeletion

@[expose] public section
/-! The original parent weight and marginal root condition after the same
physical changes as the reference configurations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_parent_potential_after_changes
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (hn:0<Fintype.card V)
    (hu:Fintype.card U≤Fintype.card V)
    (rho t τ A B pstar eps ζ kappa:ℝ) (hζ:0≤ζ) (hB:0≤B) (hpstar:0<pstar)
    (weight:(Fin (r+4+1)→V)→ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (c:Color)
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
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd (r+4) π (3*d)
      (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(DRef*pRef^(r+4)*kRef*sRef^(r+4))
    (Fintype.card V:ℝ)/2≤DRef → DRef≤2*Fintype.card V →
    pstar≤pRef → pstar≤kRef → pstar≤sRef → pRef≤1 → kRef≤1 → sRef≤1 →
    SuccessorSequenceWeightConditions P π (3*d) DRef τ A B weight →
    (∀ root,rawMarkedWheelMarginal P π d pRef kRef q s a c root≠0 →
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤eps) →
    eps+33*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))*ζ≤kappa/4 →
    ∀ root,rawMarkedWheelMarginal P π d pRef kRef q s a c root≠0 →
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ') H' root-1|≤kappa/4 :=by
  intro DRef pRef kRef sRef seed hDlo hDhi hp hk hs hp1 hk1 hs1 hw hbase hbudget
  have hseed:∀ W,0≤seed W ∧ seed W≤(2*B/pstar^(2*(r+4)+1))/(Fintype.card V:ℝ)^(r+4):=by
    intro W
    exact successor_seed_nonneg_upper hw (by omega) hn hDlo hDhi pRef kRef sRef pstar
      hpstar hp hk hs hp1 hk1 hs1 hB W.1.val
  have hB':0≤2*B/pstar^(2*(r+4)+1):=by positivity
  exact marked_reference_weighted_load_scaled_changes P π d (r+4) (by omega) hn hu σ σ' H H' seed
    (2*B/pstar^(2*(r+4)+1)) ζ hB' hζ hseed FR FS hdegR hdegS hRim hSpoke
    (fun root=>rawMarkedWheelMarginal P π d pRef kRef q s a c root≠0) eps (kappa/4) hbase
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hbudget)
end Oberwolfach
