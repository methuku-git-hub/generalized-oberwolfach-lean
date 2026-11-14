module

public import Oberwolfach.MarkedReferenceParentPotentialAfterChanges
public import Oberwolfach.MarkedReferenceParentLoadFromZeroDeletionSplit

@[expose] public section
/-! The parent load after changes, derived from the zero-deletion case of
the original adaptive packing event on the same fixed sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_parent_from_adaptive_event
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (hn:0<Fintype.card V)
    (hu:Fintype.card U≤Fintype.card V)
    (rho t τ A B pstar eps η C ζ kappa:ℝ) (hζ:0≤ζ) (hB:0≤B) (hpstar:0<pstar) (hη:η≤eps)
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
    (∀ δ:ℝ,0≤δ→∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      (∀ x,(DR.degree x:ℝ)≤δ)→(∀ x,(DS.degree x:ℝ)≤δ)→
      MarkedPackingLoadsWithSpokes P π d (r+4) DRef pRef kRef sRef weight a c
        (Equiv.refl U) q s (η+C*δ/Fintype.card V)
        (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS)) →
    eps+33*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))*ζ≤kappa/4 →
    ∀ root,rawMarkedWheelMarginal P π d pRef kRef q s a c root≠0 →
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ') H' root-1|≤kappa/4 :=by
  intro DRef pRef kRef sRef seed hDlo hDhi hp hk hs hp1 hk1 hs1 hw hpack hbudget
  have hbase:∀ root,rawMarkedWheelMarginal P π d pRef kRef q s a c root≠0 →
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤eps:=by
    have hh:=marked_reference_parent_load_from_zero_deletion_split P π d r rho t (4*eps) η C
      weight a c q s σ H (by linarith only [hη]) hpack
    simpa only [mul_div_cancel_left₀,show (4*eps)/4=eps by ring] using hh
  exact marked_reference_parent_potential_after_changes r P π d hn hu rho t τ A B pstar eps ζ kappa
    hζ hB hpstar weight q s a c σ σ' H H' FR FS hRim hSpoke hdegR hdegS
    hDlo hDhi hp hk hs hp1 hk1 hs1 hw hbase hbudget
end Oberwolfach
