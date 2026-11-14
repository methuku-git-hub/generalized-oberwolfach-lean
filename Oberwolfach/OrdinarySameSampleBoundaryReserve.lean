module

public import Oberwolfach.OrdinaryBoundaryReserveReady
public import Oberwolfach.OrdinarySameSampleBalanceProfiles

@[expose] public section
/-! Connect the same-sample edited-host profiles to the actual boundary
reserve without assuming the profile conclusions separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def OrdinaryBoundaryReserveReadyProperty (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U)
    (τ ε b c:ℝ) (σ:Sym2 (V⊕U)→Bool):Prop :=
    let R:=retainedGraph (ordinaryBoundaryGraph Q H I J) σ;
    (R.comap Sum.inl)≤Q\spanningRestriction Q I ∧
    (∀v u,R.Adj (Sum.inl v) (Sum.inr u)→H v u∧¬(v∈I∧u∈J)) ∧
    (∀v,((R.comap Sum.inl).degree v:ℝ)≤(τ+ε)*Fintype.card (V⊕U)) ∧
    (∀v,((Finset.univ.filter (fun u=>R.Adj (Sum.inl v) (Sum.inr u))).card:ℝ)≤(τ+ε)*Fintype.card (V⊕U)) ∧
    (∀u,((Finset.univ.filter (fun v=>R.Adj (Sum.inl v) (Sum.inr u))).card:ℝ)≤(τ+ε)*Fintype.card (V⊕U)) ∧
    (∀v,|((((Q\spanningRestriction Q I)\(R.comap Sum.inl)).degree v):ℝ)-
      2*(Finset.univ.filter (fun u=>(H v u∧¬(v∈I∧u∈J))∧¬R.Adj (Sum.inl v) (Sum.inr u))).card|
        ≤b+τ*max b c+3*ε*Fintype.card (V⊕U))

theorem ordinary_same_sample_profiles_boundary_reserve
    (P F Q:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (J:Finset U)
    (pR pH tR tH e L:ℝ) (htR:0≤tR) (htH:0≤tH) (he:0≤e) (hL:0≤L)
    (s:U→Color→ℝ) (j:Color) (sample:RawWheelOutcome V U Γ Color)
    (hrows:RawOrdinaryRows P π d 2 I pR s j tR sample)
    (hcols:RawOrdinaryDomainIndices F π d 3 J pH j tH sample)
    (hparent:∀v,|pR*(P.neighborFinset v∩I).card-2*pH*J.card|≤e)
    (hrim:∀v,((changed (Q.neighborFinset v) ((rawWheelGraph P sample).neighborFinset v)).card:ℝ)≤L)
    (hspoke:∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (rawWheelSpokes π d sample j v))).card:ℝ)≤L)
    (hQbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (τ ε:ℝ) (hτ:0≤τ) (σ:Sym2 (V⊕U)→Bool)
    (hgood:OrdinaryBoundaryReserveGood Q H I J τ ε σ):
    OrdinaryBoundaryReserveReadyProperty Q H I J τ ε (e+tR+2*tH+3*L) (e+tR+2*tH+3*L) σ:=by
  have hp:=ordinary_same_sample_balance_profiles P F Q H π d I J pR pH tR tH e L htR htH he hL
    s j sample hrows hcols hparent hrim hspoke
  exact ordinary_boundary_reserve_ready Q H I J τ ε _ _ hτ σ hgood hQbal hp.2 (fun v _=>hp.1 v)
end Oberwolfach
