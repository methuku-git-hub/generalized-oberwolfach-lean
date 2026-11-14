module

public import Oberwolfach.MarkedSampleSeedWitness
public import Oberwolfach.MarkedPackingPotentialPhysicalDeletion

@[expose] public section

/-! Actual wheel weights after later physical deletions, with the original
coefficients, normalization, marginal domain and error target unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_deleted_sample_seed_witness
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:3≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (D τ A B p k s₀ pstar η:ℝ)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀)
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀≤1) (hA:0≤A) (hB:0≤B) (hη:0≤η)
    (weight:(Fin (m+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (hq:∀ u,0<q u g) (hS:∀ u,0<s u j)
    (hload:
      let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
      ∀ root,rawMarkedWheelMarginal P π d p k q s g j root≠0→
        |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤η)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (deltaR deltaS:ℝ) (hR:0≤deltaR) (hSp:0≤deltaS)
    (hrim:∀ x,(DR.degree x:ℝ)≤deltaR)
    (hrow:∀ x,(DS.degree (Sum.inl x):ℝ)≤deltaS)
    (hcol:∀ u,(DS.degree (Sum.inr u):ℝ)≤deltaS):
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let η':=η+11*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*(2*deltaR+deltaS)/Fintype.card V
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let ψ:=fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H' false) (H' true)=>weight W.1.val/(D*p^m*k*s₀^m)
    (∀ e,|markedWheelRimLoad ψ e-1|≤η')∧
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η')∧
    (∀ W,(A/2)/(Fintype.card V:ℝ)^m≤ψ W∧ψ W≤(2*B/pstar^(2*m+1))/(Fintype.card V:ℝ)^m):=by
  intro σ' H' η' E K ψ
  have heta:0≤η':=by dsimp [η'];positivity
  apply marked_sample_seed_witness P π d m (by omega) hn D τ A B p k s₀ pstar η'
    hDlo hDhi hpstar hp hk hs hp1 hk1 hs1 hA hB heta weight hw σ' H' q s g j hq hS
  intro seed root hroot
  have hc:=marked_packing_potential_after_physical_deletion P π d m hm hn hu
    D τ A B hDlo hDhi p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB weight hw
    deltaR deltaS hR hSp σ H root DR DS hrim hrow hcol
  have ho:=hload root hroot
  have ht:=abs_sub_le (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ') H' root)
    (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root) 1
  exact ht.trans ((add_le_add hc ho).trans_eq (by dsimp [η'];ring))

end Oberwolfach
