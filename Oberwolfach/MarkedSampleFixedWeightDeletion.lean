module

public import Oberwolfach.MarkedFixedWeightPotentialPhysicalDeletion
public import Oberwolfach.MarkedSampleSeedPresentRootBounds
public import Oberwolfach.MarkedSamplePhysicalDeletionLift

@[expose] public section

/-! Bounded physical deletion in an actual sampled host retains its supplied
tuple coefficients and changes its loads by an explicit deterministic loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sample_fixed_weight_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:3≤m) (hn:0<Fintype.card V)
    (hu:Fintype.card U≤Fintype.card V) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (weight:(Fin (m+1)→V)→ℝ) (B η lo hi:ℝ) (hB:0≤B) (hη:0≤η)
    (hw:∀ C,0≤weight C∧weight C≤B/(Fintype.card V:ℝ)^m)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (deltaR deltaS:ℝ) (hR:0≤deltaR) (hS:0≤deltaS)
    (hrim:∀ x,(DR.degree x:ℝ)≤deltaR)
    (hrow:∀ x,(DS.degree (Sum.inl x):ℝ)≤deltaS)
    (hcol:∀ u,(DS.degree (Sum.inr u):ℝ)≤deltaS):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let ψ:=fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true)=>weight W.1.val
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let η':=η+11*((m:ℝ)+1)^4*B*(2*deltaR+deltaS)/Fintype.card V
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let ψ':=fun W:MarkedWheel (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) m π (3*d) (H' false) (H' true)=>weight W.1.val
    (∀ e,|markedWheelRimLoad ψ e-1|≤η)→
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η)→
    (∀ W,lo≤ψ W∧ψ W≤hi)→
    (∀ e,|markedWheelRimLoad ψ' e-1|≤η')∧
    (∀ j v u,|markedSpokeResidual ψ' j v u|≤η')∧
    (∀ W,lo≤ψ' W∧ψ' W≤hi):=by
  intro E K ψ σ' H' η' E' K' ψ' hloadR hloadS hcoeff
  let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
    (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val
  have hc:=marked_fixed_weight_potential_physical_deletion P π d m hm hn hu weight B hB hw
    deltaR deltaS hR hS σ H
  have hη':0≤η':=by dsimp [η'];positivity
  have hactual:=marked_sample_seed_present_root_bounds P π d m 1 1 1 1 η' hη' weight σ' H'
  simp only [one_pow,mul_one,div_one] at hactual
  have htriangle (root:((V×V)⊕(V×V))⊕(Bool×V×U))
      (hbase:|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤η):
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ') H' root-1|≤η':=by
    have he:=hc root DR DS hrim hrow hcol
    exact (abs_sub_le (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ') H' root)
      (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root) 1).trans
        ((add_le_add he hbase).trans_eq (by dsimp [η'];ring))
  obtain ⟨hR',hS'⟩:=hactual (by
    intro a
    let a₀:E⊕K:=Sum.map
      (fun e=>(markedSampleDeletedArcEquiv P π d σ DR.edgeFinset false e).val)
      (fun e=>(markedSampleDeletedArcEquiv P π d σ DR.edgeFinset true e).val) a
    have he:Sum.map Subtype.val Subtype.val a₀=Sum.map Subtype.val Subtype.val a:=by cases a <;> rfl
    apply htriangle
    have hid:=marked_sample_seed_rim_load P π d m 1 1 1 1 weight σ H a₀
    simp only [one_pow,mul_one,div_one] at hid
    rw [he] at hid
    rw [hid]
    exact hloadR a₀) (by
    intro j v u hpresent
    have hp:H j v u:=hpresent.1
    apply htriangle
    have hid:=marked_sample_seed_spoke_load P π d m 1 1 1 1 weight σ H j v u hp
    simp only [one_pow,mul_one,div_one] at hid
    rw [hid]
    have hh:=hloadS j v u
    have hp':if j then H true v u else H false v u:=by cases j <;> exact hp
    simpa only [markedSpokeResidual,if_pos hp',abs_sub_comm] using hh)
  refine ⟨hR',hS',?_⟩
  intro W
  exact hcoeff (markedPhysicalDeletedSampleWheelLift P π d m σ DR DS H W)

end Oberwolfach
