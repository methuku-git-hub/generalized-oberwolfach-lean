module

public import Oberwolfach.OrdinaryHubDeletionGlobalChanges

@[expose] public section
/-! Earlier hub wheels consume a bounded amount of the existing deviation
budget from the same reference, while active hub columns remain untouched. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r nh:ℕ}

theorem ordinary_hub_deletion_reference_changes
    (R:SimpleGraph V) (H₀:V→U→Prop) (B:Finset U) (L:ℝ) (hL:0≤L)
    (hR:∀v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hrow:∀v,((changed (Finset.univ.filter (H₀ v)) (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hcol:∀a∈B,((changed (Finset.univ.filter (fun v=>H₀ v a)) (Finset.univ.filter (fun v=>H v a))).card:ℝ)≤L)
    (u:Fin nh→U) (T:Fin nh→Finset V) (M:Finset (OrdinaryWheel Q F H r))
    (hnh:(2*nh:ℝ)≤L) (hnotB:∀i,u i∉B) (hMdeg:∀v,(ordinaryWheelRimGraph M).degree v≤2*nh)
    (hunion:M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i)))):
    let Q':=Q\ordinaryWheelRimGraph M
    let H':=fun v a=>H v a∧¬ordinaryPackingSpokes M v a;
    (∀v,((changed (R.neighborFinset v) (Q'.neighborFinset v)).card:ℝ)≤2*L) ∧
    (∀v,((changed (Finset.univ.filter (H₀ v)) (Finset.univ.filter (H' v))).card:ℝ)≤2*L) ∧
    (∀a∈B,((changed (Finset.univ.filter (fun v=>H₀ v a)) (Finset.univ.filter (fun v=>H' v a))).card:ℝ)≤2*L):=by
  intro Q' H'
  have hrim:=ordinary_hub_deletion_global_rim_change M u T hMdeg hunion
  have hspoke:=ordinary_hub_deletion_global_spoke_row_change M u T hunion
  have hc:∀a∈B,Finset.univ.filter (fun v=>H' v a)=Finset.univ.filter (fun v=>H v a):=by
    intro a ha
    have hh:=(ordinary_hub_deletion_fixed_domain M u T Finset.univ B hnotB hunion hMdeg).2.2 a ha
    simpa only [Finset.univ_inter] using hh
  constructor
  · intro v
    have ht:=changed_card_triangle (R.neighborFinset v) (Q.neighborFinset v) (Q'.neighborFinset v)
    have ht':((changed (R.neighborFinset v) (Q'.neighborFinset v)).card:ℝ)≤
        ((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)+
        ((changed (Q.neighborFinset v) (Q'.neighborFinset v)).card:ℝ):=by exact_mod_cast ht
    have hd:((changed (Q.neighborFinset v) (Q'.neighborFinset v)).card:ℝ)≤2*nh:=by exact_mod_cast hrim v
    linarith [hR v]
  constructor
  · intro v
    have ht:=changed_card_triangle (Finset.univ.filter (H₀ v)) (Finset.univ.filter (H v)) (Finset.univ.filter (H' v))
    have ht':((changed (Finset.univ.filter (H₀ v)) (Finset.univ.filter (H' v))).card:ℝ)≤
        ((changed (Finset.univ.filter (H₀ v)) (Finset.univ.filter (H v))).card:ℝ)+
        ((changed (Finset.univ.filter (H v)) (Finset.univ.filter (H' v))).card:ℝ):=by exact_mod_cast ht
    have hd:((changed (Finset.univ.filter (H v)) (Finset.univ.filter (H' v))).card:ℝ)≤nh:=by exact_mod_cast hspoke v
    linarith [hrow v]
  · intro a ha
    rw [hc a ha]
    linarith [hcol a ha]
end Oberwolfach
