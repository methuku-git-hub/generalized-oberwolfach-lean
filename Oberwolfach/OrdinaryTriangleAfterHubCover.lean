module

public import Oberwolfach.OrdinaryTriangleSelectedColumns
public import Oberwolfach.OrdinaryHubDeletionReferenceChanges
public import Oberwolfach.RootedRowCover

@[expose] public section
/-! Use the robust same-sample triangle event after a hub packing. Only the
uncovered hub columns are compared; root stars survive the hub deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_triangle_event_after_hub_cover
    (P F Q:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d D nh nr:ℕ)
    (A:Finset V) (B:Finset U) (u:Fin nh→U) (x:Fin nr→V)
    (hu:Function.Injective u) (hx:Function.Injective x)
    (pR pH η θ ρ L:ℝ) (hL:0≤L) (hcap:2*L+nr+D+2*(3*d:ℕ)≤ρ*Fintype.card V)
    (hn:(nr:ℝ)≤θ*Fintype.card V) (hnh:(2*nh:ℝ)≤L)
    (hnotB:∀i,u i∉B) (hxA:∀i,x i∉A) (hroot:∀i,Q.neighborFinset (x i)⊆A)
    (hrootB:∀i a,H (x i) a→a∈B)
    (hbalance:∀i,|pR*(P.neighborFinset (x i)).card/(2*B.card*pH)-1|≤η)
    (hbal:∀i,Q.degree (x i)=2*(Finset.univ.filter (H (x i))).card)
    (hQ:Q≤P\F) (j:Color) (sample:RawWheelOutcome V U Γ Color)
    (hEvent:OrdinaryTriangleTwoDomainRowEvent P F π d D Finset.univ Finset.univ B pR pH η θ ρ j sample):
    let R:=rawWheelGraph P sample\F
    let H₀:=rawWheelSpokes π d sample j;
    (∀v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) →
    (∀v,((changed (Finset.univ.filter (H₀ v)) (Finset.univ.filter (H v))).card:ℝ)≤L) →
    (∀a∈B,((changed (Finset.univ.filter (fun v=>H₀ v a)) (Finset.univ.filter (fun v=>H v a))).card:ℝ)≤L) →
    ∀(T:Fin nh→Finset V) (M:Finset (OrdinaryWheel Q F H 3)),
    (∀i,T i⊆A) → (∀v,(ordinaryWheelRimGraph M).degree v≤2*nh) →
    M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i))) →
    ∃ C:Fin nr→Finset (OrdinaryWheel (Q\ordinaryWheelRimGraph M) F
      (fun v a=>H v a∧¬ordinaryPackingSpokes M v a) 3),
      (∀i,OrdinaryRowCover (C i) (x i) A 0) ∧
      (∀i k,i≠k→Disjoint ((C i).biUnion ordinaryWheelResources) ((C k).biUnion ordinaryWheelResources)) ∧
      (∀i,∀W∈C i,∀k,x k∈(ordinaryWheelRim W).support↔k=i) ∧
      (∀v∈A,(ordinaryWheelRimGraph (Finset.univ.biUnion C)).degree v≤2*nr) ∧
      (∀v∈A,(Finset.univ.filter (ordinaryPackingSpokes (Finset.univ.biUnion C) v)).card≤nr) ∧
      (∀a,(Finset.univ.filter (fun v=>ordinaryPackingSpokes (Finset.univ.biUnion C) v a)).card≤3*nr) ∧
      (∀i,Disjoint ((C i).biUnion ordinaryWheelResources) (M.biUnion ordinaryWheelResources)):=by
  intro R H₀ hR hrow hcol T M hTA hMdeg hunion
  let Q':=Q\ordinaryWheelRimGraph M
  let H':=fun v a=>H v a∧¬ordinaryPackingSpokes M v a
  have hinterfaces:=ordinary_hub_deletion_fixed_domain M u T Finset.univ B hnotB hunion hMdeg
  have hstars (i:Fin nr):Q'.neighborFinset (x i)=Q.neighborFinset (x i) ∧
      Finset.univ.filter (H' (x i))=Finset.univ.filter (H (x i)):=
    ordinary_hub_deletion_preserves_row_balance M (by omega) u hu T A hTA hunion (x i) (hxA i)
  have hchanges:=ordinary_hub_deletion_reference_changes R H₀ B L hL
    (by intro v;convert hR v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hrow v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro a ha;convert hcol a ha using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    u T M hnh hnotB hMdeg hunion
  have hQ':Q'≤P\F:=sdiff_le.trans hQ
  have hroot':∀i,Q'.neighborFinset (x i)⊆A:=by intro i;rw [(hstars i).1];exact hroot i
  have hrootB':∀i a,H' (x i) a→a∈B:=fun i a h=>hrootB i a h.1
  have hbal':∀i,Q'.degree (x i)=2*(Finset.univ.filter (H' (x i))).card:=by
    intro i
    have hdeg:Q'.degree (x i)=Q.degree (x i):=by
      rw [←SimpleGraph.card_neighborFinset_eq_degree,←SimpleGraph.card_neighborFinset_eq_degree,(hstars i).1]
    rw [hdeg,(hstars i).2]
    exact hbal i
  have hrows:=ordinary_triangle_event_with_selected_columns P F Q' H' π d D Finset.univ Finset.univ A B nr x
    pR pH η θ ρ (2*L) (by positivity) (by simpa only [Finset.card_univ] using hcap)
    (Finset.subset_univ _) (by simpa only [Finset.card_univ] using hn) hx (fun _=>Finset.mem_univ _) hxA
    (by intro i;convert hroot' i using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    hrootB' (by simpa only [Finset.univ_inter] using hbalance)
    (by intro i;convert hbal' i using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hQ' j sample hEvent
    (by intro v;convert hchanges.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hchanges.2.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro a ha;convert hchanges.2.2 a ha using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  obtain ⟨C,hC,hcross⟩:=hrows
  obtain ⟨C',_,hC',hcross',hroots,hbounds⟩:=rooted_ordinary_row_cover_family C x A hx hxA hC hcross
  refine ⟨C',hC',hcross',hroots,?_,?_,?_,?_⟩
  · simpa only [Nat.zero_add,Nat.mul_one,Nat.mul_comm] using hbounds.1
  · simpa only [Nat.zero_add,Nat.mul_one] using hbounds.2.1
  · simpa only [Nat.mul_comm] using hbounds.2.2
  · intro i
    apply Finset.disjoint_left.mpr
    intro e he heM
    obtain ⟨W,hW,heW⟩:=Finset.mem_biUnion.mp he
    exact Finset.disjoint_left.mp (ordinary_wheel_avoids_removed_packing M W) heW heM
end Oberwolfach
