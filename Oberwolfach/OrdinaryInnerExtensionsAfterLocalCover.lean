module

public import Oberwolfach.OrdinaryBoundaryGraph
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section
/-! Only the inner restriction of a root-cover packing affects extension
counts inside the enclosing pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_inner_extensions_after_local_cover
    (Q R:SimpleGraph V) (H S:V→U→Prop) (X:Finset V) (Z:Finset U) (η:ℝ)
    (hdegree:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤η)
    (u:U) (hu:u∈Z) (a c:V) (ha:a∈X) (hc:c∈X):
    (((X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)-3*η≤
      (((X.filter (fun v=>H v u∧¬S v u))∩(Q\R).neighborFinset a∩(Q\R).neighborFinset c).card:ℝ):=by
  let G:=spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)
  let Da:=X.filter (fun v=>R.Adj a v)
  let Dc:=X.filter (fun v=>R.Adj c v)
  let Du:=X.filter (fun v=>S v u)
  have hcard (w:V⊕U) (Y:Finset V) (hY:∀v∈Y,G.Adj w (Sum.inl v)):
      (Y.card:ℝ)≤η:=by
    have hsub:Y.image (Sum.inl:V→V⊕U)⊆G.neighborFinset w:=by
      intro z hz
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (hY v hv)
    have hc:=Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Sum.inl_injective,SimpleGraph.card_neighborFinset_eq_degree] at hc
    have hcR:(Y.card:ℝ)≤(G.degree w:ℝ):=by exact_mod_cast hc
    exact hcR.trans (hdegree w)
  have hDa:(Da.card:ℝ)≤η:=by
    apply hcard (Sum.inl a)
    intro v hv
    have hv':v∈X∧R.Adj a v:=Finset.mem_filter.mp hv
    exact (spanningRestriction_adj _ _ _ _).mpr ⟨hv'.2,(ordinaryInnerVertices_left X Z a).mpr ha,
      (ordinaryInnerVertices_left X Z v).mpr hv'.1⟩
  have hDc:(Dc.card:ℝ)≤η:=by
    apply hcard (Sum.inl c)
    intro v hv
    have hv':v∈X∧R.Adj c v:=Finset.mem_filter.mp hv
    exact (spanningRestriction_adj _ _ _ _).mpr ⟨hv'.2,(ordinaryInnerVertices_left X Z c).mpr hc,
      (ordinaryInnerVertices_left X Z v).mpr hv'.1⟩
  have hDu:(Du.card:ℝ)≤η:=by
    apply hcard (Sum.inr u)
    intro v hv
    have hv':v∈X∧S v u:=Finset.mem_filter.mp hv
    exact (spanningRestriction_adj _ _ _ _).mpr ⟨hv'.2,(ordinaryInnerVertices_right X Z u).mpr hu,
      (ordinaryInnerVertices_left X Z v).mpr hv'.1⟩
  let A:Finset V:=(X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c
  let B:Finset V:=(X.filter (fun v=>H v u∧¬S v u))∩(Q\R).neighborFinset a∩(Q\R).neighborFinset c
  have hsub:A\B⊆Da∪Dc∪Du:=by
    intro v hv
    simp only [A,B,Da,Dc,Du,Finset.mem_sdiff,Finset.mem_inter,Finset.mem_filter,
      Finset.mem_union,SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj] at hv ⊢
    tauto
  have hdiff:(A\B).card≤Da.card+Dc.card+Du.card:=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hpart:=Finset.card_sdiff_add_card_inter A B
  have hinter:(A∩B).card≤B.card:=Finset.card_le_card Finset.inter_subset_right
  have hn:A.card≤B.card+Da.card+Dc.card+Du.card:=by omega
  have hnR:(A.card:ℝ)≤(B.card:ℝ)+Da.card+Dc.card+Du.card:=by exact_mod_cast hn
  linarith only [hnR,hDa,hDc,hDu]
end Oberwolfach
