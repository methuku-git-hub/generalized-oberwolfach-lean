module

public import Oberwolfach.OrdinaryReserveCutStability
public import Oberwolfach.OrdinaryUnreservedOrientation
public import Oberwolfach.GreedyGraphCandidates
public import Oberwolfach.SupportedBernoulliFactor

@[expose] public section
/-! The removed inner rectangle and reserve form one rim/spoke deletion
whose row and column degrees are bounded on the original vertex scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryUnreservedRimDeletion (Q:SimpleGraph V) (X:Finset V) (R:SimpleGraph (V⊕U)):SimpleGraph V:=
  spanningRestriction Q X⊔R.comap Sum.inl

def ordinaryUnreservedSpokeDeletion (X:Finset V) (Z:Finset U) (R:SimpleGraph (V⊕U)):V→U→Prop:=
  fun v u=>(v∈X∧u∈Z)∨R.Adj (Sum.inl v) (Sum.inr u)

theorem ordinary_unreserved_as_deletion (Q:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (R:SimpleGraph (V⊕U)):
    ordinaryUnreservedRim Q X R=Q\ordinaryUnreservedRimDeletion Q X R ∧
    ordinaryUnreservedSpokes H X Z R=(fun v u=>H v u∧¬ordinaryUnreservedSpokeDeletion X Z R v u):=by
  constructor
  · ext v w
    simp [ordinaryUnreservedRim,ordinaryUnreservedRimDeletion,SimpleGraph.sdiff_adj,SimpleGraph.sup_adj] <;> tauto
  · funext v u
    apply propext
    simp only [ordinaryUnreservedSpokes,ordinaryUnreservedSpokeDeletion,not_or]

theorem ordinary_unreserved_deletion_degree_bounds (Q:SimpleGraph V) (X:Finset V) (Z:Finset U)
    (R:SimpleGraph (V⊕U)) (ξ ζ:ℝ)
    (hX:(X.card:ℝ)≤ξ*Fintype.card V) (hZ:(Z.card:ℝ)≤ξ*Fintype.card V)
    (hR:∀w,(R.degree w:ℝ)≤ζ*Fintype.card V):
    (∀v,((ordinaryUnreservedRimDeletion Q X R).degree v:ℝ)≤(ξ+ζ)*Fintype.card V) ∧
    (∀v,((Finset.univ.filter (ordinaryUnreservedSpokeDeletion X Z R v)).card:ℝ)≤(ξ+ζ)*Fintype.card V) ∧
    (∀u,((Finset.univ.filter (fun v=>ordinaryUnreservedSpokeDeletion X Z R v u)).card:ℝ)≤(ξ+ζ)*Fintype.card V):=by
  have hinner (v:V):((spanningRestriction Q X).degree v:ℝ)≤X.card:=by
    rw [←SimpleGraph.card_neighborFinset_eq_degree]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro w hw
    exact ((spanningRestriction_adj Q X v w).mp ((SimpleGraph.mem_neighborFinset _ _ _).mp hw)).2.2
  have hcomap (v:V):((R.comap Sum.inl).degree v:ℝ)≤ζ*Fintype.card V:=by
    have hh:=graph_comap_degree_le R (Function.Embedding.inl:V↪V⊕U) v
    exact (Nat.cast_le.mpr hh).trans (hR (Sum.inl v))
  refine ⟨?_,?_,?_⟩
  · intro v
    have hh:((ordinaryUnreservedRimDeletion Q X R).degree v:ℝ)≤
        ((spanningRestriction Q X).degree v:ℝ)+(R.comap Sum.inl).degree v:=by
      have h0:=graph_degree_sup_le (spanningRestriction Q X) (R.comap Sum.inl) v
      have hcast:=(Nat.cast_le (α:=ℝ)).mpr h0
      push_cast at hcast
      convert hcast using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    have hx:=hinner v
    have hr:=hcomap v
    nlinarith only [hh,hx,hr,hX]
  · intro v
    let T:=Finset.univ.filter (fun u=>R.Adj (Sum.inl v) (Sum.inr u))
    have hs:(Finset.univ.filter (ordinaryUnreservedSpokeDeletion X Z R v))⊆Z∪T:=by
      intro u hu
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,ordinaryUnreservedSpokeDeletion] at hu
      rcases hu with ⟨_,hu⟩|hu
      · exact Finset.mem_union_left _ hu
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩)
    have hc:((Finset.univ.filter (ordinaryUnreservedSpokeDeletion X Z R v)).card:ℝ)≤(Z.card:ℝ)+T.card:=by
      exact_mod_cast (Finset.card_le_card hs).trans (Finset.card_union_le Z T)
    have ht:(T.card:ℝ)≤ζ*Fintype.card V:=(Nat.cast_le.mpr (ordinary_physical_spoke_row_le_degree R v)).trans (hR (Sum.inl v))
    nlinarith only [hc,hX,hZ,ht]
  · intro u
    let T:=Finset.univ.filter (fun v=>R.Adj (Sum.inl v) (Sum.inr u))
    have hs:(Finset.univ.filter (fun v=>ordinaryUnreservedSpokeDeletion X Z R v u))⊆X∪T:=by
      intro v hv
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,ordinaryUnreservedSpokeDeletion] at hv
      rcases hv with ⟨hv,_⟩|hv
      · exact Finset.mem_union_left _ hv
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩)
    have hc:((Finset.univ.filter (fun v=>ordinaryUnreservedSpokeDeletion X Z R v u)).card:ℝ)≤(X.card:ℝ)+T.card:=by
      exact_mod_cast (Finset.card_le_card hs).trans (Finset.card_union_le X T)
    have ht:(T.card:ℝ)≤ζ*Fintype.card V:=(Nat.cast_le.mpr (ordinary_physical_spoke_column_le_degree R u)).trans (hR (Sum.inr u))
    nlinarith only [hc,hX,ht]
end Oberwolfach
