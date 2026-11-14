module

public import Oberwolfach.OrdinaryRootCoverInnerIncident

@[expose] public section
/-! Common extensions survive the root cover even when some endpoints
lie outside the enclosing pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_all_extensions (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (u:U) (a c:V):
    (((X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)-3*max η ell≤
      (((X.filter (fun v=>H v u∧¬D.spokes v u))∩(Q\D.rim).neighborFinset a∩(Q\D.rim).neighborFinset c).card:ℝ):=by
  let Da:=X.filter (fun v=>D.rim.Adj a v)
  let Dc:=X.filter (fun v=>D.rim.Adj c v)
  let Du:=X.filter (fun v=>D.spokes v u)
  have hDa:(Da.card:ℝ)≤max η ell:=by
    have hh:=ordinary_root_cover_inner_incident Q F H X T Z W r η ell D (Sum.inl a)
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hDc:(Dc.card:ℝ)≤max η ell:=by
    have hh:=ordinary_root_cover_inner_incident Q F H X T Z W r η ell D (Sum.inl c)
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hDu:(Du.card:ℝ)≤max η ell:=by
    have hh:=ordinary_root_cover_inner_incident Q F H X T Z W r η ell D (Sum.inr u)
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  let A:Finset V:=(X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c
  let B:Finset V:=(X.filter (fun v=>H v u∧¬D.spokes v u))∩(Q\D.rim).neighborFinset a∩(Q\D.rim).neighborFinset c
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
