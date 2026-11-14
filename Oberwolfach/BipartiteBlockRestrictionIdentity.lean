module

public import Oberwolfach.BipartiteBlockMatching
public import Oberwolfach.MarkedEmbeddedHubCycles

@[expose] public section

/-! Restricting a relation outside the specified left class changes none
of the degree or cut inequalities on that class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bipartiteBlockBounds_congr_on_parts {V U:Type} [Fintype V] [Fintype U]
    (E F:V→U→Prop) (P:V→Prop) (Q:U→Prop) (d a lam:ℝ)
    (he:∀ v u,P v→Q u→(E v u↔F v u))
    (H:BipartiteBlockBounds E P Q d a lam):BipartiteBlockBounds F P Q d a lam:=by
  constructor
  · intro v hv
    have hf:Finset.univ.filter (fun u=>Q u∧F v u)=Finset.univ.filter (fun u=>Q u∧E v u):=by
      ext u
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      by_cases hu:Q u
      · simp only [hu,true_and,he v u hv hu]
      · simp only [hu,false_and]
    rw [hf];exact H.row v hv
  · intro u hu
    have hf:Finset.univ.filter (fun v=>P v∧F v u)=Finset.univ.filter (fun v=>P v∧E v u):=by
      ext v
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      by_cases hv:P v
      · simp only [hv,true_and,he v u hv hu]
      · simp only [hv,false_and]
    rw [hf];exact H.col u hu
  · intro S T hS hT hs ht
    have hc:bipartiteMatrixCut (fun v u=>if F v u then 1 else 0) S T=
        bipartiteMatrixCut (fun v u=>if E v u then 1 else 0) S T:=by
      unfold bipartiteMatrixCut
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro u hu
      simp only [he v u (hS v hv) (hT u hu)]
    rw [hc];exact H.cut S T hS hT hs ht

theorem spokeRelationImage_subtype {V U:Type} [Fintype V] [DecidableEq V]
    (A:Finset V) (H:V→U→Prop) (v:V) (u:U):
    spokeRelationImage (⟨Subtype.val,Subtype.val_injective⟩:A↪V) (fun x:A=>H x.val) v u↔v∈A∧H v u:=by
  constructor
  · rintro ⟨x,hx,hH⟩
    exact ⟨hx ▸ x.property,hx ▸ hH⟩
  · rintro ⟨hv,hH⟩
    exact ⟨⟨v,hv⟩,rfl,hH⟩

theorem bipartiteBlockBounds_inner_spokes {V U:Type} [Fintype V] [Fintype U] [DecidableEq V]
    (A:Finset V) (H:V→U→Prop) (P:V→Prop) (Q:U→Prop) (d a lam:ℝ)
    (hP:∀ v,P v→v∈A) (h:BipartiteBlockBounds H P Q d a lam):
    BipartiteBlockBounds (spokeRelationImage (⟨Subtype.val,Subtype.val_injective⟩:A↪V)
      (fun x:A=>H x.val)) P Q d a lam:=by
  apply bipartiteBlockBounds_congr_on_parts H _ P Q d a lam _ h
  intro v u hv _
  rw [spokeRelationImage_subtype]
  simp only [hP v hv,true_and]

end Oberwolfach
