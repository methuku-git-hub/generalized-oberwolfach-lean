module

public import Oberwolfach.OrdinaryRootCoverNonrootData
public import Oberwolfach.OrdinaryReservedInnerStarEditBounds
public import Oberwolfach.PhysicalHostDegreeBounds

@[expose] public section
/-! Removing a root cover changes every nonroot row and column by at most
its nonroot physical degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_nonroot_edit_bounds
    (Reference Q F:SimpleGraph V) (Href H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (r:ℕ) (η ell L:ℝ) (A:OrdinaryRootCoverNonrootData Q F H X T Z W r η ell)
    (hR:∀v∉T,((changed (Reference.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hRow:∀v∉T,((changed (Finset.univ.filter (Href v)) (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hCol:∀u∉W,((changed (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L):
    (∀v∉T,((changed (Reference.neighborFinset v) ((Q\A.rim).neighborFinset v)).card:ℝ)≤L+ell) ∧
    (∀v∉T,((changed (Finset.univ.filter (Href v)) (Finset.univ.filter (fun u=>H v u∧¬A.spokes v u))).card:ℝ)≤L+ell) ∧
    (∀u∉W,((changed (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u∧¬A.spokes v u))).card:ℝ)≤L+ell):=by
  let R:=A.rim
  let S:=A.spokes
  have hRQ:R≤Q:=A.rim_sub
  have hSH:∀v u,S v u→H v u:=A.spoke_sub
  have hsize (v:V) (hv:v∉T):(R.degree v:ℝ)+((Finset.univ.filter (S v)).card:ℝ)≤ell:=by
    have hn:Sum.inl v∉ordinaryInnerVertices T W:=by simpa only [ordinaryInnerVertices_left] using hv
    have hh:=A.nonroot_degree (Sum.inl v) hn
    rw [ordinary_physical_degree_row,Nat.cast_add] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hcolsize (u:U) (hu:u∉W):((Finset.univ.filter (fun v=>S v u)).card:ℝ)≤ell:=by
    have hn:Sum.inr u∉ordinaryInnerVertices T W:=by simpa only [ordinaryInnerVertices_right] using hu
    have hh:=A.nonroot_degree (Sum.inr u) hn
    rw [ordinary_physical_degree_column] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hrim (v:V):(changed (Q.neighborFinset v) ((Q\R).neighborFinset v)).card=R.degree v:=by
    have he:(Q\R).neighborFinset v=Q.neighborFinset v\R.neighborFinset v:=by
      ext a;simp only [SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj,Finset.mem_sdiff]
    have hs:R.neighborFinset v⊆Q.neighborFinset v:=by
      intro a ha;exact (Q.mem_neighborFinset v a).mpr (hRQ ((R.mem_neighborFinset v a).mp ha))
    rw [he,←SimpleGraph.card_neighborFinset_eq_degree]
    convert congrArg Finset.card (changed_sdiff_of_subset (Q.neighborFinset v) (R.neighborFinset v) hs) using 1 <;> congr!
  have hrow (v:V):(changed (Finset.univ.filter (H v))
      (Finset.univ.filter (fun u=>H v u∧¬S v u))).card=(Finset.univ.filter (S v)).card:=by
    have he:Finset.univ.filter (fun u=>H v u∧¬S v u)=Finset.univ.filter (H v)\Finset.univ.filter (S v):=by ext u;simp
    have hs:Finset.univ.filter (S v)⊆Finset.univ.filter (H v):=by
      intro u hu;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hSH v u (Finset.mem_filter.mp hu).2⟩
    rw [he]
    convert congrArg Finset.card (changed_sdiff_of_subset (Finset.univ.filter (H v)) (Finset.univ.filter (S v)) hs) using 1 <;> congr!
  have hcol (u:U):(changed (Finset.univ.filter (fun v=>H v u))
      (Finset.univ.filter (fun v=>H v u∧¬S v u))).card=(Finset.univ.filter (fun v=>S v u)).card:=by
    have he:Finset.univ.filter (fun v=>H v u∧¬S v u)=Finset.univ.filter (fun v=>H v u)\Finset.univ.filter (fun v=>S v u):=by ext v;simp
    have hs:Finset.univ.filter (fun v=>S v u)⊆Finset.univ.filter (fun v=>H v u):=by
      intro v hv;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hSH v u (Finset.mem_filter.mp hv).2⟩
    rw [he]
    convert congrArg Finset.card (changed_sdiff_of_subset (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>S v u)) hs) using 1 <;> congr!
  constructor
  · intro v hv
    have ht:=changed_card_triangle (Reference.neighborFinset v) (Q.neighborFinset v) ((Q\R).neighborFinset v)
    rw [hrim v] at ht
    have hh:((changed (Reference.neighborFinset v) ((Q\R).neighborFinset v)).card:ℝ)≤
      ((changed (Reference.neighborFinset v) (Q.neighborFinset v)).card:ℝ)+R.degree v:=by exact_mod_cast ht
    have hs:=hsize v hv
    have hz:(0:ℝ)≤(Finset.univ.filter (S v)).card:=by positivity
    linarith only [hh,hR v hv,hs,hz]
  constructor
  · intro v hv
    have ht:=changed_card_triangle (Finset.univ.filter (Href v)) (Finset.univ.filter (H v))
      (Finset.univ.filter (fun u=>H v u∧¬S v u))
    rw [hrow v] at ht
    have hh:((changed (Finset.univ.filter (Href v)) (Finset.univ.filter (fun u=>H v u∧¬S v u))).card:ℝ)≤
      ((changed (Finset.univ.filter (Href v)) (Finset.univ.filter (H v))).card:ℝ)+(Finset.univ.filter (S v)).card:=by exact_mod_cast ht
    have hs:=hsize v hv
    have hz:(0:ℝ)≤R.degree v:=by positivity
    linarith only [hh,hRow v hv,hs,hz]
  · intro u hu
    have ht:=changed_card_triangle (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u))
      (Finset.univ.filter (fun v=>H v u∧¬S v u))
    rw [hcol u] at ht
    have hh:((changed (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u∧¬S v u))).card:ℝ)≤
      ((changed (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)+(Finset.univ.filter (fun v=>S v u)).card:=by exact_mod_cast ht
    linarith only [hh,hCol u hu,hcolsize u hu]
end Oberwolfach
