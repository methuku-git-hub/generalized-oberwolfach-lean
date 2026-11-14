module

public import Oberwolfach.OrdinaryCorrectedInnerStarBalance
public import Oberwolfach.WheelFamilyDeletionChanges
public import Oberwolfach.GraphSelectionDegrees
public import Oberwolfach.HubToRowDeletion

@[expose] public section
/-! Reserving the corrected inner star costs at most the inner row or hub
    size in each original rim, spoke-row and spoke-column edit budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_reserved_inner_star_edit_bounds
    (Reference Q C:SimpleGraph V) (Href H K:V→U→Prop) (I T:Finset V) (B W:Finset U) (L:ℝ)
    (hC:C≤spanningRestriction Q I) (hK:∀v u,K v u→H v u∧v∈I∧u∈B)
    (hR:∀v,((changed (Reference.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hRow:∀v,((changed (Finset.univ.filter (Href v)) (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hCol:∀u,((changed (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L):
    let R:=ordinaryRimRootStar C T;
    let S:=ordinarySpokeRootStar K T W;
    (∀v,((changed (Reference.neighborFinset v) ((Q\R).neighborFinset v)).card:ℝ)≤L+I.card) ∧
    (∀v,((changed (Finset.univ.filter (Href v)) (Finset.univ.filter (fun u=>H v u∧¬S v u))).card:ℝ)≤L+B.card) ∧
    (∀u,((changed (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u∧¬S v u))).card:ℝ)≤L+I.card):=by
  intro R S
  have hRI:R≤spanningRestriction Q I:=by intro v w h;exact hC h.1
  have hRQ:R≤Q:=hRI.trans (by intro v w h;exact (spanningRestriction_adj Q I v w).mp h |>.1)
  have hSH:∀v u,S v u→H v u:=by intro v u h;exact (hK v u h.1).1
  have hRsize (v:V):R.degree v≤I.card:=by
    rw [←SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro w hw
    have ha: R.Adj v w:=(R.mem_neighborFinset v w).mp hw
    exact (spanningRestriction_adj Q I v w).mp (hRI ha) |>.2.2
  have hSrow (v:V):(Finset.univ.filter (S v)).card≤B.card:=by
    apply Finset.card_le_card
    intro u hu
    exact (hK v u (Finset.mem_filter.mp hu).2.1).2.2
  have hScol (u:U):(Finset.univ.filter (fun v=>S v u)).card≤I.card:=by
    apply Finset.card_le_card
    intro v hv
    exact (hK v u (Finset.mem_filter.mp hv).2.1).2.1
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
  · intro v
    have ht:=changed_card_triangle (Reference.neighborFinset v) (Q.neighborFinset v) ((Q\R).neighborFinset v)
    rw [hrim v] at ht
    have hh:((changed (Reference.neighborFinset v) ((Q\R).neighborFinset v)).card:ℝ)≤
      ((changed (Reference.neighborFinset v) (Q.neighborFinset v)).card:ℝ)+R.degree v:=by exact_mod_cast ht
    have hs:(R.degree v:ℝ)≤I.card:=by exact_mod_cast hRsize v
    linarith [hR v]
  constructor
  · intro v
    have ht:=changed_card_triangle (Finset.univ.filter (Href v)) (Finset.univ.filter (H v))
      (Finset.univ.filter (fun u=>H v u∧¬S v u))
    rw [hrow v] at ht
    have hh:((changed (Finset.univ.filter (Href v)) (Finset.univ.filter (fun u=>H v u∧¬S v u))).card:ℝ)≤
      ((changed (Finset.univ.filter (Href v)) (Finset.univ.filter (H v))).card:ℝ)+(Finset.univ.filter (S v)).card:=by exact_mod_cast ht
    have hs:((Finset.univ.filter (S v)).card:ℝ)≤B.card:=by exact_mod_cast hSrow v
    linarith [hRow v]
  · intro u
    have ht:=changed_card_triangle (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u))
      (Finset.univ.filter (fun v=>H v u∧¬S v u))
    rw [hcol u] at ht
    have hh:((changed (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u∧¬S v u))).card:ℝ)≤
      ((changed (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)+(Finset.univ.filter (fun v=>S v u)).card:=by exact_mod_cast ht
    have hs:((Finset.univ.filter (fun v=>S v u)).card:ℝ)≤I.card:=by exact_mod_cast hScol u
    linarith [hCol u]
end Oberwolfach
