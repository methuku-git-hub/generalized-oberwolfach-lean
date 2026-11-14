module

public import Oberwolfach.FixedDomainNeighbourhoodStability
public import Oberwolfach.BipartiteIntersectionEstimates

@[expose] public section

/-! Actual changed-neighbourhood cardinalities and the local hub-factor
count after later rim and spoke changes. The target remains the original
parent common neighbourhood; the realised loss has no density multiplier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem changed_predicate_card (P Q:V→Prop):
    ((changed (Finset.univ.filter P) (Finset.univ.filter Q)).card:ℝ)=
      ∑ v,if ¬(P v↔Q v) then (1:ℝ) else 0:=by
  have he:changed (Finset.univ.filter P) (Finset.univ.filter Q)=Finset.univ.filter (fun v=>¬(P v↔Q v)):=by
    ext v
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
    tauto
  rw [he]
  simp only [Finset.sum_boole]

theorem graph_changed_neighbour_card (P Q:SimpleGraph V) (v:V):
    ((changed (P.neighborFinset v) (Q.neighborFinset v)).card:ℝ)=
      ∑ z,bipAdj (fun a b=>¬(P.Adj a b↔Q.Adj a b)) v z:=by
  have he (G:SimpleGraph V):G.neighborFinset v=Finset.univ.filter (G.Adj v):=by ext z;simp
  rw [he P,he Q,changed_predicate_card]
  simp only [bipAdj]
  congr!

theorem ordinary_hub_counts_under_changes (P R Q F:SimpleGraph V) (H H':V→U→Prop)
    (p s ε θ L:ℝ) (hp:0≤p) (hs:0≤s) (hL:0≤L)
    (hbudget:ε*Fintype.card V+4*L≤θ*Fintype.card V)
    (hR:∀ v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hH:∀ u,((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>H' v u))).card:ℝ)≤L)
    (hcount:∀ u,∀ S:Finset V,S.card≤3→
      |((common (common Finset.univ S (fun v=>R.neighborFinset v)) {u}
        (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ)-
        p^S.card*s*(common Finset.univ S (fun v=>P.neighborFinset v)).card|≤ε*Fintype.card V):
    ∀ u,∀ S:Finset V,S.card≤3→
      p^S.card*s*(common Finset.univ S (fun v=>(P\F).neighborFinset v)).card-θ*Fintype.card V≤
        ((common (Finset.univ.filter (fun v=>H' v u)) S (fun v=>Q.neighborFinset v)).card:ℝ):=by
  intro u S hS
  have hh:=fixed_domain_mixed_target_stability Finset.univ S {u}
    (fun v=>R.neighborFinset v) (fun v=>Q.neighborFinset v)
    (fun u=>Finset.univ.filter (fun v=>H v u)) (fun u=>Finset.univ.filter (fun v=>H' v u))
    L L (p^S.card*s*(common Finset.univ S (fun v=>P.neighborFinset v)).card) (ε*Fintype.card V)
    (fun v _=>by simpa only [Finset.univ_inter] using hR v)
    (fun u _=>by simpa only [Finset.univ_inter] using hH u) (hcount u S hS)
  have he:common (common Finset.univ S (fun v=>Q.neighborFinset v)) {u}
      (fun u=>Finset.univ.filter (fun v=>H' v u))=
      common (Finset.univ.filter (fun v=>H' v u)) S (fun v=>Q.neighborFinset v):=by
    ext v
    simp only [mem_common_iff,Finset.mem_univ,true_and,Finset.mem_singleton,forall_eq,Finset.mem_filter,and_comm]
  rw [he,Finset.card_singleton,Nat.cast_one,one_mul] at hh
  have hsub:common Finset.univ S (fun v=>(P\F).neighborFinset v)⊆
      common Finset.univ S (fun v=>P.neighborFinset v):=by
    intro v hv
    have hs':=(mem_common_iff _ _ _ _).mp hv
    refine (mem_common_iff _ _ _ _).mpr ⟨hs'.1,?_⟩
    intro z hz
    exact (P.mem_neighborFinset z v).mpr (((P\F).mem_neighborFinset z v).mp (hs'.2 z hz)).1
  have htarget:=mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hsub):
      ((common Finset.univ S (fun v=>(P\F).neighborFinset v)).card:ℝ)≤
        (common Finset.univ S (fun v=>P.neighborFinset v)).card) (show 0≤p^S.card*s by positivity)
  have hcost:=mul_le_mul_of_nonneg_right (show (S.card:ℝ)≤3 by exact_mod_cast hS) hL
  have hlo:=(abs_le.mp hh).1
  linarith only [htarget,hcost,hlo,hbudget]

end Oberwolfach
