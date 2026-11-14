module

public import Oberwolfach.PhysicalHostDegreeBounds
public import Oberwolfach.EmbeddedClassChanges

@[expose] public section
/-! Exact translation of row and column edits to the physical undirected
spoke graph on the disjoint sum of the two original domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryPhysicalSpokeGraph (H:V→U→Prop):SimpleGraph (V⊕U):=ordinaryPhysicalGraph ⊥ H

theorem ordinary_physical_spoke_graph_difference (H J:V→U→Prop):
    ordinaryPhysicalSpokeGraph H\ordinaryPhysicalSpokeGraph J=
      ordinaryPhysicalSpokeGraph (fun v u=>H v u∧¬J v u):=by
  ext a b
  cases a <;> cases b <;> simp [ordinaryPhysicalSpokeGraph,ordinaryPhysicalGraph]

theorem ordinary_physical_spoke_difference_degree (H J:V→U→Prop):
    (∀v,(ordinaryPhysicalSpokeGraph H\ordinaryPhysicalSpokeGraph J).degree (Sum.inl v)=
      (Finset.univ.filter (fun u=>H v u∧¬J v u)).card) ∧
    (∀u,(ordinaryPhysicalSpokeGraph H\ordinaryPhysicalSpokeGraph J).degree (Sum.inr u)=
      (Finset.univ.filter (fun v=>H v u∧¬J v u)).card):=by
  constructor
  · intro v
    have hh:=ordinary_physical_degree_row (⊥:SimpleGraph V) (fun v u=>H v u∧¬J v u) v
    simp only [←SimpleGraph.ncard_neighborSet] at hh ⊢
    have hb:((⊥:SimpleGraph V).neighborSet v).ncard=0:=by simp
    rw [hb,zero_add] at hh
    rw [ordinary_physical_spoke_graph_difference]
    convert hh using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
  · intro u
    have hh:=ordinary_physical_degree_column (⊥:SimpleGraph V) (fun v u=>H v u∧¬J v u) u
    simp only [←SimpleGraph.ncard_neighborSet] at hh ⊢
    rw [ordinary_physical_spoke_graph_difference]
    convert hh using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _

theorem ordinary_physical_spoke_difference_bound (H J:V→U→Prop) (L:ℝ)
    (hrow:∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (J v))).card:ℝ)≤L)
    (hcol:∀u,((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>J v u))).card:ℝ)≤L):
    ∀z,((ordinaryPhysicalSpokeGraph H\ordinaryPhysicalSpokeGraph J).degree z:ℝ)≤L:=by
  intro z
  cases z with
  | inl v=>
    rw [(ordinary_physical_spoke_difference_degree H J).1 v]
    have hs:Finset.univ.filter (fun u=>H v u∧¬J v u)⊆
        changed (Finset.univ.filter (H v)) (Finset.univ.filter (J v)):=by
      intro u hu
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu
      simp [changed,hu.1,hu.2]
    exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans (hrow v)
  | inr u=>
    rw [(ordinary_physical_spoke_difference_degree H J).2 u]
    have hs:Finset.univ.filter (fun v=>H v u∧¬J v u)⊆
        changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>J v u)):=by
      intro v hv
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hv
      simp [changed,hv.1,hv.2]
    exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans (hcol u)
end Oberwolfach
