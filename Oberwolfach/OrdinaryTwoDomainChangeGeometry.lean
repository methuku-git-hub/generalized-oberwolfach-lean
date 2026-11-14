module

public import Oberwolfach.OrdinaryTwoDomainSpokeGraph
public import Oberwolfach.OrdinaryTwoDomainRimGraph

@[expose] public section
/-! Exact neighborhood sets in the physical sum domain. These formulas let
the robust triangle event charge the original rim and spoke edit degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_sum_rim_neighbours (G:SimpleGraph V) (A:Finset V) (v:V):
    A.image (Sum.inl:V→V⊕U) ∩ (G.map (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U)).neighborFinset (Sum.inl v)=
      (A∩G.neighborFinset v).image Sum.inl:=by
  ext z
  cases z with
  | inl w=>
    simp [SimpleGraph.mem_neighborFinset]
    intro _
    change (G.map (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U)).Adj
      ((⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U) v) ((⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U) w) ↔ _
    exact SimpleGraph.map_adj_apply
  | inr u=>simp

theorem ordinary_sum_rim_neighbours_hub (G:SimpleGraph V) (A:Finset V) (u:U):
    A.image (Sum.inl:V→V⊕U) ∩ (G.map (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U)).neighborFinset (Sum.inr u)=∅:=by
  ext z
  cases z with
  | inr w=>simp
  | inl w=>
    simp [SimpleGraph.mem_neighborFinset]
    intro hw hadj
    obtain ⟨a,b,hab,ha,hb⟩:=(SimpleGraph.map_adj (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U) G _ _).mp hadj
    cases ha

theorem ordinary_sum_spoke_row_neighbours (H:V→U→Prop) (B:Finset U) (v:V):
    B.image (Sum.inr:U→V⊕U) ∩ (ordinaryPhysicalSpokeGraph H).neighborFinset (Sum.inl v)=
      (B.filter (H v)).image Sum.inr:=by
  ext z
  cases z <;> simp [SimpleGraph.mem_neighborFinset,ordinaryPhysicalSpokeGraph,ordinaryPhysicalGraph]

theorem ordinary_sum_spoke_row_neighbours_hub (H:V→U→Prop) (B:Finset U) (u:U):
    B.image (Sum.inr:U→V⊕U) ∩ (ordinaryPhysicalSpokeGraph H).neighborFinset (Sum.inr u)=∅:=by
  ext z
  cases z <;> simp [SimpleGraph.mem_neighborFinset,ordinaryPhysicalSpokeGraph,ordinaryPhysicalGraph]

theorem ordinary_sum_spoke_column_neighbours (H:V→U→Prop) (A:Finset V) (u:U):
    A.image (Sum.inl:V→V⊕U) ∩ (ordinaryPhysicalSpokeGraph H).neighborFinset (Sum.inr u)=
      (A.filter (fun v=>H v u)).image Sum.inl:=by
  ext z
  cases z <;> simp [SimpleGraph.mem_neighborFinset,ordinaryPhysicalSpokeGraph,ordinaryPhysicalGraph]
end Oberwolfach
