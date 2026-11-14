module

public import Oberwolfach.PhysicalBoundaryClassesAfterPacking
public import Oberwolfach.MarkedFreshHubCommonEvent

@[expose] public section
/-! The full mixed endpoint class and a hub class change by at most the
actual unused-boundary and cleanup degrees after a packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W:Type} [Fintype W] [DecidableEq W]

def physicalIncidentCoin (x:W):W↪Sym2 W where
  toFun y:=s(x,y)
  inj':=by
    intro y z h
    rcases Sym2.eq_iff.mp h with ⟨_,hyz⟩|⟨hxz,hyx⟩
    · exact hyz
    · exact hyx.trans hxz

theorem physical_full_boundary_class_after_packing (x:W) (S:Finset W)
    (G C D:SimpleGraph W) (σ:Sym2 W→Bool)
    (hG:∀w∈S,G.Adj x w) (hCR:Disjoint C (retainedGraph G σ)):
    (changed (S.filter (fun w=>σ (physicalIncidentCoin x w)=true))
      (S.filter (fun w=>((G\C)\D).Adj x w))).card≤
      ((G\retainedGraph G σ)\C).degree x+D.degree x:=by
  apply physical_boundary_class_after_packing (physicalIncidentCoin x) S x G C D σ _ hCR
  intro w hw
  exact ⟨(SimpleGraph.mem_edgeSet G).mpr (hG w hw),by change x∈s(x,w);simp⟩

theorem physical_boundary_neighborhood_after_packing (x:W)
    (G C D:SimpleGraph W) (σ:Sym2 W→Bool)
    (hCR:Disjoint C (retainedGraph G σ)):
    (changed ((retainedGraph G σ).neighborFinset x) (((G\C)\D).neighborFinset x)).card≤
      ((G\retainedGraph G σ)\C).degree x+D.degree x:=by
  have h:=physical_full_boundary_class_after_packing x (G.neighborFinset x) G C D σ
    (by intro w hw;exact (G.mem_neighborFinset x w).mp hw) hCR
  have he₁:(G.neighborFinset x).filter (fun w=>σ (physicalIncidentCoin x w)=true)=
      (retainedGraph G σ).neighborFinset x:=by
    ext w
    simp [physicalIncidentCoin,retainedGraph,SimpleGraph.mem_neighborFinset]
  have he₂:(G.neighborFinset x).filter (fun w=>((G\C)\D).Adj x w)=
      ((G\C)\D).neighborFinset x:=by
    ext w
    simp only [Finset.mem_filter,SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj]
    tauto
  rw [he₁,he₂] at h
  exact h

variable {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem physical_hub_boundary_class_after_packing (u:U) (S:Finset V)
    (G C D:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool)
    (hG:∀v∈S,G.Adj (Sum.inr u) (Sum.inl v))
    (hCR:Disjoint C (retainedGraph G σ)):
    (changed (S.filter (fun v=>σ (hubSpokeCoin u v)=true))
      (S.filter (fun v=>((G\C)\D).Adj (Sum.inl v) (Sum.inr u)))).card≤
      ((G\retainedGraph G σ)\C).degree (Sum.inr u)+D.degree (Sum.inr u):=by
  apply physical_boundary_class_after_packing (hubSpokeCoin u) S (Sum.inr u) G C D σ _ hCR
  intro v hv
  exact ⟨(SimpleGraph.mem_edgeSet G).mpr (hG v hv).symm,by change Sum.inr u∈s(Sum.inl v,Sum.inr u);simp⟩
end Oberwolfach
