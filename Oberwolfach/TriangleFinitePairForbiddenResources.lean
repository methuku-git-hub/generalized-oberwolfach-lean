module

public import Oberwolfach.TriangleFinitePairExtendedTransformer
public import Oberwolfach.OrdinaryTransformerForbiddenEdges

@[expose] public section
/-! The finite-pair transformer's vertex exclusions imply avoidance of
any earlier resource set whose endpoints were put in the forbidden sets. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem triangle_transformer_avoids_forbidden_resources
    (T L:Finset (Sym2 V⊕(V×U))) (R ZV:Finset V) (B ZU:Finset U)
    (hrows:ordinaryResourceRows L⊆ZV) (hhubs:ordinaryResourceHubs L⊆ZU)
    (hrootR:∀ v∈R,∀ w∈R,Sum.inl s(v,w)∉T)
    (hrootS:∀ v∈R,∀ z∈B,Sum.inr (v,z)∉T)
    (havoidR:∀ v∈ordinaryResourceRows T,v∈ZV→v∈R)
    (havoidU:∀ z∈ordinaryResourceHubs T,z∈ZU→z∈B):
    Disjoint T L:=by
  apply ordinary_transformer_forbidden_edges T L R ZV ZU hrows hhubs
  · intro v hv w he
    apply havoidR _ _ hv
    exact Finset.mem_biUnion.mpr ⟨Sum.inl s(v,w),he,by simp⟩
  · intro v hv u he
    apply havoidR _ _ hv
    exact Finset.mem_biUnion.mpr ⟨Sum.inr (v,u),he,by simp⟩
  · exact hrootR
  · intro v hv u hu he
    have hu':u∈ordinaryResourceHubs T:=Finset.mem_biUnion.mpr ⟨Sum.inr (v,u),he,by simp⟩
    exact hrootS v hv u (havoidU u hu' hu) he
end Oberwolfach
