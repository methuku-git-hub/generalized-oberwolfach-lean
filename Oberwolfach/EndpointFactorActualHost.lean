module

public import Oberwolfach.EndpointTriangleClassRestriction

@[expose] public section
/-! Restrict a fresh factor to its actual surviving classes and transfer it
to the host after earlier physical-edge deletions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem endpoint_factor_actual_host
    (Q Q' F:SimpleGraph V) (S T S' T':Finset V) (hST:Disjoint S T) (hST':Disjoint S' T')
    (hS:S'⊆S) (hT:T'⊆T) (M:Finset (EndpointTriangle Q F S T))
    (hcover:M.biUnion endpointTriangleVertices⊆S'∪T') (hsub:endpointFactorGraph hST M≤Q'):
    ∃M':Finset (EndpointTriangle Q' F S' T'),
      ((∀C∈M',∀D∈M',C≠D→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices D)) ↔
        (∀C∈M,∀D∈M,C≠D→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices D))) ∧
      M'.biUnion endpointTriangleVertices=M.biUnion endpointTriangleVertices ∧
      endpointFactorGraph hST' M'=endpointFactorGraph hST M:=by
  obtain ⟨M₁,hdis₁,hcover₁,hgraph₁⟩:=endpoint_factor_restrict_classes Q F S T S' T' hST hST' hS hT M hcover
  have hsub₁:endpointFactorGraph hST' M₁≤Q':=by rw [hgraph₁];exact hsub
  obtain ⟨M₂,hdis₂,hcover₂,hgraph₂⟩:=endpoint_factor_transfer_to_host Q Q' F S' T' hST' M₁ hsub₁
  exact ⟨M₂,hdis₂.trans hdis₁,hcover₂.trans hcover₁,hgraph₂.trans hgraph₁⟩
end Oberwolfach
