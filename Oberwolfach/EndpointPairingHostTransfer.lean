module

public import Oberwolfach.EndpointPairing

@[expose] public section
/-! An endpoint assignment survives transfer to a later host whenever its
actual physical edges survive. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W:Type} [Fintype W] [DecidableEq W]

def endpointPairingToHost (G G' F:SimpleGraph W) (A B:Finset W)
    (P:EndpointPairing G F A B) (hsub:P.graph≤G'):EndpointPairing G' F A B where
  disjoint_parts:=P.disjoint_parts
  left:=P.left
  right:=P.right
  adjacent:=by
    intro u
    constructor
    · apply hsub
      exact ⟨u,Or.inr ⟨rfl,Or.inl rfl⟩⟩
    · apply hsub
      exact ⟨u,Or.inr ⟨rfl,Or.inr rfl⟩⟩
  avoid:=P.avoid
  disjoint_ranges:=P.disjoint_ranges
  cover:=P.cover

theorem endpoint_pairing_to_host_graph (G G' F:SimpleGraph W) (A B:Finset W)
    (P:EndpointPairing G F A B) (hsub:P.graph≤G'):
    (endpointPairingToHost G G' F A B P hsub).graph=P.graph:=by
  ext x y
  rfl

theorem endpoint_pairing_survives_deletion (G G' F K:SimpleGraph W) (A B:Finset W)
    (P:EndpointPairing G F A B) (havoid:Disjoint P.graph K) (hkeep:G\K≤G'):
    P.graph≤G':=by
  intro a b hab
  apply hkeep
  refine ⟨?_,?_⟩
  · exact ((spanningRestriction_adj _ _ _ _).mp (P.graph_le hab)).1
  · intro hk
    exact (disjoint_iff_inf_le.mp havoid) (v:=a) (w:=b) ⟨hab,hk⟩
end Oberwolfach
