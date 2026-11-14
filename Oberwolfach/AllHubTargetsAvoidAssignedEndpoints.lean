module

public import Oberwolfach.ProtectedPairAllowedEdges
public import Oberwolfach.InnerRequiredTargets

@[expose] public section
/-! Missing targets may be covered at every hub: they avoid every endpoint
of a bad edge assigned from a protected pair list. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem all_hub_targets_avoid_assigned_endpoints
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (I:Finset V) (protectedH:Finset U) (Lists Outer Y Absorber Old:U→Finset V)
    (hsub:∀u,Lists u⊆Outer u):
    ∀u e v,v∈e.toFinset→u∈protectedPairEdgeHubs Lists protectedH e→
      v∉innerRequiredTargets Finset.univ I Outer Y Absorber Old u :=by
  intro u e v hv hu ht
  have hl:v∈Lists u:=(Finset.mem_filter.mp hu).2.2 v hv
  have ho:v∈Outer u:=hsub u hl
  simp only [innerRequiredTargets,Finset.mem_univ,if_true,Finset.mem_sdiff,Finset.mem_union] at ht
  exact ht.2 (Or.inl (Or.inl (Or.inl ho)))
end Oberwolfach
