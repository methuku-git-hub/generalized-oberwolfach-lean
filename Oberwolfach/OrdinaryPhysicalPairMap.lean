module

public import Oberwolfach.OrdinaryGraphPairEmbeddings
public import Oberwolfach.OrdinaryPhysicalGraphDeletion

@[expose] public section
/-! Mapping the rim and spoke pair is the same physical graph map on the
sum of the vertex and hub domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U':Type} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']

theorem ordinary_physical_pair_map (Q:SimpleGraph V) (H:V→U→Prop) (φ:V↪V') (ψ:U↪U'):
    ordinaryPhysicalGraph (Q.map φ) (ordinaryMappedSpokes H φ ψ)=
      (ordinaryPhysicalGraph Q H).map (φ.sumMap ψ):=by
  ext a b
  constructor
  · intro hab
    cases a with
    | inl x=>cases b with
      | inl y=>
        obtain ⟨v,w,h,rfl,rfl⟩:=(SimpleGraph.map_adj φ Q x y).mp hab
        change ((ordinaryPhysicalGraph Q H).map (φ.sumMap ψ)).Adj ((φ.sumMap ψ) (Sum.inl v)) ((φ.sumMap ψ) (Sum.inl w))
        exact SimpleGraph.map_adj_apply.mpr (show (ordinaryPhysicalGraph Q H).Adj (Sum.inl v) (Sum.inl w) from h)
      | inr y=>
        obtain ⟨v,u,h,rfl,rfl⟩:=hab
        change ((ordinaryPhysicalGraph Q H).map (φ.sumMap ψ)).Adj ((φ.sumMap ψ) (Sum.inl v)) ((φ.sumMap ψ) (Sum.inr u))
        exact SimpleGraph.map_adj_apply.mpr (show (ordinaryPhysicalGraph Q H).Adj (Sum.inl v) (Sum.inr u) from h)
    | inr y=>cases b with
      | inl x=>
        obtain ⟨v,u,h,rfl,rfl⟩:=hab
        change ((ordinaryPhysicalGraph Q H).map (φ.sumMap ψ)).Adj ((φ.sumMap ψ) (Sum.inr u)) ((φ.sumMap ψ) (Sum.inl v))
        exact SimpleGraph.map_adj_apply.mpr (show (ordinaryPhysicalGraph Q H).Adj (Sum.inr u) (Sum.inl v) from h)
      | inr z=>exact hab.elim
  · intro hab
    obtain ⟨a,b,h,rfl,rfl⟩:=(SimpleGraph.map_adj (φ.sumMap ψ) (ordinaryPhysicalGraph Q H) a b).mp hab
    cases a with
    | inl v=>cases b with
      | inl w=>exact SimpleGraph.map_adj_apply.mpr h
      | inr u=>exact ⟨v,u,h,rfl,rfl⟩
    | inr u=>cases b with
      | inl v=>exact ⟨v,u,h,rfl,rfl⟩
      | inr z=>exact h.elim
end Oberwolfach
