module

public import Oberwolfach.OrdinaryInducedWheelEmbedding
public import Oberwolfach.OrdinaryWheelHostRecovery
public import Oberwolfach.OrdinaryGraphPairEmbeddings

@[expose] public section
/-! Wheels in an induced host are exactly the ambient wheels supported on
its vertex and hub domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryAmbientInducedWheel (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U) (r:ℕ)
    (C:OrdinaryWheel (Q.induce (A:Set V)) (F.induce (A:Set V)) (fun (v:A) (u:B)=>H v.val u.val) r):
    {W:OrdinaryWheel Q F H r // (ordinaryWheelRim W).support⊆A ∧ ordinaryWheelHub W∈B}:=by
  let φ:A↪V:=Function.Embedding.subtype (fun v=>v∈(A:Set V))
  let ψ:B↪U:=Function.Embedding.subtype (fun u=>u∈(B:Set U))
  let W:=universalOrdinaryWheelEmbedding φ ψ (ordinaryWheelUniversal C)
  have hW:ordinaryWheelResources W⊆ordinaryHostResources Q H:=by
    apply (ordinaryWheelResources_subset_host _ Q H).mpr
    constructor
    · intro x y hxy
      obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj φ _ _ _).mp hxy
      exact C.val.1.property hab
    · intro x hx
      change x∈((ordinaryWheelRim C).map φ).support at hx
      rw [SimpleGraph.support_map] at hx
      obtain ⟨a,ha,rfl⟩:=hx
      exact C.property.1 a ha
  have hF:∀x∈(ordinaryWheelRim W).support,∀y∈(ordinaryWheelRim W).support,¬F.Adj x y:=by
    intro x hx y hy hxy
    change x∈((ordinaryWheelRim C).map φ).support at hx
    change y∈((ordinaryWheelRim C).map φ).support at hy
    rw [SimpleGraph.support_map] at hx hy
    obtain ⟨a,ha,rfl⟩:=hx
    obtain ⟨b,hb,rfl⟩:=hy
    exact C.property.2 a ha b hb hxy
  let D:=ordinaryWheelInHost Q F H W hW hF
  refine ⟨D,?_,?_⟩
  · intro x hx
    change x∈((ordinaryWheelRim C).map φ).support at hx
    rw [SimpleGraph.support_map] at hx
    obtain ⟨a,_,rfl⟩:=hx
    exact a.property
  · exact (ordinaryWheelHub C).property

theorem ordinary_induced_wheel_surjective (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U) (r:ℕ):
    Function.Surjective (ordinaryInducedWheel Q F H A B r):=by
  intro C
  let W:=ordinaryAmbientInducedWheel Q F H A B r C
  refine ⟨W,?_⟩
  have hrim:(ordinaryWheelRim (ordinaryInducedWheel Q F H A B r W))=ordinaryWheelRim C:=by
    ext a b
    have he:=ordinary_induced_wheel_rim_map Q F H A B r W
    have hmap:(ordinaryWheelRim W.val)=(ordinaryWheelRim C).map
        (Function.Embedding.subtype (fun v=>v∈(A:Set V))):=rfl
    rw [hmap] at he
    constructor
    · intro hab
      have hh:((ordinaryWheelRim (ordinaryInducedWheel Q F H A B r W)).map
          (Function.Embedding.subtype (fun v=>v∈(A:Set V)))).Adj a.val b.val:=SimpleGraph.map_adj_apply.mpr hab
      rw [he] at hh
      exact SimpleGraph.map_adj_apply.mp hh
    · intro hab
      have hh:((ordinaryWheelRim C).map
          (Function.Embedding.subtype (fun v=>v∈(A:Set V)))).Adj a.val b.val:=SimpleGraph.map_adj_apply.mpr hab
      rw [←he] at hh
      exact SimpleGraph.map_adj_apply.mp hh
  have hhub:ordinaryWheelHub (ordinaryInducedWheel Q F H A B r W)=ordinaryWheelHub C:=by
    apply Subtype.ext
    rfl
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    exact hrim
  · exact hhub

def ordinaryInducedWheelEquiv (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U) (r:ℕ):
    {W:OrdinaryWheel Q F H r // (ordinaryWheelRim W).support⊆A ∧ ordinaryWheelHub W∈B} ≃
    OrdinaryWheel (Q.induce (A:Set V)) (F.induce (A:Set V)) (fun (v:A) (u:B)=>H v.val u.val) r:=
  Equiv.ofBijective (ordinaryInducedWheel Q F H A B r)
    ⟨ordinary_induced_wheel_injective Q F H A B r,ordinary_induced_wheel_surjective Q F H A B r⟩
end Oberwolfach
