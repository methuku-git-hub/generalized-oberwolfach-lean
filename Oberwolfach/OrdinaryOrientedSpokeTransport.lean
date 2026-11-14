module

public import Oberwolfach.OrdinaryEmbeddedPackingHosts

@[expose] public section
/-! Orient the two parts of an undirected bipartite spoke graph. Rim support
chooses the first part, so every actual wheel and its resources are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U W Z:Type} [Fintype V] [Fintype U] [Fintype W] [Fintype Z]
  [DecidableEq V] [DecidableEq U] [DecidableEq W] [DecidableEq Z]
  (φ:V↪W) (ψ:U↪Z) (Q F:SimpleGraph W) (H:W→Z→Prop) (r:ℕ)
  (hQ:∀v w,Q.Adj v w→v∈Set.range φ ∧ w∈Set.range φ)
  (hH:∀v∈Set.range φ,∀u,H v u→u∈Set.range ψ)

def ordinaryOrientedWheel (T:OrdinaryWheel Q F H r):
    OrdinaryWheel Q F (ordinaryMappedSpokes (fun v u=>H (φ v) (ψ u)) φ ψ) r:=by
  refine ⟨T.val,?_,T.property.2⟩
  intro a ha
  have ha':a∈Q.support:=SimpleGraph.support_mono T.val.1.property ha
  obtain ⟨b,hab⟩:=Q.mem_support.mp ha'
  obtain ⟨v,hv⟩:=(hQ a b hab).1
  obtain ⟨u,hu⟩:=hH a ⟨v,hv⟩ (ordinaryWheelHub T) (T.property.1 a ha)
  refine ⟨v,u,?_,hv,hu⟩
  change H (φ v) (ψ u)
  rw [hv,hu]
  exact T.property.1 a ha

theorem ordinaryOrientedWheel_resources (T:OrdinaryWheel Q F H r):
    ordinaryWheelResources (ordinaryOrientedWheel φ ψ Q F H r hQ hH T)=ordinaryWheelResources T:=rfl

theorem ordinaryOrientedWheel_injective:
    Function.Injective (ordinaryOrientedWheel φ ψ Q F H r hQ hH):=by
  intro A B he
  apply ordinaryWheelResources_injective
  have hh:=congrArg ordinaryWheelResources he
  simpa only [ordinaryOrientedWheel_resources] using hh

theorem ordinary_oriented_packing_resources (M:Finset (OrdinaryWheel Q F H r)):
    (M.image (ordinaryOrientedWheel φ ψ Q F H r hQ hH)).biUnion ordinaryWheelResources=
      M.biUnion ordinaryWheelResources:=by
  ext e
  simp only [Finset.mem_biUnion,Finset.mem_image,ordinaryOrientedWheel_resources]
  constructor
  · rintro ⟨_,⟨T,hT,rfl⟩,he⟩;exact ⟨T,hT,he⟩
  · rintro ⟨T,hT,he⟩;exact ⟨_,⟨T,hT,rfl⟩,he⟩

theorem ordinary_oriented_row_cover (M:Finset (OrdinaryWheel Q F H r)) (x:V) (A:Finset W) (K:ℕ)
    (hcover:OrdinaryRowCover M (φ x) A K):
    OrdinaryRowCover (M.image (ordinaryOrientedWheel φ ψ Q F H r hQ hH)) (φ x) A K:=by
  let P:=M.image (ordinaryOrientedWheel φ ψ Q F H r hQ hH)
  have he: P.biUnion ordinaryWheelResources=M.biUnion ordinaryWheelResources:=ordinary_oriented_packing_resources φ ψ Q F H r hQ hH M
  rw [ordinary_packing_resources_eq_host,ordinary_packing_resources_eq_host] at he
  have hrim:ordinaryWheelRimGraph P=ordinaryWheelRimGraph M:=by
    ext a b
    have hh:=congrArg (fun S:Finset (Sym2 W⊕(W×Z))=>Sum.inl s(a,b)∈S) he
    simpa only [ordinaryHostResources_rim,SimpleGraph.mem_edgeSet] using (Iff.of_eq hh)
  have hspoke:ordinaryPackingSpokes P=ordinaryPackingSpokes M:=by
    funext a b;apply propext
    have hh:=congrArg (fun S:Finset (Sym2 W⊕(W×Z))=>Sum.inr (a,b)∈S) he
    simpa only [ordinaryHostResources_spoke] using (Iff.of_eq hh)
  change OrdinaryRowCover P (φ x) A K
  constructor
  · intro T hT S hS hne
    obtain ⟨T',hT',rfl⟩:=Finset.mem_image.mp hT
    obtain ⟨S',hS',rfl⟩:=Finset.mem_image.mp hS
    exact hcover.disjoint T' hT' S' hS' (fun h=>hne (congrArg (ordinaryOrientedWheel φ ψ Q F H r hQ hH) h))
  · intro T hT a ha
    obtain ⟨T',hT',rfl⟩:=Finset.mem_image.mp hT
    exact hcover.support T' hT' a ha
  · rw [hrim];exact hcover.rims
  · intro u
    rw [hspoke,hcover.spokes]
    constructor
    · intro hu
      obtain ⟨a,ha⟩:=hH (φ x) ⟨x,rfl⟩ u hu
      refine ⟨x,a,?_,rfl,ha⟩
      change H (φ x) (ψ a)
      rw [ha];exact hu
    · rintro ⟨v,a,ha,hv,hu⟩
      exact hv ▸ hu ▸ ha
  · rw [hrim];exact hcover.rimDegree
  · rw [hspoke];exact hcover.rowDegree
  · rw [hspoke];exact hcover.columnDegree
end Oberwolfach
