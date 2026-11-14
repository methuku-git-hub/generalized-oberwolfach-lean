module

public import Oberwolfach.OrdinaryCycleInEmbeddedDomain
public import Oberwolfach.OrdinaryGraphPairEmbeddings

@[expose] public section
/-! A wheel in embedded rim and spoke domains pulls back to an actual wheel
on the original types, preserving all physical resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U W Z:Type} [Fintype V] [Fintype U] [Fintype W] [Fintype Z]
  [DecidableEq V] [DecidableEq U] [DecidableEq W] [DecidableEq Z]

theorem ordinary_wheel_in_embedded_domains (φ:V↪W) (ψ:U↪Z)
    (G F:SimpleGraph V) (F':SimpleGraph W) (H:V→U→Prop) (r:ℕ)
    (hF:∀v w,F.Adj v w→F'.Adj (φ v) (φ w))
    (T:OrdinaryWheel (G.map φ) F' (ordinaryMappedSpokes H φ ψ) r):
    ∃S:OrdinaryWheel G F H r,
      (ordinaryWheelRim S).map φ=ordinaryWheelRim T ∧
      ψ (ordinaryWheelHub S)=ordinaryWheelHub T ∧
      (ordinaryWheelResources S).image (ordinaryPairResourceEmbedding φ ψ)=ordinaryWheelResources T:=by
  let C:=ordinaryWheelRim T
  have hc:IsEmbeddedCycle C r:=T.val.1.val.property
  obtain ⟨D,hD,hDG,hmap⟩:=ordinary_cycle_in_embedded_domain φ G C r hc T.val.1.property
  obtain ⟨hr,e,he⟩:=hD
  let i:Fin r:=⟨0,by omega⟩
  have hi:e i∈D.support:=by rw [he,cycle_map_support hr];exact ⟨i,rfl⟩
  have hφi:φ (e i)∈C.support:=by
    rw [←hmap,SimpleGraph.support_map]
    exact ⟨e i,hi,rfl⟩
  obtain ⟨v,u,hvu,hv,hu⟩:=T.property.1 (φ (e i)) hφi
  have hhub:ψ u=ordinaryWheelHub T:=hu
  have hspokes:∀v∈D.support,H v u:=by
    intro v hv'
    have hvφ:φ v∈C.support:=by
      rw [←hmap,SimpleGraph.support_map]
      exact ⟨v,hv',rfl⟩
    have hh:=T.property.1 (φ v) hvφ
    change ordinaryMappedSpokes H φ ψ (φ v) (ordinaryWheelHub T) at hh
    rw [←hhub] at hh
    exact (ordinaryMappedSpokes_apply H φ ψ v u).mp hh
  have hind:∀v∈D.support,∀w∈D.support,¬F.Adj v w:=by
    intro v hv' w hw' hfw
    have hvφ:φ v∈C.support:=by rw [←hmap,SimpleGraph.support_map];exact ⟨v,hv',rfl⟩
    have hwφ:φ w∈C.support:=by rw [←hmap,SimpleGraph.support_map];exact ⟨w,hw',rfl⟩
    exact T.property.2 (φ v) hvφ (φ w) hwφ (hF v w hfw)
  let S:OrdinaryWheel G F H r:=⟨(⟨⟨D,⟨hr,e,he⟩⟩,hDG⟩,u),hspokes,hind⟩
  refine ⟨S,hmap,hhub,?_⟩
  have hh:=universalOrdinaryWheelEmbedding_resources φ ψ (ordinaryWheelUniversal S)
  rw [ordinaryWheelUniversal_resources] at hh
  rw [←hh]
  ext a
  cases a with
  | inl e=>
    simp only [ordinaryWheelResources_rim]
    change e∈(D.map φ).edgeSet ↔ e∈C.edgeSet
    rw [hmap]
  | inr vu=>
    rcases vu with ⟨v,u'⟩
    simp only [ordinaryWheelResources_spoke]
    change (ψ u=u' ∧ v∈(D.map φ).support) ↔ (ordinaryWheelHub T=u' ∧ v∈C.support)
    rw [hmap,hhub]
end Oberwolfach
