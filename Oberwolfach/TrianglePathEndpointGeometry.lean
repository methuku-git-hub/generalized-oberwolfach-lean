module

public import Oberwolfach.TriangleSharedEndpointGeometry

@[expose] public section

/-! Identify the endpoints of zero-length rim paths and positive spoke
paths. Only the spoke endpoints are individually injective; the rim
endpoints have the weaker, precisely sufficient pair injectivities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem triangular_path_endpoint_geometry (G Q:SimpleGraph V) (H₀:V→U→Prop)
    (φ:V→V) (hφ:∀ v w,G.Adj v w→φ v≠φ w)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (hσ:∀ v w,σ v w≠w) (h:G.edgeFinset↪U)
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (hrim:∀ e:G.edgeFinset,(p (.inl e)).2.2.length=0)
    (hsp:∀ e:{e:V×U // H₀ e.1 e.2},(p (.inr e)).2.2.IsPath∧0<(p (.inr e)).2.2.length)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset):
    let a:=transformerRimEndpoint G Q H₀ p
    let z:=transformerSpokeEndpoint G Q H₀ b p
    let u:=transformerAssignedHub G σ h
    Function.Injective z ∧ (∀ d e,a d≠z e) ∧
      Function.Injective (fun d:Σ v,G.neighborSet v=>(φ d.1,a d)) ∧
      Function.Injective (fun d=>(a d,u d)):=by
  dsimp only
  let pe:G.edgeFinset↪V:=⟨fun e=>(p (.inl e)).1,by
    intro e f he
    change (p (.inl e)).1=(p (.inl f)).1 at he
    by_contra hne
    exact Finset.disjoint_left.mp (hdis (.inl e) (.inl f) (fun hh=>hne (Sum.inl.inj hh)))
      (List.mem_toFinset.mpr (p (.inl e)).2.2.start_mem_support)
      (he.symm ▸ List.mem_toFinset.mpr (p (.inl f)).2.2.start_mem_support)⟩
  have ha (d:Σ v,G.neighborSet v):transformerRimEndpoint G Q H₀ p d=pe (rimIncidenceEquiv G d).1:=by
    have hend:=(p (.inl (rimIncidenceEquiv G d).1)).2.2.eq_of_length_eq_zero (hrim _)
    simp only [transformerRimEndpoint,graphPathEndpoint,←hend,ite_self]
    rfl
  have hzinj:Function.Injective (transformerSpokeEndpoint G Q H₀ b p):=by
    have hp:=disjoint_path_endpoint_injective (fun e:{e:V×U // H₀ e.1 e.2}=>p (.inr e))
      (fun e=>(hsp e).1) (fun e=>(hsp e).2)
      (fun e f hef=>hdis (.inr e) (.inr f) (fun hh=>hef (Sum.inr.inj hh)))
    intro d e he
    exact (spokeEndpointEquiv G H₀ b).injective (hp he)
  refine ⟨hzinj,?_,?_,?_⟩
  · intro d e he
    have ha:=graphPathEndpoint_mem (p (.inl (rimIncidenceEquiv G d).1)) (rimIncidenceEquiv G d).2
    have hz:=graphPathEndpoint_mem (p (.inr (spokeEndpointEquiv G H₀ b e).1)) (spokeEndpointEquiv G H₀ b e).2
    change transformerRimEndpoint G Q H₀ p d∈_ at ha
    change transformerSpokeEndpoint G Q H₀ b p e∈_ at hz
    exact Finset.disjoint_left.mp (hdis _ _ Sum.inl_ne_inr) (List.mem_toFinset.mpr ha)
      (he.symm ▸ List.mem_toFinset.mpr hz)
  · simpa only [ha] using triangle_root_shared_endpoint_injective G φ pe hφ
  · simpa only [ha] using triangle_shared_endpoint_hub_injective G σ hσ pe h

end Oberwolfach
