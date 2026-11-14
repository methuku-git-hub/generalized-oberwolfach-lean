module

public import Oberwolfach.FixedHubAssignedComponents
public import Oberwolfach.FactorComponentHubEquiv
public import Oberwolfach.ComponentFamilyPartialEmbedding

@[expose] public section
/-! For each fixed hub, glue the selected component maps into one injective
partial map on exactly the union of their source components. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U A:Type} [Fintype U] [DecidableEq U]

theorem assigned_factor_partial_embeddings
    (F:U→SimpleGraph (Fin n)) (hub:A→U)
    (C:∀a,(F (hub a)).ConnectedComponent)
    (assign:A↪(Σu,(F u).ConnectedComponent))
    (hC:∀a,(⟨hub a,C a⟩:Σu,(F u).ConnectedComponent)=assign a)
    (f:∀a,C a↪Fin n)
    (hdis:∀a b,a≠b→hub a=hub b→
      Disjoint (Finset.univ.image (f a)) (Finset.univ.image (f b))):
    ∀u,
    let B:Type:={a:A // hub a=u}
    let D:B→(F u).ConnectedComponent:=fun a=>
      factorComponentAtAssignedHub F ⟨hub a.val,C a.val⟩ u a.property
    let fB:∀a:B,D a↪Fin n:=fun a=>
      (factorComponentHubEquiv F ⟨hub a.val,C a.val⟩ u a.property).toEmbedding.trans (f a.val)
    ∃ψ:{v:Fin n // ∃a:B,v∈(D a).supp}↪Fin n,
      ∀a (x:D a),ψ ⟨x.val,⟨a,x.property⟩⟩=fB a x :=by
  intro u B D fB
  have hD:Function.Injective D:=fixed_hub_assigned_components_injective F hub C assign hC u
  have hB:∀a b:B,a≠b→Disjoint (Finset.univ.image (fB a)) (Finset.univ.image (fB b)):=by
    intro a b hne
    have hne':a.val≠b.val:=by intro h;exact hne (Subtype.ext h)
    have hu:hub a.val=hub b.val:=a.property.trans b.property.symm
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨x,_,hx⟩:=Finset.mem_image.mp hv
    obtain ⟨y,_,hy⟩:=Finset.mem_image.mp hv'
    have h₁:v∈Finset.univ.image (f a.val):=by
      apply Finset.mem_image.mpr
      refine ⟨factorComponentHubEquiv F ⟨hub a.val,C a.val⟩ u a.property x,Finset.mem_univ _,?_⟩
      exact hx
    have h₂:v∈Finset.univ.image (f b.val):=by
      apply Finset.mem_image.mpr
      refine ⟨factorComponentHubEquiv F ⟨hub b.val,C b.val⟩ u b.property y,Finset.mem_univ _,?_⟩
      exact hy
    exact (Finset.disjoint_left.mp (hdis a.val b.val hne' hu)) h₁ h₂
  exact component_family_partial_embedding (F u) D hD fB hB
end Oberwolfach
