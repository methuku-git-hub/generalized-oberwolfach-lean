module

public import Oberwolfach.OrdinaryComponentToWheel
public import Oberwolfach.ComponentFamilyPartialEmbedding

@[expose] public section
/-! At one hub, pairwise resource-disjoint wheels assigned to distinct
factor components give a single injective partial embedding of all of them. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_wheels_partial_embedding {n:ℕ} {A U:Type} [Fintype U] [DecidableEq U]
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2)
    (C:A→F.ConnectedComponent) (hC:Function.Injective C) (len:A→ℕ)
    (W:∀a,UniversalOrdinaryWheel (Fin n) U (len a)) (u:U)
    (hsize:∀a,Fintype.card (C a)=len a) (hhub:∀a,ordinaryWheelHub (W a)=u)
    (hdis:∀a b,a≠b→Disjoint (ordinaryWheelResources (W a)) (ordinaryWheelResources (W b))):
    ∃g:∀a,C a↪Fin n,
      (∀a,Set.range (g a)=(ordinaryWheelRim (W a)).support) ∧
      (∀a (x y:C a),(C a).toSimpleGraph.Adj x y↔(ordinaryWheelRim (W a)).Adj (g a x) (g a y)) ∧
    ∃ψ:{v:Fin n // ∃a,v∈(C a).supp}↪Fin n,
      ∀a (x:C a),ψ ⟨x.val,⟨a,x.property⟩⟩=g a x :=by
  have hex:∀a,∃g:C a↪Fin n,Set.range g=(ordinaryWheelRim (W a)).support ∧
      ∀x y:C a,(C a).toSimpleGraph.Adj x y↔(ordinaryWheelRim (W a)).Adj (g x) (g y):=
    fun a=>ordinary_component_to_wheel F hF (C a) (hsize a) (W a)
  choose g hRange hGraph using hex
  have hGdis:∀a b,a≠b→Disjoint (Finset.univ.image (g a)) (Finset.univ.image (g b)):=by
    intro a b hab
    apply Finset.disjoint_left.mpr
    intro v hva hvb
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hva
    obtain ⟨y,_,hy⟩:=Finset.mem_image.mp hvb
    have ha:g a x∈(ordinaryWheelRim (W a)).support:=by rw [←hRange a];exact ⟨x,rfl⟩
    have hb:g a x∈(ordinaryWheelRim (W b)).support:=by rw [←hRange b];exact ⟨y,hy⟩
    have hea:Sum.inr (g a x,u)∈ordinaryWheelResources (W a):=
      (ordinaryWheelResources_spoke (W a) (g a x) u).2 ⟨hhub a,ha⟩
    have heb:Sum.inr (g a x,u)∈ordinaryWheelResources (W b):=
      (ordinaryWheelResources_spoke (W b) (g a x) u).2 ⟨hhub b,hb⟩
    exact Finset.disjoint_left.mp (hdis a b hab) hea heb
  obtain ⟨ψ,hψ⟩:=component_family_partial_embedding F C hC g hGdis
  exact ⟨g,hRange,hGraph,ψ,hψ⟩
end Oberwolfach
