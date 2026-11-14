module

public import Oberwolfach.ComponentToOrderedWheelEmbedding

@[expose] public section
/-! Select the component-to-wheel maps simultaneously. Disjoint wheel
spokes at a common hub force the corresponding vertex images to be disjoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U A:Type} [Fintype U] [DecidableEq U]

theorem ordinary_component_wheel_family_maps
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (b:ℕ) (hub:A→U) (r:A→ℕ)
    (W:∀a,OrderedOrdinaryWheel (U:=U) π b (r a))
    (C:∀a,(F (hub a)).ConnectedComponent)
    (hsize:∀a,Fintype.card (C a)=r a)
    (hhub:∀a,(W a).2=hub a)
    (hdis:∀a a',a≠a'→hub a=hub a'→Disjoint (orderedOrdinaryResources (W a)) (orderedOrdinaryResources (W a'))):
    ∃ f:∀a,(C a)↪Fin n,
      (∀a x,∃i:Fin (r a),f a x=(W a).1.val i) ∧
      (∀a,∀i:Fin (r a),∃x:C a,f a x=(W a).1.val i) ∧
      (∀a x y,(C a).toSimpleGraph.Adj x y→
        ∃i:Fin (r a),(f a x=(W a).1.val i ∧ f a y=(W a).1.val (cycleNext i)) ∨
          (f a y=(W a).1.val i ∧ f a x=(W a).1.val (cycleNext i))) ∧
      (∀a x,Sum.inr (f a x,hub a)∈orderedOrdinaryResources (W a)) ∧
      (∀a a',a≠a'→hub a=hub a'→
        Disjoint (Finset.univ.image (f a)) (Finset.univ.image (f a'))) :=by
  have hex:∀a,∃f:(C a)↪Fin n,
      (∀x,∃i:Fin (r a),f x=(W a).1.val i) ∧
      (∀i:Fin (r a),∃x:C a,f x=(W a).1.val i) ∧
      (∀x y,(C a).toSimpleGraph.Adj x y→
        ∃i:Fin (r a),(f x=(W a).1.val i ∧ f y=(W a).1.val (cycleNext i)) ∨
          (f y=(W a).1.val i ∧ f x=(W a).1.val (cycleNext i))) ∧
      (∀x,Sum.inr (f x,hub a)∈orderedOrdinaryResources (W a)):=by
    intro a
    obtain ⟨f,h1,h2,h3,h4⟩:=component_to_ordered_ordinary_wheel_embedding
      (F (hub a)) (hF (hub a)) (C a) π b (W a) (hsize a)
    refine ⟨f,h1,h2,h3,?_⟩
    intro x
    simpa only [hhub a] using h4 x
  choose f hf using hex
  refine ⟨f,?_,?_,?_,?_,?_⟩
  · intro a;exact (hf a).1
  · intro a;exact (hf a).2.1
  · intro a;exact (hf a).2.2.1
  · intro a;exact (hf a).2.2.2
  · intro a a' hne heq
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨x,_,hx⟩:=Finset.mem_image.mp hv
    obtain ⟨y,_,hy⟩:=Finset.mem_image.mp hv'
    have h₁:Sum.inr (v,hub a)∈orderedOrdinaryResources (W a):=by
      rw [←hx];exact (hf a).2.2.2 x
    have h₂:Sum.inr (v,hub a)∈orderedOrdinaryResources (W a'):=by
      rw [heq,←hy];exact (hf a').2.2.2 y
    exact (Finset.disjoint_left.mp (hdis a a' hne heq)) h₁ h₂
end Oberwolfach
