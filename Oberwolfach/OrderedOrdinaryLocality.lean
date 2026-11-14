module

public import Oberwolfach.OrderedOrdinaryWheelGeometry

@[expose] public section
/-! Locality of directed ordinary-edge and ordinary-spoke indicators. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {r b:ℕ} {π:Equiv.Perm V}

theorem orderedOrdinaryResourceEmbedding_injective:
    Function.Injective (orderedOrdinaryResourceEmbedding (V:=V) (U:=U)):=by
  intro a b h
  cases a <;> cases b <;> simp_all [orderedOrdinaryResourceEmbedding,Prod.ext_iff]

theorem orderedOrdinaryResourceCoordinates_card (π:Equiv.Perm V) (d:ℕ) (a:(V×V)⊕(V×U)):
    (orderedOrdinaryResourceCoordinates π d a).card≤8*d+6:=
  rawMarkedResourceCoordinates_card π d (orderedOrdinaryResourceEmbedding a)

theorem orderedOrdinaryResourceCoordinates_reverse_card (π:Equiv.Perm V) (d:ℕ) (e:RawWheelCoordinate V U):
    (Finset.univ.filter (fun a:(V×V)⊕(V×U)=>e∈orderedOrdinaryResourceCoordinates π d a)).card≤8*d+6:=by
  let A:=Finset.univ.filter (fun a:(V×V)⊕(V×U)=>e∈orderedOrdinaryResourceCoordinates π d a)
  let B:=Finset.univ.filter (fun a:((V×V)⊕(V×V))⊕(Bool×V×U)=>e∈rawMarkedResourceCoordinates π d a)
  have hs:A.image orderedOrdinaryResourceEmbedding⊆B:=by
    intro a ha
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩
  calc
    _ = (A.image orderedOrdinaryResourceEmbedding).card := (Finset.card_image_of_injective _ orderedOrdinaryResourceEmbedding_injective).symm
    _ ≤ B.card := Finset.card_le_card hs
    _ ≤ 8*d+6 := rawMarkedResourceCoordinates_reverse_card π d e

theorem orderedOrdinaryResources_card (W:OrderedOrdinaryWheel (U:=U) π b r):
    (orderedOrdinaryResources W).card≤2*r:=by
  unfold orderedOrdinaryResources
  have hh:=Finset.card_union_le
    (Finset.univ.image (fun i:Fin r=>(Sum.inl (W.1.val i,W.1.val (cycleNext i)):(V×V)⊕(V×U))))
    (Finset.univ.image (fun i:Fin r=>Sum.inr (W.1.val i,W.2)))
  have h1:=Finset.card_image_le (s:=(Finset.univ:Finset (Fin r))) (f:=fun i=>Sum.inl (α:=V×V) (β:=V×U) (W.1.val i,W.1.val (cycleNext i)))
  have h2:=Finset.card_image_le (s:=(Finset.univ:Finset (Fin r))) (f:=fun i=>Sum.inr (α:=V×V) (β:=V×U) (W.1.val i,W.2))
  simp only [Finset.card_univ,Fintype.card_fin] at h1 h2
  omega
end Oberwolfach
