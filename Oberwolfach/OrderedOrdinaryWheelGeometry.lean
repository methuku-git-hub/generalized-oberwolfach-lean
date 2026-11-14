module

public import Oberwolfach.OrderedOrdinaryWheelResources

@[expose] public section
/-! Distinct requests in an ordered separated ordinary wheel use disjoint
physical-edge or interval coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {r:ℕ} {π:Equiv.Perm V}

def orderedOrdinaryResourceEmbedding : (V×V)⊕(V×U) → ((V×V)⊕(V×V))⊕(Bool×V×U)
  | Sum.inl e=>Sum.inl (Sum.inl e)
  | Sum.inr a=>Sum.inr (false,a.1,a.2)

def orderedOrdinaryResourceCoordinates (π:Equiv.Perm V) (d:ℕ) (a:(V×V)⊕(V×U)):
    Finset (RawWheelCoordinate V U):=
  rawMarkedResourceCoordinates π d (orderedOrdinaryResourceEmbedding a)

theorem orderedOrdinaryCoordinates_disjoint (d:ℕ) (hr:3≤r)
    (W:OrderedOrdinaryWheel (U:=U) π (3*d) r)
    (a b:(V×V)⊕(V×U))
    (ha:a∈orderedOrdinaryResources W) (hb:b∈orderedOrdinaryResources W) (hne:a≠b):
    Disjoint (orderedOrdinaryResourceCoordinates π d a) (orderedOrdinaryResourceCoordinates π d b) :=by
  cases a with
  | inl a=>
    cases b with
    | inl b=>
      obtain ⟨i,hi⟩:=(orderedOrdinaryResources_rim W a).mp ha
      obtain ⟨j,hj⟩:=(orderedOrdinaryResources_rim W b).mp hb
      apply Finset.disjoint_singleton.mpr
      intro he
      have hp:s(a.1,a.2)=s(b.1,b.2):=Sum.inl.inj he
      have hij:i=j:=orderedOrdinaryPhysical_edge_injective hr W (by simpa [←hi,←hj] using hp)
      apply hne
      exact congrArg Sum.inl (hi.symm.trans (hij ▸ hj))
    | inr b=>simp [orderedOrdinaryResourceCoordinates,orderedOrdinaryResourceEmbedding,rawMarkedResourceCoordinates]
  | inr a=>
    cases b with
    | inl b=>simp [orderedOrdinaryResourceCoordinates,orderedOrdinaryResourceEmbedding,rawMarkedResourceCoordinates]
    | inr b=>
      obtain ⟨i,hi⟩:=(orderedOrdinaryResources_spoke W a).mp ha
      obtain ⟨j,hj⟩:=(orderedOrdinaryResources_spoke W b).mp hb
      have hij:i≠j:=by intro h;subst j;exact hne (congrArg Sum.inr (hi.symm.trans hj))
      have hv:W.1.val i=a.1:=congrArg Prod.fst hi
      have hw:W.1.val j=b.1:=congrArg Prod.fst hj
      have hsep:¬PermutationClose π (3*d) a.1 b.1:=by
        rw [←hv,←hw];exact W.1.property i j hij
      apply Finset.disjoint_left.mpr
      intro e he hf
      obtain ⟨x,hx,he⟩:=Finset.mem_image.mp he
      obtain ⟨y,hy,hf⟩:=Finset.mem_image.mp hf
      have hxy:=Sum.inr.inj (he.trans hf.symm)
      exact Finset.disjoint_left.mp (rawIntervalFamilyCoordinates_disjoint π d a b (Or.inr hsep))
        hx (hxy ▸ hy)
end Oberwolfach
