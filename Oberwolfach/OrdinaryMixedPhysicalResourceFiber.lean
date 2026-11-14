module

public import Oberwolfach.RawMarkedResourceCoordinates
public import Oberwolfach.PhysicalResourcePairFiberBound

@[expose] public section
/-! Physical resources forget whether a rim occurrence is ordinary or
shifted, and forget whether a spoke is an interval or an ordinary spoke.
Their typed fibers have size at most four. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

def ordinaryMixedPhysicalResource (π:Equiv.Perm V):
    (((V×V)⊕(V×V))⊕(Bool×V×U))→Sym2 V⊕(V×U) :=
  Sum.elim (fun e=>Sum.inl (markedPairPhysical π e)) (fun a=>Sum.inr a.2)

theorem ordinary_mixed_physical_resource_fiber_card
    (π:Equiv.Perm V) (e:Sym2 V⊕(V×U)):
    (Finset.univ.filter (fun a=>ordinaryMixedPhysicalResource π a=e)).card≤4 := by
  cases e with
  | inl e=>
    have he:Finset.univ.filter (fun a=>ordinaryMixedPhysicalResource π a=Sum.inl e)=
      (Finset.univ.filter (fun a=>markedPairPhysical π a=e)).image (Sum.inl (β:=Bool×V×U)) := by
      ext a
      cases a <;> simp [ordinaryMixedPhysicalResource]
    rw [he]
    exact Finset.card_image_le.trans (markedPairPhysical_fiber_card π e)
  | inr e=>
    rcases e with ⟨v,u⟩
    let T:Finset (((V×V)⊕(V×V))⊕(Bool×V×U)):=
      {Sum.inr (false,v,u),Sum.inr (true,v,u)}
    have hsub:Finset.univ.filter (fun a=>ordinaryMixedPhysicalResource π a=Sum.inr (v,u))⊆T := by
      intro a ha
      have hh:ordinaryMixedPhysicalResource π a=Sum.inr (v,u):=(Finset.mem_filter.mp ha).2
      cases a with
      | inl a=>simp [ordinaryMixedPhysicalResource] at hh
      | inr a=>
        obtain ⟨b,x,w⟩:=a
        simp only [ordinaryMixedPhysicalResource,Sum.elim_inr,Sum.inr.injEq,Prod.mk.injEq] at hh
        obtain ⟨rfl,rfl⟩:=hh
        cases b <;> simp [T]
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two.trans (by omega))
end Oberwolfach
