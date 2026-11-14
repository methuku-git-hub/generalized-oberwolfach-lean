module

public import Oberwolfach.TransformerOriginalEdgeIdentity

@[expose] public section

/-! Exact signed contribution of the original typed rim and spoke edges.
Only injectivity of the two physical edge maps is used, not injectivity
of the row or hub maps individually. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A S:Type} [Fintype A] [Fintype S] [DecidableEq A] [DecidableEq S]
    [DecidableEq V] [DecidableEq U]

 theorem marked_old_resource_integer_identity (r r':A→Finset V) (s s':S→V×U)
    (hr:Function.Injective r) (hr':Function.Injective r') (hs:Function.Injective s) (hs':Function.Injective s')
    (e:Finset V⊕(V×U)):
    (∑ i,physicalIntDelta (Sum.inl (r i)) (Sum.inl (r' i)) e)+
      (∑ i,physicalIntDelta (Sum.inr (s i)) (Sum.inr (s' i)) e)=
    (if e∈(Finset.univ.image (fun i=>Sum.inl (r i))∪Finset.univ.image (fun i=>Sum.inr (s i))) then (1:ℤ) else 0)-
      (if e∈(Finset.univ.image (fun i=>Sum.inl (r' i))∪Finset.univ.image (fun i=>Sum.inr (s' i))) then 1 else 0):=by
  rw [physical_delta_sum _ _ (fun i j h=>hr (Sum.inl.inj h)) (fun i j h=>hr' (Sum.inl.inj h)),
    physical_delta_sum _ _ (fun i j h=>hs (Sum.inr.inj h)) (fun i j h=>hs' (Sum.inr.inj h))]
  cases e <;> simp only [Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and,
    Sum.inl_ne_inr,Sum.inr_ne_inl,exists_false,ite_false,sub_self,add_zero,zero_add,or_false,false_or]

end Oberwolfach
