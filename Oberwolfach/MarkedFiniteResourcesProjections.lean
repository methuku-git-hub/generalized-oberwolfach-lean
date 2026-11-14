module

public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section
/-! A mixed physical-resource set uniquely determines its rim set and its
spoke set, even when the underlying typed arc domains differ. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K':Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K] [Fintype E'] [Fintype K']
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K] [DecidableEq E'] [DecidableEq K']
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}
  {tail' head':E'→V} {ktail' khead':K'→V} {π':Equiv.Perm V}
theorem marked_finite_resources_determine_projections
    (A:Finset (E⊕K)) (S:Finset (V×U)) (A':Finset (E'⊕K')) (S':Finset (V×U))
    (he:markedFiniteResources tail head ktail khead π A S=
      markedFiniteResources tail' head' ktail' khead' π' A' S'):
    A.image (markedPhysicalEdge tail head ktail khead π)=
      A'.image (markedPhysicalEdge tail' head' ktail' khead' π') ∧ S=S':=by
  constructor
  · ext e
    have h:=congrArg (fun R:Finset (Finset V⊕(V×U))=>Sum.inl e∈R) he
    simpa only [markedFiniteResources,Finset.mem_union,Finset.mem_image,Sum.inl.injEq,
      Sum.inr_ne_inl,and_false,exists_false,or_false] using Iff.of_eq h
  · ext z
    have h:=congrArg (fun R:Finset (Finset V⊕(V×U))=>Sum.inr z∈R) he
    simpa only [markedFiniteResources,Finset.mem_union,Finset.mem_image,Sum.inr.injEq,
      Sum.inl_ne_inr,and_false,exists_false,false_or,exists_eq_right] using Iff.of_eq h
end Oberwolfach
