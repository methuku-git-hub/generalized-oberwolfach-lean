module

public import Oberwolfach.BoundaryLabelCoordinates

@[expose] public section

/-! A crossing directed edge has exactly one outside owner and one inside
label. The number of directed edge types bounds every owner/label fibre;
no independence or injectivity of the untyped endpoint union is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A W T:Type*} [Fintype A] [Fintype W] [Fintype T]
  [DecidableEq A] [DecidableEq W] [DecidableEq T]

def DirectedBoundaryEdge (tail head:A→W) (X:Finset W):Type _ :=
  {a:A // (tail a∉X∧head a∈X)∨(tail a∈X∧head a∉X)}

instance (tail head:A→W) (X:Finset W):Fintype (DirectedBoundaryEdge tail head X):=
  inferInstanceAs (Fintype {a:A // (tail a∉X∧head a∈X)∨(tail a∈X∧head a∉X)})
instance (tail head:A→W) (X:Finset W):DecidableEq (DirectedBoundaryEdge tail head X):=
  inferInstanceAs (DecidableEq {a:A // (tail a∉X∧head a∈X)∨(tail a∈X∧head a∉X)})

def boundaryOutside (tail head:A→W) (X:Finset W) (a:DirectedBoundaryEdge tail head X):W :=
  if tail a.val∈X then head a.val else tail a.val
def boundaryInside (tail head:A→W) (X:Finset W) (a:DirectedBoundaryEdge tail head X):W :=
  if tail a.val∈X then tail a.val else head a.val

theorem boundaryOutside_notMem (tail head:A→W) (X:Finset W) (a:DirectedBoundaryEdge tail head X):
    boundaryOutside tail head X a∉X := by
  rcases a.property with h|h <;> simp only [boundaryOutside,h.1,ite_false,ite_true] <;> tauto

theorem boundaryInside_mem (tail head:A→W) (X:Finset W) (a:DirectedBoundaryEdge tail head X):
    boundaryInside tail head X a∈X := by
  rcases a.property with h|h <;> simp only [boundaryInside,h.1,ite_false,ite_true] <;> tauto

theorem boundary_ordered_endpoints (tail head:A→W) (X:Finset W)
    (a:DirectedBoundaryEdge tail head X):
    tail a.val=(if tail a.val∈X then boundaryInside tail head X a else boundaryOutside tail head X a)∧
    head a.val=(if tail a.val∈X then boundaryOutside tail head X a else boundaryInside tail head X a) := by
  by_cases h:tail a.val∈X <;> simp [boundaryOutside,boundaryInside,h]

theorem boundary_owner_label_fibre (tail head:A→W) (kind:A→T) (X:Finset W)
    (hinj:Function.Injective (fun a=>(kind a,tail a,head a))) (x y:W):
    (Finset.univ.filter (fun a:DirectedBoundaryEdge tail head X=>
      boundaryOutside tail head X a=x∧boundaryInside tail head X a=y)).card≤2*Fintype.card T := by
  let F:=Finset.univ.filter (fun a:DirectedBoundaryEdge tail head X=>
      boundaryOutside tail head X a=x∧boundaryInside tail head X a=y)
  let f:F→Bool×T:=fun a=>(decide (tail a.val.val∈X),kind a.val.val)
  have hf:Function.Injective f := by
    intro a b hab
    have ht:kind a.val.val=kind b.val.val:=congrArg Prod.snd hab
    have hd:decide (tail a.val.val∈X)=decide (tail b.val.val∈X):=congrArg Prod.fst hab
    have hm:(tail a.val.val∈X)↔(tail b.val.val∈X):=by
      simpa only [decide_eq_decide] using hd
    have ha:boundaryOutside tail head X a.val=x∧boundaryInside tail head X a.val=y:=
      (Finset.mem_filter.mp a.property).2
    have hb:boundaryOutside tail head X b.val=x∧boundaryInside tail head X b.val=y:=
      (Finset.mem_filter.mp b.property).2
    apply Subtype.ext
    apply Subtype.ext
    apply hinj
    have ea:=boundary_ordered_endpoints tail head X a.val
    have eb:=boundary_ordered_endpoints tail head X b.val
    rw [ha.1,ha.2] at ea
    rw [hb.1,hb.2] at eb
    by_cases h:tail a.val.val∈X
    · have h':tail b.val.val∈X:=hm.mp h
      simp only [h,h',ite_true] at ea eb
      exact Prod.ext ht (Prod.ext (ea.1.trans eb.1.symm) (ea.2.trans eb.2.symm))
    · have h':tail b.val.val∉X:=fun hb=>h (hm.mpr hb)
      simp only [h,h',ite_false] at ea eb
      exact Prod.ext ht (Prod.ext (ea.1.trans eb.1.symm) (ea.2.trans eb.2.symm))
  have hh:=Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_bool,F] using hh

end Oberwolfach
