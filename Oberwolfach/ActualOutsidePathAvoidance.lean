module

public import Oberwolfach.ResidualActualData
public import Oberwolfach.BufferedComplementImage

@[expose] public section
/-! Avoid reserved labels on the complement of the final paths only. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_outside_buffered_path_image_avoids_reserved
    {X V I K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype I]
    [DecidableEq K] [DecidableEq J] (F:SimpleGraph X)
    (data:ActualResidualData (K:=K) (J:=J) F)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (fC:{x // x∉bufferedPathStrictInterior n inner}↪V)
    (ψ:X→V) (Φ g:{x // x∈data.remaining}→V)
    (Anchors:Finset {x // x∈data.remaining}) (Lists Y:Finset V)
    (hold:∀(x:{x // x∉bufferedPathStrictInterior n inner}),
      x.val∈data.oldDomain→fC x=ψ x.val)
    (hnew:∀(x:{x // x∉bufferedPathStrictInterior n inner}) (hx:x.val∈data.remaining),
      fC x=Φ ⟨x.val,hx⟩)
    (hAnchor:∀x∈Anchors,Φ x=g x)
    (hFree:∀x,x∉Anchors→Φ x∈Lists)
    (hOldAvoid:∀x,x∈data.oldDomain→x∉bufferedPathFullDomain n inner→ψ x∉Y)
    (hAnchorAvoid:∀x∈Anchors,x.val∉bufferedPathFullDomain n inner → g x∉Y)
    (hListAvoid:Disjoint Lists Y):
    Disjoint (outsideBufferedPathImage n inner fC) Y:=by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hvY
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
  have hxA:x.val∉bufferedPathFullDomain n inner:=(Finset.mem_filter.mp hx).2
  have hcover:x.val∈data.oldDomain ∨ x.val∈data.remaining:=by
    have hh:x.val∈data.oldDomain∪data.remaining:=by rw [data.old_domain_union_remaining hCycle];exact Finset.mem_univ _
    exact Finset.mem_union.mp hh
  rcases hcover with hxold | hxnew
  · rw [hold x hxold] at hvY
    exact hOldAvoid x.val hxold hxA hvY
  · let z:{x // x∈data.remaining}:=⟨x.val,hxnew⟩
    have heq:fC x=Φ z:=hnew x hxnew
    by_cases hz:z∈Anchors
    · rw [heq,hAnchor z hz] at hvY
      exact hAnchorAvoid z hz hxA hvY
    · have hL:Φ z∈Lists:=hFree z hz
      rw [heq] at hvY
      exact Finset.disjoint_left.mp hListAvoid hL hvY
end Oberwolfach
