module

public import Oberwolfach.ResidualDegreesFromOrientedIntervals
public import Oberwolfach.BufferedEndpointImagesAvoidOutside

@[expose] public section
/-! Exact directed degrees from the original uniform interval family and the
same injective complement maps used for buffered factor reconstruction. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residual_degrees_from_buffered_intervals
    {V U:Type*} [Fintype V] [DecidableEq V] [Fintype U]
    {I X E:U→Type*} [∀w,Fintype (I w)] [∀w,Fintype (X w)]
    [∀w,DecidableEq (X w)] [∀w,Fintype (E w)]
    (π:Equiv.Perm V) (k:∀w,I w→ℕ) (a:∀w,I w→V)
    (hk:∀w j,0<k w j)
    (hinj:∀w j,Function.Injective (fun i:Fin (k w j+1)=>(π^i.val) (a w j)))
    (hdisIntervals:∀w (j l:I w),j≠l→Disjoint (permutationWindow π 0 (k w j) (a w j))
      (permutationWindow π 0 (k w l) (a w l)))
    (huniform:∀v z,(Finset.univ.filter (fun w=>v∈markedIntervalRootSet π (k w) (a w))).card=
      (Finset.univ.filter (fun w=>z∈markedIntervalRootSet π (k w) (a w))).card)
    (n:∀w,I w→ℕ) (ext:∀w i,Fin (n w i+5)↪X w) (inner:∀w i,Fin (n w i+1)↪X w)
    (hinner:∀w i p,inner w i p=ext w i ⟨p.val+2,by omega⟩)
    (hdisPaths:∀w i j,i≠j→Disjoint (Finset.univ.image (ext w i)) (Finset.univ.image (ext w j)))
    (fC:∀w,{x // x∉bufferedPathStrictInterior (n w) (inner w)}↪V)
    (hstart:∀w i,fC w (bufferedInitialEndpointInComplement (n w) (ext w) (inner w) (hinner w) (hdisPaths w) i)=a w i)
    (hfinish:∀w i,fC w (bufferedEndpointInComplement (n w) (ext w) (inner w) (hinner w) (hdisPaths w) i)=(π^(k w i)) (a w i))
    (H:Finset (V×V)) (tail head:∀w,E w↪V)
    (htail:∀w,Finset.univ.image (tail w)=outsideBufferedPathImage (n w) (inner w) (fC w) ∪
      Finset.univ.image (fun j=>(π^(k w j)) (a w j)))
    (hhead:∀w,Finset.univ.image (head w)=outsideBufferedPathImage (n w) (inner w) (fC w) ∪ Finset.univ.image (a w))
    (hsub:∀w,Finset.univ.image (fun e=>(tail w e,head w e))⊆H)
    (hdis:∀w z,w≠z→Disjoint (Finset.univ.image (fun e=>(tail w e,head w e)))
      (Finset.univ.image (fun e=>(tail z e,head z e))))
    (hHout:∀v,(H.filter (fun e=>e.1=v)).card=Fintype.card U)
    (hHin:∀v,(H.filter (fun e=>e.2=v)).card=Fintype.card U):
    ∀v,(((H\Finset.univ.biUnion (fun w=>Finset.univ.image (fun e=>(tail w e,head w e)))).filter (fun e=>e.1=v)).card=
      (Finset.univ.filter (fun w=>v∉outsideBufferedPathImage (n w) (inner w) (fC w) ∪
        Finset.univ.image (fun j=>(π^(k w j)) (a w j)))).card) ∧
      (((H\Finset.univ.biUnion (fun w=>Finset.univ.image (fun e=>(tail w e,head w e)))).filter (fun e=>e.2=v)).card=
      (Finset.univ.filter (fun w=>v∉outsideBufferedPathImage (n w) (inner w) (fC w) ∪
        Finset.univ.image (fun j=>(π^(k w j)) (a w j)))).card):=by
  let Z:U→Finset V:=fun w=>outsideBufferedPathImage (n w) (inner w) (fC w)
  have havoid:∀w,Disjoint (Z w) (Finset.univ.image (a w)) ∧
      Disjoint (Z w) (Finset.univ.image (fun j=>(π^(k w j)) (a w j))):=by
    intro w
    exact buffered_outside_image_avoids_both_endpoints (n w) (ext w) (inner w) (hinner w) (hdisPaths w)
      (fC w) (a w) (fun j=>(π^(k w j)) (a w j)) (hstart w) (hfinish w)
  exact residual_degrees_from_oriented_intervals π k a hk hinj hdisIntervals huniform H tail head Z
    (fun w=>(havoid w).2) (fun w=>(havoid w).1) htail hhead hsub hdis hHout hHin
end Oberwolfach
