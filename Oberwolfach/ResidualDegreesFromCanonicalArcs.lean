module

public import Oberwolfach.ResidualDegreesFromBufferedIntervals
public import Oberwolfach.BufferedCanonicalOrientedArcs

@[expose] public section
/-! Exact residual degrees from the canonical mapped source arcs; tail and
head image identities are proved internally. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residual_degrees_from_canonical_arcs
    {V U:Type*} [Fintype V] [DecidableEq V] [Fintype U]
    {I X:U→Type*} [∀w,Fintype (I w)] [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
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
    (σ:∀w,Equiv.Perm (X w))
    (hσ:∀w,(complementTailDomain (bufferedPathFullDomain (n w) (inner w))
      (bufferedFinalEndpoints (n w) (inner w))).image (σ w)=
      complementTailDomain (bufferedPathFullDomain (n w) (inner w)) (bufferedInitialEndpoints (n w) (inner w)))
    (fC:∀w,{x // x∉bufferedPathStrictInterior (n w) (inner w)}↪V)
    (hstart:∀w i,fC w (bufferedInitialEndpointInComplement (n w) (ext w) (inner w) (hinner w) (hdisPaths w) i)=a w i)
    (hfinish:∀w i,fC w (bufferedEndpointInComplement (n w) (ext w) (inner w) (hinner w) (hdisPaths w) i)=(π^(k w i)) (a w i))
    (H:Finset (V×V)):
    let tail:=fun w=>bufferedOrientedTailEmbedding (n w) (ext w) (inner w) (hinner w) (hdisPaths w) (fC w)
    let head:=fun w=>bufferedOrientedHeadEmbedding (n w) (ext w) (inner w) (hinner w) (hdisPaths w) (σ w) (hσ w) (fC w)
    (∀w,Finset.univ.image (fun x=>(tail w x,head w x))⊆H)→
    (∀w z,w≠z→Disjoint (Finset.univ.image (fun x=>(tail w x,head w x)))
      (Finset.univ.image (fun x=>(tail z x,head z x))))→
    (∀v,(H.filter (fun e=>e.1=v)).card=Fintype.card U)→
    (∀v,(H.filter (fun e=>e.2=v)).card=Fintype.card U)→
    ∀v,(((H\Finset.univ.biUnion (fun w=>Finset.univ.image (fun x=>(tail w x,head w x)))).filter (fun e=>e.1=v)).card=
      (Finset.univ.filter (fun w=>v∉outsideBufferedPathImage (n w) (inner w) (fC w) ∪
        Finset.univ.image (fun j=>(π^(k w j)) (a w j)))).card) ∧
      (((H\Finset.univ.biUnion (fun w=>Finset.univ.image (fun x=>(tail w x,head w x)))).filter (fun e=>e.2=v)).card=
      (Finset.univ.filter (fun w=>v∉outsideBufferedPathImage (n w) (inner w) (fC w) ∪
        Finset.univ.image (fun j=>(π^(k w j)) (a w j)))).card):=by
  intro tail head hsub hdis hHout hHin
  have htail:∀w,Finset.univ.image (tail w)=outsideBufferedPathImage (n w) (inner w) (fC w)∪
      Finset.univ.image (fun j=>(π^(k w j)) (a w j)):=by
    intro w
    exact (buffered_canonical_oriented_arc_images (n w) (ext w) (inner w) (hinner w) (hdisPaths w)
      (σ w) (hσ w) (fC w) (a w) (fun j=>(π^(k w j)) (a w j)) (hstart w) (hfinish w)).1
  have hhead:∀w,Finset.univ.image (head w)=outsideBufferedPathImage (n w) (inner w) (fC w)∪Finset.univ.image (a w):=by
    intro w
    exact (buffered_canonical_oriented_arc_images (n w) (ext w) (inner w) (hinner w) (hdisPaths w)
      (σ w) (hσ w) (fC w) (a w) (fun j=>(π^(k w j)) (a w j)) (hstart w) (hfinish w)).2
  exact residual_degrees_from_buffered_intervals π k a hk hinj hdisIntervals huniform n ext inner hinner hdisPaths fC
    hstart hfinish H tail head htail hhead hsub hdis hHout hHin
end Oberwolfach
