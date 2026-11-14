module

public import Oberwolfach.ResidualDegreesFromCanonicalArcs
public import Oberwolfach.BufferedCanonicalArcsFromDirectedComplement
public import Oberwolfach.BalancedOrientationArcDegrees
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

theorem residual_degrees_from_balanced_complement
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U]
    {I X:U→Type} [∀w,Fintype (I w)] [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
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
    (F:∀w,SimpleGraph (X w)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (e:∀w,∀C:(F w).ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (Dsrc:∀w,X w→X w→Prop) (horient:∀w x,Dsrc w x (factorCycleOrientation (F w) (e w) x))
    (hσ:∀w,(complementTailDomain (bufferedPathFullDomain (n w) (inner w))
      (bufferedFinalEndpoints (n w) (inner w))).image (factorCycleOrientation (F w) (e w))=
      complementTailDomain (bufferedPathFullDomain (n w) (inner w)) (bufferedInitialEndpoints (n w) (inner w)))
    (fC:∀w,{x // x∉bufferedPathStrictInterior (n w) (inner w)}↪V)
    (hstart:∀w i,fC w (bufferedInitialEndpointInComplement (n w) (ext w) (inner w) (hinner w) (hdisPaths w) i)=a w i)
    (hfinish:∀w i,fC w (bufferedEndpointInComplement (n w) (ext w) (inner w) (hinner w) (hdisPaths w) i)=(π^(k w i)) (a w i))
    (G:SimpleGraph V) (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if G.Adj x y then 1 else 0)
    (hbalance:∀v,(∑w,M v w)=Fintype.card U ∧ (∑w,M w v)=Fintype.card U)
    (hDir:∀w x y,(F w).Adj x.1 y.1→Dsrc w x.1 y.1→M (fC w x) (fC w y)=1)
    (hpack:∀w z,w≠z→Disjoint
      (((F w).induce {x | x∉bufferedPathStrictInterior (n w) (inner w)}).edgeFinset.image (Sym2.map (fC w)))
      (((F z).induce {x | x∉bufferedPathStrictInterior (n z) (inner z)}).edgeFinset.image (Sym2.map (fC z)))):
    let H:=orientationMatrixArcs M
    let tail:=fun w=>bufferedOrientedTailEmbedding (n w) (ext w) (inner w) (hinner w) (hdisPaths w) (fC w)
    let head:=fun w=>bufferedOrientedHeadEmbedding (n w) (ext w) (inner w) (hinner w) (hdisPaths w)
      (factorCycleOrientation (F w) (e w)) (hσ w) (fC w)
    ∀v,(((H\Finset.univ.biUnion (fun w=>Finset.univ.image (fun x=>(tail w x,head w x)))).filter (fun e=>e.1=v)).card=
      (Finset.univ.filter (fun w=>v∉outsideBufferedPathImage (n w) (inner w) (fC w) ∪
        Finset.univ.image (fun j=>(π^(k w j)) (a w j)))).card) ∧
      (((H\Finset.univ.biUnion (fun w=>Finset.univ.image (fun x=>(tail w x,head w x)))).filter (fun e=>e.2=v)).card=
      (Finset.univ.filter (fun w=>v∉outsideBufferedPathImage (n w) (inner w) (fC w) ∪
        Finset.univ.image (fun j=>(π^(k w j)) (a w j)))).card):=by
  intro H tail head
  have hsub:∀w,Finset.univ.image (fun x=>(tail w x,head w x))⊆H:=by
    intro w a ha
    obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp ha
    have hh:=buffered_canonical_arcs_from_directed_complement (F w) (hF w) (e w) (n w) (ext w) (inner w)
      (hinner w) (hdisPaths w) (hσ w) (fC w) (Dsrc w) (horient w) (fun x y=>M x y=1) (hDir w) z
    simpa [H,orientationMatrixArcs] using hh
  have hdis:=buffered_canonical_arcs_disjoint_from_complement_packing F hF e n ext inner hinner hdisPaths hσ fC hpack
  have hdegree:=balanced_orientation_arc_degrees G M hphysical
  have hout:∀v,(H.filter (fun a=>a.1=v)).card=Fintype.card U:=by
    intro v
    exact (hdegree v).1.trans (hbalance v).1
  have hin:∀v,(H.filter (fun a=>a.2=v)).card=Fintype.card U:=by
    intro v
    exact (hdegree v).2.trans (hbalance v).2
  exact residual_degrees_from_canonical_arcs π k a hk hinj hdisIntervals huniform n ext inner hinner hdisPaths
    (fun w=>factorCycleOrientation (F w) (e w)) hσ fC hstart hfinish H hsub hdis hout hin
end Oberwolfach
