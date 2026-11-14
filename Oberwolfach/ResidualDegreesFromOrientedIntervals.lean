module

public import Oberwolfach.ResidualDegreesFromUniformIntervals
public import Oberwolfach.InjectiveOrientedIncidence

@[expose] public section
/-! The oriented partial embeddings provide the single-incidence hypotheses in
the residual degree count, using the same original marked intervals. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residual_degrees_from_oriented_intervals
    {V U:Type*} [Fintype V] [DecidableEq V] [Fintype U]
    {I E:U→Type*} [∀w,Fintype (I w)] [∀w,Fintype (E w)]
    (π:Equiv.Perm V) (k:∀w,I w→ℕ) (a:∀w,I w→V)
    (hk:∀w j,0<k w j)
    (hinj:∀w j,Function.Injective (fun i:Fin (k w j+1)=>(π^i.val) (a w j)))
    (hdisIntervals:∀w (j l:I w),j≠l→Disjoint (permutationWindow π 0 (k w j) (a w j))
      (permutationWindow π 0 (k w l) (a w l)))
    (huniform:∀v z,(Finset.univ.filter (fun w=>v∈markedIntervalRootSet π (k w) (a w))).card=
      (Finset.univ.filter (fun w=>z∈markedIntervalRootSet π (k w) (a w))).card)
    (H:Finset (V×V)) (tail head:∀w,E w↪V) (Z:U→Finset V)
    (hZB:∀w,Disjoint (Z w) (Finset.univ.image (fun j=>(π^(k w j)) (a w j))))
    (hZT:∀w,Disjoint (Z w) (Finset.univ.image (a w)))
    (htail:∀w,Finset.univ.image (tail w)=Z w∪Finset.univ.image (fun j=>(π^(k w j)) (a w j)))
    (hhead:∀w,Finset.univ.image (head w)=Z w∪Finset.univ.image (a w))
    (hsub:∀w,Finset.univ.image (fun e=>(tail w e,head w e))⊆H)
    (hdis:∀w z,w≠z→Disjoint (Finset.univ.image (fun e=>(tail w e,head w e)))
      (Finset.univ.image (fun e=>(tail z e,head z e))))
    (hHout:∀v,(H.filter (fun e=>e.1=v)).card=Fintype.card U)
    (hHin:∀v,(H.filter (fun e=>e.2=v)).card=Fintype.card U):
    ∀v,(((H\Finset.univ.biUnion (fun w=>Finset.univ.image (fun e=>(tail w e,head w e)))).filter (fun e=>e.1=v)).card=
      (Finset.univ.filter (fun w=>v∉Z w∪Finset.univ.image (fun j=>(π^(k w j)) (a w j)))).card) ∧
      (((H\Finset.univ.biUnion (fun w=>Finset.univ.image (fun e=>(tail w e,head w e)))).filter (fun e=>e.2=v)).card=
      (Finset.univ.filter (fun w=>v∉Z w∪Finset.univ.image (fun j=>(π^(k w j)) (a w j)))).card):=by
  let D:U→Finset (V×V):=fun w=>Finset.univ.image (fun e=>(tail w e,head w e))
  have hout:∀w v,((D w).filter (fun e=>e.1=v)).card=
      if v∈Z w∪Finset.univ.image (fun j=>(π^(k w j)) (a w j)) then 1 else 0:=by
    intro w v
    simpa only [D,htail w] using (oriented_partial_embedding_incidence (tail w) (head w) v).1
  have hin:∀w v,((D w).filter (fun e=>e.2=v)).card=
      if v∈Z w∪Finset.univ.image (a w) then 1 else 0:=by
    intro w v
    simpa only [D,hhead w] using (oriented_partial_embedding_incidence (tail w) (head w) v).2
  exact residual_degrees_from_uniform_intervals π k a hk hinj hdisIntervals huniform H D Z
    hZB hZT hsub hdis hHout hHin hout hin
end Oberwolfach
