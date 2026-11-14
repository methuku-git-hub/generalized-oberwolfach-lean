module

public import Oberwolfach.MarkedIntervalUniformEndpointBalance
public import Oberwolfach.ResidualEndpointLoadBalance

@[expose] public section
/-! Residual directed degrees from the original balanced interval family. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residual_degrees_from_uniform_intervals
    {V U:Type*} [Fintype V] [DecidableEq V] [Fintype U]
    {I:U→Type*} [∀w,Fintype (I w)]
    (π:Equiv.Perm V) (k:∀w,I w→ℕ) (a:∀w,I w→V)
    (hk:∀w j,0<k w j)
    (hinj:∀w j,Function.Injective (fun i:Fin (k w j+1)=>(π^i.val) (a w j)))
    (hdisIntervals:∀w (j l:I w),j≠l→Disjoint (permutationWindow π 0 (k w j) (a w j))
      (permutationWindow π 0 (k w l) (a w l)))
    (huniform:∀v z,(Finset.univ.filter (fun w=>v∈markedIntervalRootSet π (k w) (a w))).card=
      (Finset.univ.filter (fun w=>z∈markedIntervalRootSet π (k w) (a w))).card)
    (H:Finset (V×V)) (D:U→Finset (V×V)) (Z:U→Finset V)
    (hZB:∀w,Disjoint (Z w) (Finset.univ.image (fun j=>(π^(k w j)) (a w j))))
    (hZT:∀w,Disjoint (Z w) (Finset.univ.image (a w)))
    (hsub:∀w,D w⊆H)
    (hdis:∀w z,w≠z→Disjoint (D w) (D z))
    (hHout:∀v,(H.filter (fun e=>e.1=v)).card=Fintype.card U)
    (hHin:∀v,(H.filter (fun e=>e.2=v)).card=Fintype.card U)
    (hout:∀w v,((D w).filter (fun e=>e.1=v)).card=
      if v∈Z w∪Finset.univ.image (fun j=>(π^(k w j)) (a w j)) then 1 else 0)
    (hin:∀w v,((D w).filter (fun e=>e.2=v)).card=
      if v∈Z w∪Finset.univ.image (a w) then 1 else 0):
    ∀v,(((H\Finset.univ.biUnion D).filter (fun e=>e.1=v)).card=
      (Finset.univ.filter (fun w=>v∉Z w∪Finset.univ.image (fun j=>(π^(k w j)) (a w j)))).card) ∧
      (((H\Finset.univ.biUnion D).filter (fun e=>e.2=v)).card=
      (Finset.univ.filter (fun w=>v∉Z w∪Finset.univ.image (fun j=>(π^(k w j)) (a w j)))).card):=by
  let B:U→Finset V:=fun w=>Finset.univ.image (fun j=>(π^(k w j)) (a w j))
  let T:U→Finset V:=fun w=>Finset.univ.image (a w)
  have hBT:∀v,(Finset.univ.filter (fun w=>v∈B w)).card=(Finset.univ.filter (fun w=>v∈T w)).card:=
    marked_uniform_roots_give_endpoint_balance π k a hk hinj hdisIntervals huniform
  have hbalance:=residual_missing_load_balance Z B T hZB hZT hBT
  exact residual_directed_degree_balance H D Z B T hsub hdis hHout hHin hout hin hbalance
end Oberwolfach
