module

public import Oberwolfach.UniformIntervalEndpointLoads
public import Oberwolfach.MarkedIntervalBoundaryIdentity

@[expose] public section
/-! Uniform marked-root multiplicity forces equal start and finish multiplicity. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_uniform_roots_give_endpoint_balance
    {V U:Type*} [Fintype V] [DecidableEq V] [Fintype U]
    {I:U→Type*} [∀w,Fintype (I w)]
    (π:Equiv.Perm V) (k:∀w,I w→ℕ) (a:∀w,I w→V)
    (hk:∀w j,0<k w j)
    (hinj:∀w j,Function.Injective (fun i:Fin (k w j+1)=>(π^i.val) (a w j)))
    (hdis:∀w (j l:I w),j≠l→Disjoint (permutationWindow π 0 (k w j) (a w j))
      (permutationWindow π 0 (k w l) (a w l)))
    (huniform:∀v z,(Finset.univ.filter (fun w=>v∈markedIntervalRootSet π (k w) (a w))).card=
      (Finset.univ.filter (fun w=>z∈markedIntervalRootSet π (k w) (a w))).card):
    ∀v,(Finset.univ.filter (fun w=>v∈Finset.univ.image (fun j=>(π^(k w j)) (a w j)))).card=
      (Finset.univ.filter (fun w=>v∈Finset.univ.image (a w))).card:=by
  apply uniform_root_load_endpoint_balance π
    (fun w=>markedIntervalRootSet π (k w) (a w))
    (fun w=>Finset.univ.image (fun j=>(π^(k w j)) (a w j)))
    (fun w=>Finset.univ.image (a w))
  · exact fun w=>marked_interval_boundary_identity π (k w) (a w) (hk w)
  · exact fun w=>marked_interval_roots_disjoint_endpoints π (k w) (a w) (hinj w) (hdis w)
  · exact fun w=>marked_shifted_roots_disjoint_starts π (k w) (a w) (hinj w) (hdis w)
  · exact huniform
end Oberwolfach
