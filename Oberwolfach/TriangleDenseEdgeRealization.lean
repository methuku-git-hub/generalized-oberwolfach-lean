module

public import Oberwolfach.TriangleDenseGeometry
public import Oberwolfach.TriangleTransformerEdgeRealization

@[expose] public section
/-! Derive the four-root and nine-root choices for the initial triangle
transformer stage from minimum degree and near-complete spokes. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem triangle_transformer_dense_edge_realization
    (G Q:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U)
    (R W:Finset V) (B:Finset U) (β ε:ℝ) (hβ:0<β) (hε:0≤ε) (hεβ:ε≤β)
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hcross:∀ v∈G.support,∀ w∈G.support,φ v≠w)
    (hQ:G≤Q) (hφQ:∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))
    (hφedge:Function.Injective (fun e:G.edgeFinset=>s(φ e.val.out.1,φ e.val.out.2)))
    (hψedge:Function.Injective (fun e:{e:V×U // H₀ e.1 e.2}=>(φ e.val.1,ψ e.val.2)))
    (hH:∀ v u,H₀ v u→H v u∧H (φ v) (ψ u))
    (hdeg:∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(Q.degree v:ℝ))
    (hnearV:∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ε*(Fintype.card V:ℝ))
    (hnearU:∀ v,(((Finset.univ:Finset U).filter (fun u=>¬H v u)).card:ℝ)≤ε*(Fintype.card U:ℝ))
    (hbudget:((W.card+R.card+G.edgeFinset.card+2*Fintype.card {e:V×U // H₀ e.1 e.2}+1:ℕ):ℝ)
      <2*β*(Fintype.card V:ℝ))
    (hbudgetU:((B.card+G.edgeFinset.card:ℕ):ℝ)<(1-9*ε)*(Fintype.card U:ℝ)):
    Nonempty (TriangleTransformerEdgeData G Q ⊥ H₀ H φ ψ Finset.univ R W B):=by
  apply triangular_transformer_edge_realization G Q ⊥ H₀ H φ ψ Finset.univ R W B
    hbalance hroot hcross hQ hφQ hφedge hψedge hH
    (by intro v w hv a ha c hc;simp)
    0 (2*β*(Fintype.card V:ℝ)) ((1-9*ε)*(Fintype.card U:ℝ)) (by norm_num)
    (by intro v;simp)
  · intro w x y z
    have hh:=triangle_four_graph_neighbours Q β hdeg w x y z
    have hn:0≤(Fintype.card V:ℝ):=by positivity
    have hb:0≤β:=hβ.le
    simpa only [Finset.mem_univ,true_and] using (show 2*β*(Fintype.card V:ℝ)≤_ by nlinarith)
  · intro u u' w x y z
    simpa only [Finset.mem_univ,true_and] using triangle_four_neighbours_two_hubs Q H β ε hεβ hdeg hnearV u u' w x y z
  · push_cast at hbudget
    linarith
  · intro T hT _
    exact triangle_common_hub_neighbours H ε hε hnearU T hT
  · exact_mod_cast hbudgetU
end Oberwolfach
