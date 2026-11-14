module

public import Oberwolfach.FractionalCycleIncidence
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-! Weighted incidence sums count each physical undirected edge twice.
This identity keeps unordered endpoint-edge weights from being doubled. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem weighted_graph_handshake (G : SimpleGraph V) (weight : Sym2 V→ℝ) :
    (∑ v,∑ w,if G.Adj v w then weight s(v,w) else 0)=2*∑ e∈G.edgeFinset,weight e := by
  let e : (Σ v,G.neighborSet v)≃G.Dart :=
    { toFun := fun p=>⟨(p.1,p.2.val),p.2.property⟩
      invFun := fun d=>⟨d.fst,⟨d.snd,d.adj⟩⟩
      left_inv := by intro p;cases p;rfl
      right_inv := by intro d;cases d;rfl }
  have hrow (v : V) : (∑ w:G.neighborSet v,weight s(v,w.val))=
      ∑ w,if G.Adj v w then weight s(v,w) else 0 := by
    have hh:=Finset.sum_subtype (F:=inferInstance) (p:=fun w=>G.Adj v w)
      (G.neighborFinset v) (fun w=>by simp) (fun w=>weight s(v,w))
    have hx : (∑ w:G.neighborSet v,weight s(v,w.val))=∑ w∈G.neighborFinset v,weight s(v,w) := by
      convert hh.symm using 1 <;> congr!
    rw [hx,SimpleGraph.neighborFinset_eq_filter,Finset.sum_filter]
  have hdarts : (∑ v,∑ w,if G.Adj v w then weight s(v,w) else 0)=
      ∑ d:G.Dart,weight d.edge := by
    rw [←e.sum_comp (fun d=>weight d.edge),Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro v hv
    exact (hrow v).symm
  rw [hdarts]
  have hf:=Finset.sum_fiberwise_of_maps_to (s:=Finset.univ) (t:=G.edgeFinset)
    (g:=SimpleGraph.Dart.edge) (fun d _=>by rw [SimpleGraph.mem_edgeFinset];exact d.edge_mem) (fun d=>weight d.edge)
  rw [←hf,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro edge hedge
  have hsum : (∑ d:G.Dart with d.edge=edge,weight d.edge)=
      (Finset.univ.filter (fun d:G.Dart=>d.edge=edge)).card*weight edge := by
    calc
      _ = ∑ _d:G.Dart with _d.edge=edge,weight edge := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [(Finset.mem_filter.mp hd).2]
      _ = _ := by simp
  rw [hsum,G.dart_edge_fiber_card edge (by simpa using hedge)]
  norm_num

end Oberwolfach
