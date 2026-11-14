module

public import Oberwolfach.TransformerEndpointAssignments
public import Oberwolfach.CanonicalGraphPairs
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-! Each endpoint contribution in an edge-wheel sum occurs exactly once
in the vertex-indexed sum. This includes the chosen orientation of each
physical undirected edge; no orientation is independently chosen per wheel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V:Type} [Fintype V] [DecidableEq V]

 theorem canonical_edge_endpoint_sum (G:SimpleGraph V) (f:Sym2 V→V→ℤ):
    (∑ e∈G.edgeFinset,(f e e.out.1+f e e.out.2))=
      ∑ v,∑ w:G.neighborSet v,f s(v,w.val) v:=by
  let E:(Σ v,G.neighborSet v)≃G.Dart:=
    { toFun:=fun p=>⟨(p.1,p.2.val),p.2.property⟩
      invFun:=fun d=>⟨d.fst,⟨d.snd,d.adj⟩⟩
      left_inv:=by intro p;cases p;rfl
      right_inv:=by intro d;cases d;rfl }
  have hs:(∑ d:G.Dart,f d.edge d.fst)=∑ v,∑ w:G.neighborSet v,f s(v,w.val) v:=by
    rw [←E.sum_comp (fun d=>f d.edge d.fst),Fintype.sum_sigma]
    rfl
  rw [←hs]
  have hf:=Finset.sum_fiberwise_of_maps_to (s:=Finset.univ) (t:=G.edgeFinset)
    (g:=SimpleGraph.Dart.edge) (fun d _=>by rw [SimpleGraph.mem_edgeFinset];exact d.edge_mem)
    (fun d=>f d.edge d.fst)
  rw [←hf]
  apply Finset.sum_congr rfl
  intro e he
  have heq:s(e.out.1,e.out.2)=e:=by rw [Sym2.mk];exact e.out_eq
  have hadj:G.Adj e.out.1 e.out.2:=SimpleGraph.mem_edgeFinset.mp (heq.symm ▸ he)
  let d:G.Dart:=⟨(e.out.1,e.out.2),hadj⟩
  have hde:d.edge=e:=heq
  have hfilter:(Finset.univ.filter (fun a:G.Dart=>a.edge=e))={d,d.symm}:=by
    rw [←hde];exact d.edge_fiber
  rw [hfilter,Finset.sum_pair (Ne.symm d.symm_ne)]
  simp only [SimpleGraph.Dart.edge_symm,hde]
  rfl

 theorem canonical_edge_endpoint_sum_subtype (G:SimpleGraph V) (f:(e:G.edgeFinset)→V→ℤ):
    (∑ e:G.edgeFinset,(f e e.val.out.1+f e e.val.out.2))=
      ∑ v,∑ w:G.neighborSet v,f ⟨s(v,w.val),SimpleGraph.mem_edgeFinset.mpr w.property⟩ v:=by
  let f':Sym2 V→V→ℤ:=fun e v=>if he:e∈G.edgeFinset then f ⟨e,he⟩ v else 0
  have hh:=canonical_edge_endpoint_sum G f'
  have hleft:(∑ e:G.edgeFinset,(f e e.val.out.1+f e e.val.out.2))=
      ∑ e∈G.edgeFinset,(f' e e.out.1+f' e e.out.2):=by
    calc
      _ = ∑ e:G.edgeFinset,(f' e.val e.val.out.1+f' e.val e.val.out.2):=by
        apply Finset.sum_congr rfl
        intro e _
        simp only [f',dite_eq_left e.property]
      _ = _:=by simpa only [] using (Finset.sum_coe_sort G.edgeFinset (fun e=>f' e e.out.1+f' e e.out.2))
  rw [hleft,hh]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  have hw:s(v,w.val)∈G.edgeFinset:=SimpleGraph.mem_edgeFinset.mpr w.property
  simp only [f',dite_eq_left hw]

end Oberwolfach
