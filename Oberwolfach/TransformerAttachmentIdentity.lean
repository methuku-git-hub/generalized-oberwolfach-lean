module

public import Oberwolfach.TransformerIncidenceSums

@[expose] public section

/-! Exact cancellation of the rim and spoke attachment terms of the
ordinary transformer. The endpoint bijection and hub permutation are the
ones supplied by the degree balance. Every term has coefficient one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem transformer_attachment_identity (G:SimpleGraph V) (H:V→U→Prop)
    (b:∀ v,G.neighborSet v≃({u:U // H v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v))
    (a:(e:G.edgeFinset)→V→V) (z:∀ v,{u:U // H v u}→Fin 2→V)
    (hub:G.edgeFinset→U) (rim:V→V→ℤ) (spoke:V→U→ℤ)
    (core:G.edgeFinset→ℤ) (cross:∀ v,{u:U // H v u}→ℤ)
    (load:∀ v,{u:U // H v u}→ℤ):
    (∑ e:G.edgeFinset,(core e+rim e.val.out.1 (a e e.val.out.1)+rim e.val.out.2 (a e e.val.out.2)+
      spoke e.val.out.1 (hub e)+spoke e.val.out.2 (hub e)))+
    (∑ v,∑ u:{u:U // H v u},(cross v u+(∑ i:Fin 2,rim v (z v u i))+load v u))-
    (∑ v,∑ w:G.neighborSet v,
      (rim v (a ⟨s(v,w.val),SimpleGraph.mem_edgeFinset.mpr w.property⟩ v)+
       rim v (z v (b v w).1 (b v w).2)+
       spoke v (hub ⟨s(v,(σ v w).val),SimpleGraph.mem_edgeFinset.mpr (σ v w).property⟩)))=
    (∑ e:G.edgeFinset,core e)+(∑ v,∑ u:{u:U // H v u},cross v u)+
      (∑ v,∑ u:{u:U // H v u},load v u):=by
  have hr:=canonical_edge_endpoint_sum_subtype G (fun e v=>rim v (a e v))
  have hs:=canonical_edge_endpoint_sum_subtype G (fun e v=>spoke v (hub e))
  have hz (v:V):(∑ w:G.neighborSet v,rim v (z v (b v w).1 (b v w).2))=
      ∑ u:{u:U // H v u},∑ i:Fin 2,rim v (z v u i):=by
    exact transformer_endpoint_sum G H (b v) (fun ui=>rim v (z v ui.1 ui.2))
  have hp (v:V):(∑ w:G.neighborSet v,
      spoke v (hub ⟨s(v,(σ v w).val),SimpleGraph.mem_edgeFinset.mpr (σ v w).property⟩))=
      ∑ w:G.neighborSet v,spoke v (hub ⟨s(v,w.val),SimpleGraph.mem_edgeFinset.mpr w.property⟩):=by
    exact Equiv.sum_comp (σ v) (fun w=>spoke v (hub ⟨s(v,w.val),SimpleGraph.mem_edgeFinset.mpr w.property⟩))
  simp_rw [Finset.sum_add_distrib] at hr hs ⊢
  simp_rw [hz,hp]
  rw [←hr,←hs]
  abel

end Oberwolfach
