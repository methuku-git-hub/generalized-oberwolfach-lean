module

public import Oberwolfach.CycleEdgeEnumeration
public import Oberwolfach.ActualMatchedPieceDirectedArcs

@[expose] public section
/-! A simple path of length one less than an embedded cycle, using only its
cycle edges and closed by the missing edge, uses the whole rim. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_wheel_path_edge_saturation
    {V:Type} [DecidableEq V] (n:ℕ) (hn:2≤n) (f:Fin (n+1)↪V)
    (G:SimpleGraph V) (q:G.Walk (f (cycleNext 0)) (f 0)) (hq:q.IsPath) (hlen:q.length=n)
    (hcover:∀e∈q.edges,∃i:Fin (n+1),e=s(f i,f (cycleNext i))):
    Finset.univ.image (fun i:Fin (n+1)=>s(f i,f (cycleNext i)))=
      insert s(f 0,f (cycleNext 0)) q.edges.toFinset:=by
  let closing:=s(f 0,f (cycleNext 0))
  have hnot:closing∉q.edges.toFinset:=by
    intro he
    obtain ⟨k,hk,hkedge⟩:=(q.mk_mem_edges_iff_exists).mp (List.mem_toFinset.mp he)
    rcases Sym2.eq_iff.mp hkedge with ⟨ha,hb⟩|⟨ha,hb⟩
    · have hk1:k=q.length:=by
        apply hq.getVert_injOn (by simp;omega) (by simp)
        simpa only [SimpleGraph.Walk.getVert_length] using ha
      have hk2:k+1=0:=by
        apply hq.getVert_injOn (by simp;omega) (by simp)
        simpa only [SimpleGraph.Walk.getVert_zero] using hb
      omega
    · have hk1:k=0:=by
        apply hq.getVert_injOn (by simp;omega) (by simp)
        simpa only [SimpleGraph.Walk.getVert_zero] using ha
      have hk2:k+1=q.length:=by
        apply hq.getVert_injOn (by simp;omega) (by simp)
        simpa only [SimpleGraph.Walk.getVert_length] using hb
      omega
  have hsub:insert closing q.edges.toFinset⊆Finset.univ.image (fun i:Fin (n+1)=>s(f i,f (cycleNext i))):=by
    intro e he
    rcases Finset.mem_insert.mp he with rfl|he
    · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
    · obtain ⟨i,hi⟩:=hcover e (List.mem_toFinset.mp he)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi.symm⟩
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_image_of_injective _ (cycle_edge_injective (by omega) f),Finset.card_univ,Fintype.card_fin,
    Finset.card_insert_of_notMem hnot,List.toFinset_card_of_nodup hq.isTrail.edges_nodup,SimpleGraph.Walk.length_edges,hlen]
end Oberwolfach
