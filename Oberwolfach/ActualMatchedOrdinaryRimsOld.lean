module

public import Oberwolfach.OrdinaryWheelPathEdgeSaturation
public import Oberwolfach.ActualCycleEdgesOld
public import Oberwolfach.WalkEdgeImagesExact

@[expose] public section
/-! The matched ordinary wheel's complete rim, including the closing edge,
is contained in the same actual old physical edge image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_matched_ordinary_rims_old
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F) (j:{j // j∈data.t})
    (n:ℕ) (hn:2≤n) (f:Fin (n+1)↪V) (H:SimpleGraph V)
    (q:H.Walk (f (cycleNext 0)) (f 0)) (hq:q.IsPath) (hlen:q.length=n)
    (hcover:∀e∈q.edges,∃i:Fin (n+1),e=s(f i,f (cycleNext i)))
    (ψ:X→V) (hlenSource:q.length=(data.C j.val).tail.length)
    (hmap:∀k,k≤(data.C j.val).tail.length→ψ ((data.C j.val).tail.getVert k)=q.getVert k)
    (hfirst:ψ ((data.C j.val).snd)=f (cycleNext 0)) (hlast:ψ (data.root j.val)=f 0):
    ∀i:Fin (n+1),s(f i,f (cycleNext i))∈
      (data.deletedEdges\(Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))).image (Sym2.map ψ):=by
  let Old:=(data.deletedEdges\(Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))).image (Sym2.map ψ)
  have htail:(data.C j.val).tail.edges.toFinset⊆(data.C j.val).edges.toFinset:=by
    intro e he
    apply List.mem_toFinset.mpr
    have ht:=List.mem_toFinset.mp he
    rw [SimpleGraph.Walk.edges_tail] at ht
    exact List.mem_of_mem_tail ht
  have hqOld:q.edges.toFinset⊆Old:=by
    have h:=walk_edge_images_exact F H (data.C j.val).tail q ψ hlenSource hmap
    rw [←h]
    exact Finset.image_subset_image (htail.trans (actual_cycle_edges_old data j))
  have hclose: s(f 0,f (cycleNext 0))∈Old:=by
    have hn0:¬(data.C j.val).Nil:=by
      intro h
      have hlen0:=(data.hcycle j.val j.property).isCircuit.three_le_length
      have hh:=h.length_eq_zero
      omega
    have he:s(data.root j.val,(data.C j.val).snd)∈(data.C j.val).edges.toFinset:=
      List.mem_toFinset.mpr ((data.C j.val).mk_start_snd_mem_edges hn0)
    have he':s(ψ (data.root j.val),ψ ((data.C j.val).snd))∈Old:=by
      exact Finset.mem_image.mpr ⟨s(data.root j.val,(data.C j.val).snd),actual_cycle_edges_old data j he,rfl⟩
    simpa only [hlast,hfirst] using he'
  intro i
  have hsat:=ordinary_wheel_path_edge_saturation n hn f H q hq hlen hcover
  have hi:s(f i,f (cycleNext i))∈Finset.univ.image (fun i:Fin (n+1)=>s(f i,f (cycleNext i))):=Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  rw [hsat] at hi
  rcases Finset.mem_insert.mp hi with hi|hi
  · exact hi ▸ hclose
  · exact hqOld hi
end Oberwolfach
