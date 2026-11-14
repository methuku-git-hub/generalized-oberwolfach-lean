module

public import Oberwolfach.ActualOldPhysicalCoverage

@[expose] public section
/-! The old deleted edges are exactly the matched cycles and deleted paths.
Removing the final paths leaves only cycles and selected runs, so physical
coverage transports directly to the symmetric edge images. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_coverage_symmetric_direct
    {X V K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    [DecidableEq K] [DecidableEq J] {G:SimpleGraph X}
    (data:ActualResidualData (K:=K) (J:=J) G) (ψ:X→V)
    (Pack:Finset (Finset V)) (hcover:ActualOldPhysicalCoverage data ψ Pack):
    ∀e∈(data.deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))).image (Sym2.map ψ),e.toFinset∈Pack:=by
  classical
  have hWalk {a b:X} (p:G.Walk a b)
      (h:∀k,k<p.length→{ψ (p.getVert k),ψ (p.getVert (k+1))}∈Pack):
      ∀e∈p.edges.toFinset,(Sym2.map ψ e).toFinset∈Pack:=by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨k,hk,heq⟩:=p.mk_mem_edges_iff_exists.mp (List.mem_toFinset.mp he)
      have hh:=h k hk
      have hh':(Sym2.map ψ s(x,y)).toFinset=(Sym2.map ψ s(p.getVert k,p.getVert (k+1))).toFinset:=by rw [heq]
      rw [hh']
      simpa only [Sym2.map_mk,Sym2.toFinset_mk_eq] using hh
  intro e he
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp he
  obtain ⟨hdel,hnot⟩:=Finset.mem_sdiff.mp ha
  simp only [ActualResidualData.deletedEdges,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and] at hdel
  rcases hdel with ⟨j,hj,hjedge⟩|⟨z,hzedge⟩
  · exact hWalk (data.C j) (hcover.1 j hj) a hjedge
  · rcases z with i|r
    · exact False.elim (hnot (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hzedge⟩))
    · exact hWalk (data.path (.inr r)) (hcover.2 r) a hzedge
end Oberwolfach
