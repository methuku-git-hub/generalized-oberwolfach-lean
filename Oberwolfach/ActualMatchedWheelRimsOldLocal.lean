module

public import Oberwolfach.ActualRunWheelEdgesSaturateLocal
public import Oberwolfach.ActualMatchedRunEdgesOld

@[expose] public section
/-! Every selected marked wheel edge is an actual old embedded edge of its
run, under the wheel packing and matched-walk hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_matched_wheel_rims_old_local
    {X V U E L K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [LinearOrder V] [DecidableEq U] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (G:SimpleGraph V) (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (hc:data.c=m+1)
    (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (W:actualSelectedSegmentIndex data→MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (hm:2≤m) (hb:1≤b)
    (hpair:∀z z',z≠z'→Disjoint (markedWheelPhysicalResources (W z)) (markedWheelPhysicalResources (W z')))
    (u v:SelectedRunIndex data.s₂ data.d data.T→V) (q:∀r,G.Walk (u r) (v r)) (ψ:X→V)
    (hq:∀r,(q r).IsPath)
    (hlen:∀r,(q r).length=data.c*(r.2.val.2+1-r.2.val.1))
    (hlenSource:∀r,(q r).length=(data.path (.inr r)).length)
    (hmap:∀r k,k≤(data.path (.inr r)).length→ψ ((data.path (.inr r)).getVert k)=(q r).getVert k)
    (hcover:∀r edge,edge∈(q r).edges→∃z:actualSelectedSegmentIndex data,z.1=r ∧ edge.toFinset∈markedCyclePhysicalEdges tail head ktail khead m π b (W z).1):
    ∀z edge,edge∈markedCyclePhysicalEdges tail head ktail khead m π b (W z).1→
      ∃e∈(data.deletedEdges\(Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))).image (Sym2.map ψ),e.toFinset=edge:=by
  intro z edge he
  have hh:=actual_run_wheel_edges_saturate_local data G tail head ktail khead m b hc π H₀ Hₖ W hm hb hpair z.1 (q z.1) (hq z.1) (hlen z.1) (hcover z.1) z rfl he
  obtain ⟨e,heq,he⟩:=Finset.mem_image.mp hh
  have hold:=actual_matched_run_edges_old data z.1 G (q z.1) ψ (hlenSource z.1) (hmap z.1)
  exact ⟨e,hold heq,he⟩
end Oberwolfach
