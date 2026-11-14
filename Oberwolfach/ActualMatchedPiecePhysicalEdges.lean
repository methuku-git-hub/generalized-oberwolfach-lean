module

public import Oberwolfach.ActualMatchedPieceDirectedArcs
public import Oberwolfach.MixedPackingSpokeSeparation

@[expose] public section
/-! Every physical edge of an actual matched old piece belongs to its
original marked or ordinary wheel; this includes the cycle-closing edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_matched_piece_physical_edges_from_wheels
    {X V U E L K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (W:actualSelectedSegmentIndex data→MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (n:{j // j∈data.t}→ℕ) (C:∀j:{j // j∈data.t},OrderedOrdinaryWheel (U:=U) π b (n j+1))
    (u v:actualOldPieceIndex data→V) (q:∀z,(SimpleGraph.completeGraph V).Walk (u z) (v z))
    (hlen:∀z,(q z).length=(actualOldPieceWalk data z).length)
    (hends:∀j:{j // j∈data.t},u (.inl j)=(C j).1.val (cycleNext 0) ∧ v (.inl j)=(C j).1.val 0)
    (hcedges:∀j:{j // j∈data.t},∀k,k<(q (.inl j)).length→∃a:Fin (n j+1),
      (q (.inl j)).getVert k=(C j).1.val a ∧ (q (.inl j)).getVert (k+1)=(C j).1.val (cycleNext a))
    (hredges:∀r:SelectedRunIndex data.s₂ data.d data.T,∀e:Sym2 V,e∈(q (.inr r)).edges→
      ∃z:actualSelectedSegmentIndex data,z.1=r ∧ e.toFinset∈markedCyclePhysicalEdges tail head ktail khead m π b (W z).1)
    (Pack:Finset (Finset V))
    (hCp:∀j a,{(C j).1.val a,(C j).1.val (cycleNext a)}∈Pack)
    (hWp:∀z,markedCyclePhysicalEdges tail head ktail khead m π b (W z).1⊆Pack)
    (ψ:X→V):
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∀(f:{x // x∈A}↪V),
    (∀x (hx:x∈A),ψ x=f ⟨x,hx⟩)→
    (∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
      f ⟨(actualOldPieceWalk data z).getVert k.val,
        Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=
        (q z).getVert k.val)→
    (∀z k,k<(actualOldPieceWalk data z).length→
      {ψ ((actualOldPieceWalk data z).getVert k),ψ ((actualOldPieceWalk data z).getVert (k+1))}∈Pack) ∧
    (∀j∈data.t,∀k<(data.C j).length,{ψ ((data.C j).getVert k),ψ ((data.C j).getVert (k+1))}∈Pack):=by
  intro A f hψ hf
  have hdir:∀z k,k<(q z).length→{(q z).getVert k,(q z).getVert (k+1)}∈Pack:=by
    intro z k hk
    cases z with
    | inl j =>
      obtain ⟨a,ha,hb⟩:=hcedges j k hk
      rw [ha,hb]
      exact hCp j a
    | inr r =>
      have he:s((q (.inr r)).getVert k,(q (.inr r)).getVert (k+1))∈(q (.inr r)).edges:=by
        apply (q (.inr r)).mk_mem_edges_iff_exists.mpr
        exact ⟨k,hk,rfl⟩
      obtain ⟨z,_,hz⟩:=hredges r _ he
      have hh:=hWp z hz
      simpa only [Sym2.toFinset_mk_eq] using hh
  have hclose:∀j:{j // j∈data.t},{v (.inl j),u (.inl j)}∈Pack:=by
    intro j
    rw [(hends j).1,(hends j).2]
    exact hCp j 0
  have ⟨hp,hc⟩:=actual_matched_piece_directed_arcs data (SimpleGraph.completeGraph V) u v q hlen
    (fun x y=>({x,y}:Finset V)∈Pack) hdir hclose ψ f hψ hf
  exact ⟨hp,actual_matched_cycle_directed_arcs data ψ (fun x y=>({x,y}:Finset V)∈Pack) hp hc⟩
end Oberwolfach
