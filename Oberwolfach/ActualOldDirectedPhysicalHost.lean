module

public import Oberwolfach.ActualOldCoverageSymmetricDirect
public import Oberwolfach.WheelRunPhysicalEdgeSaturation

@[expose] public section
/-! Directed old-piece images in a graph place every surviving symmetric old
edge in that graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_directed_physical_host
    {X V K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    [DecidableEq K] [DecidableEq J] {G:SimpleGraph X}
    (data:ActualResidualData (K:=K) (J:=J) G) (ψ:X→V)
    (H:SimpleGraph V) (Arc:V→V→Prop) (hArc:∀x y,Arc x y→H.Adj x y)
    (hdir:ActualOldImageDirected data ψ Arc):
    (data.deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))).image (Sym2.map ψ)⊆H.edgeFinset:=by
  classical
  let Pack:=H.edgeFinset.image Sym2.toFinset
  have hcover:ActualOldPhysicalCoverage data ψ Pack:=by
    constructor
    · intro j hj k hk
      have hh:=hArc _ _ (hdir.1 j hj k hk)
      exact Finset.mem_image.mpr ⟨s(ψ ((data.C j).getVert k),ψ ((data.C j).getVert (k+1))),
        SimpleGraph.mem_edgeFinset.mpr hh,by ext v; simp only [Sym2.toFinset_mk_eq,Finset.mem_insert,Finset.mem_singleton]⟩
    · intro r k hk
      have hh:=hArc _ _ (hdir.2 r k hk)
      exact Finset.mem_image.mpr ⟨s(ψ ((data.path (.inr r)).getVert k),ψ ((data.path (.inr r)).getVert (k+1))),
        SimpleGraph.mem_edgeFinset.mpr hh,by ext v; simp only [Sym2.toFinset_mk_eq,Finset.mem_insert,Finset.mem_singleton]⟩
  intro e he
  have he':e.toFinset∈Pack:=actual_old_coverage_symmetric_direct data ψ Pack hcover e he
  obtain ⟨f,hf,hfe⟩:=Finset.mem_image.mp he'
  have hEq:f=e:=sym2_toFinset_injective_local hfe
  simpa only [hEq] using hf
end Oberwolfach
