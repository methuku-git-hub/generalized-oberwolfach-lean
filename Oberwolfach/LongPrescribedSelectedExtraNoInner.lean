module

public import Oberwolfach.LongSelectedExtraHasNoInnerEdges
public import Oberwolfach.LongApproximateGraphStateInclusion
public import Oberwolfach.PrescribedPhysicalUnionImageLoad

@[expose] public section
/-! The same completed factor family has no marked-state extra edges
entirely inside the protected vortex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem long_prescribed_selected_extra_no_inner
    (P S Used K:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (E:U→Finset (Sym2 V))
    (hHost:prescribedPhysicalUnion E≤S)
    (hAvoid:∀w,Disjoint (E w) ((spanningRestriction (S\Used) I)\K).edgeFinset)
    (hUsed:Used≤longApproximatePhysicalGraph P π d ω):
    ∀x∈I,∀y∈I,¬((((prescribedPhysicalUnion E)\K)⊓longPhysicalStateGraph P ω {1}).Adj x y) :=by
  have hAvoidAll:Disjoint (prescribedPhysicalUnion E).edgeFinset
      ((spanningRestriction (S\Used) I)\K).edgeFinset:=by
    apply Finset.disjoint_left.mpr
    intro e he hf
    have he':e∈Finset.univ.biUnion E:=by
      induction e using Sym2.ind with
      | _ x y =>
        have hh:(prescribedPhysicalUnion E).Adj x y:=SimpleGraph.mem_edgeFinset.mp he
        exact ((SimpleGraph.fromEdgeSet_adj _).mp hh).1
    obtain ⟨w,_,hw⟩:=Finset.mem_biUnion.mp he'
    exact (Finset.disjoint_left.mp (hAvoid w)) hw hf
  apply long_selected_extra_has_no_inner_edges S Used K (prescribedPhysicalUnion E) (longPhysicalStateGraph P ω {1}) I hHost hAvoidAll
  intro x y hu hs
  have ha:=long_approximate_graph_in_state_graph P π d ω (hUsed hu)
  have h2:((ω (Sum.inl s(x,y))).1)∈({2,3}:Finset (Fin 6)):=ha.2
  have h1:((ω (Sum.inl s(x,y))).1)=1:=by simpa only [Finset.mem_singleton] using hs.2
  rw [h1] at h2
  norm_num at h2
theorem long_prescribed_selected_extra_no_inner_from_full_packing
    (P S Used K:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (E:U→Finset (Sym2 V)) (Pack:Finset (Sym2 V))
    (hHost:prescribedPhysicalUnion E≤S)
    (hAvoid:∀w,Disjoint (E w) ((spanningRestriction (S\Used) I)\K).edgeFinset)
    (hPackFull:Pack=Used.edgeFinset)
    (hPack:Pack⊆(longApproximatePhysicalGraph P π d ω).edgeFinset):
    ∀x∈I,∀y∈I,¬((((prescribedPhysicalUnion E)\K)⊓longPhysicalStateGraph P ω {1}).Adj x y) :=by
  have hUsed:Used≤longApproximatePhysicalGraph P π d ω:=by
    intro x y h
    have hh:s(x,y)∈(longApproximatePhysicalGraph P π d ω).edgeFinset:=by
      apply hPack
      rw [hPackFull]
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using h
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hh
  exact long_prescribed_selected_extra_no_inner P S Used K π d I ω E hHost hAvoid hUsed
end Oberwolfach
