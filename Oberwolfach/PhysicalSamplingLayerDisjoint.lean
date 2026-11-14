module

public import Oberwolfach.LongApproximatePhysicalStates

@[expose] public section
/-! Selected and approximate physical rim graphs come from disjoint
categorical states of the same undirected edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem marked_sample_graph_edge_has_physical_state
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (raw:RawMarkedOutcome V U Γ Color)
    (x y:V) (h:(markedSampleArcSetGraph P π d raw Finset.univ).Adj x y):
    ∃b o,raw (Sum.inl s(x,y))=some (b,o):=by
  change x≠y ∧ ({x,y}:Finset V)∈
    (Finset.univ.image (markedPhysicalEdge
      (fun e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) false=>e.val.1)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) false=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) true=>e.val.1)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) true=>e.val.2) π)) at h
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp h.2
  have hpair {a b c e:V} (hh:({a,b}:Finset V)={c,e}):s(a,b)=s(c,e):=by
    apply Sym2.eq_iff.mpr
    apply Set.pair_eq_pair_iff.mp
    simpa only [Finset.coe_pair] using congrArg (fun S:Finset V=>(S:Set V)) hh
  cases a with
  | inl e=>
    have hval:raw (Sum.inl s(e.val.1,e.val.2))=some (false,orientationBit e.val.1 e.val.2):=
      ((markedPhysicalRim_eq_one_iff P π (3*d) _ false e.val.1 e.val.2).mp e.property).2.2
    have hp:s(e.val.1,e.val.2)=s(x,y):=hpair (by simpa [markedPhysicalEdge] using ha)
    exact ⟨false,orientationBit e.val.1 e.val.2,hp ▸ hval⟩
  | inr e=>
    have hval:raw (Sum.inl s(e.val.1,π e.val.2))=some (true,orientationBit e.val.1 (π e.val.2)):=
      ((markedPhysicalRim_eq_one_iff P π (3*d) _ true e.val.1 e.val.2).mp e.property).2.2
    have hp:s(e.val.1,π e.val.2)=s(x,y):=hpair (by simpa [markedPhysicalEdge] using ha)
    exact ⟨true,orientationBit e.val.1 (π e.val.2),hp ▸ hval⟩

theorem selected_and_approximate_rim_graphs_disjoint
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):
    Disjoint (longSelectedPhysicalGraph P π d σ) (longApproximatePhysicalGraph P π d σ):=by
  apply disjoint_iff_inf_le.mpr
  intro x y h
  obtain ⟨b,o,hsel⟩:=marked_sample_graph_edge_has_physical_state P π d (fun e=>rawExpandedMarkedCollapse e (σ e)) x y h.1
  obtain ⟨b',o',happ⟩:=marked_sample_graph_edge_has_physical_state P π d (fun e=>rawExpandedApproximateCollapse e (σ e)) x y h.2
  have hh:¬(markedExpandedPhysicalCollapse (σ (Sum.inl s(x,y)))≠none ∧
      markedExpandedApproximateCollapse (σ (Sum.inl s(x,y)))≠none):=by
    rcases σ (Sum.inl s(x,y)) with ⟨z,o⟩
    fin_cases z <;> simp [markedExpandedPhysicalCollapse,markedExpandedApproximateCollapse]
  apply hh
  constructor
  · simp only [rawExpandedMarkedCollapse] at hsel
    rw [hsel];exact Option.some_ne_none _
  · simp only [rawExpandedApproximateCollapse] at happ
    rw [happ];exact Option.some_ne_none _
end Oberwolfach
