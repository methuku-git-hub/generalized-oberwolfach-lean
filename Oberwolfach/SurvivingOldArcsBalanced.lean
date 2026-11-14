module

public import Oberwolfach.OrientationDisagreementGraph
public import Oberwolfach.ActualOldArcContainment

@[expose] public section
/-! The surviving old packing keeps its sampled directions after balancing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem surviving_old_arcs_follow_balanced_orientation
    {V X K J U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype X] [DecidableEq X]
    [DecidableEq K] [DecidableEq J] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ) (Used:SimpleGraph V) (hUsed:∀x y,Used.Adj x y→
      ¬(orientationDisagreementGraph P (fun e=>(σ (Sum.inl e)).2) M).Adj x y)
    (F:SimpleGraph X) (data:ActualResidualData (K:=K) (J:=J) F) (ψ:X→V)
    (finalEdges:Finset (Sym2 X)) (Dsrc:X→X→Prop)
    (hOldPack:(data.deletedEdges\finalEdges).image (Sym2.map ψ)⊆Used.edgeFinset)
    (hOldArc:∀x y,s(x,y)∈data.deletedEdges\finalEdges→Dsrc x y→
      rawMixedPhysicalArc P π d (fun e=>rawExpandedApproximateCollapse e (σ e)) (ψ x) (ψ y)):
    ∀x y,s(x,y)∈data.deletedEdges\finalEdges→Dsrc x y→M (ψ x) (ψ y)=1:=by
  intro x y he hsrc
  have hRaw:=hOldArc x y he hsrc
  have hSample:=expanded_approximate_arc_uses_sampled_orientation P π d σ (ψ x) (ψ y) hRaw
  have hUsedEdge:s(ψ x,ψ y)∈Used.edgeFinset:=by
    apply hOldPack
    exact Finset.mem_image.mpr ⟨s(x,y),he,by simp⟩
  have hUsedAdj:Used.Adj (ψ x) (ψ y):=SimpleGraph.mem_edgeFinset.mp hUsedEdge
  have hDel:=hUsed _ _ hUsedAdj
  by_contra hM
  apply hDel
  have hP:P.Adj (ψ x) (ψ y):=by
    by_contra hn
    simp [sampledOrientation,hn] at hSample
  exact ⟨hP,Or.inl (by simpa [hSample] using hM)⟩
end Oberwolfach
