module

public import Oberwolfach.OrdinaryApproximateArcAvoidReferenceHost
public import Oberwolfach.ActualOldDirectedPhysicalHost
public import Oberwolfach.ActualFinalEdgesEmpty

@[expose] public section
/-! With no retained final paths, all old embedded edges avoid the selected
reference colour because their source arcs come from the approximate sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_old_approximate_edges_disjoint_reference
    {n:ℕ} {U X A B J:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=A⊕B) (J:=J) F) (ψ:X→Fin n)
    (hempty:IsEmpty A) (hs:data.s₁=firstSumIndices)
    (Host P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (hdir:ActualOldImageDirected data ψ
      (rawMixedPhysicalArc Host π d (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset))):
    Disjoint (data.deletedEdges.image (Sym2.map ψ)) (longPhysicalStateGraph P σ {0}).edgeFinset:=by
  let Ref:=longPhysicalStateGraph P σ {0}
  letI:DecidableRel (⊤\Ref).Adj:=Classical.decRel _
  have hhost:=actual_old_directed_physical_host data ψ (⊤\Ref)
    (rawMixedPhysicalArc Host π d (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset))
    (ordinary_approximate_arc_avoids_reference_host Host P Del π d σ) hdir
  have hfinal:=actual_final_edges_empty_of_empty_first_index data hempty hs
  rw [hfinal,Finset.sdiff_empty] at hhost
  apply Finset.disjoint_left.mpr
  intro e he hRef
  have hehost:=hhost he
  have hehost':e∈(⊤\Ref).edgeSet:=
    (@SimpleGraph.mem_edgeFinset (Fin n) (⊤\Ref) e ((⊤\Ref).fintypeEdgeSet)).mp hehost
  induction e using Sym2.ind with
  | _ x y =>
    have hh:(⊤\Ref).Adj x y:=hehost'
    exact hh.2 (SimpleGraph.mem_edgeFinset.mp hRef)
end Oberwolfach
