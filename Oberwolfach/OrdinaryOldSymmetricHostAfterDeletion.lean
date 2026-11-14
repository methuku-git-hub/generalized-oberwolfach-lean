module

public import Oberwolfach.ActualOldDirectedPhysicalHost
public import Oberwolfach.RawMixedDeletedArcHost

@[expose] public section
/-! The old-piece images use only surviving host edges on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_old_symmetric_host_after_deletion
    {n:ℕ} {U X K J:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    [DecidableEq K] [DecidableEq J] {F:SimpleGraph X}
    (data:ActualResidualData (K:=K) (J:=J) F) (ψ:X→Fin n)
    (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (hdir:ActualOldImageDirected data ψ (rawMixedPhysicalArc P π d (rawMarkedDeleteRims raw Del.edgeFinset))):
    (data.deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))).image (Sym2.map ψ)⊆(P\Del).edgeFinset:=by
  letI:DecidableRel (P\Del).Adj:=Classical.decRel _
  have hArc:∀x y,rawMixedPhysicalArc P π d (rawMarkedDeleteRims raw Del.edgeFinset) x y→(P\Del).Adj x y:=by
    intro x y h
    exact raw_mixed_deleted_arc_host P Del π d raw x y h
  have hh:=actual_old_directed_physical_host data ψ (P\Del)
    (rawMixedPhysicalArc P π d (rawMarkedDeleteRims raw Del.edgeFinset)) hArc hdir
  intro e he
  have he':e∈(P\Del).edgeSet:=
    (@SimpleGraph.mem_edgeFinset (Fin n) (P\Del) e (P\Del).fintypeEdgeSet).mp (hh he)
  exact (@SimpleGraph.mem_edgeFinset (Fin n) (P\Del) e (P.fintypeEdgeSetSdiff Del)).mpr he' 
end Oberwolfach
