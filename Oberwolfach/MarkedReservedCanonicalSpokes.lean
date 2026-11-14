module

public import Oberwolfach.MarkedReservedDeletionInnerAgreement

@[expose] public section
/-! The canonical inner spoke set, including removal of a prescribed set,
is unchanged when the reserved resources avoid the inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem marked_reserved_canonical_inner_spokes
    (H:Bool→V→U→Prop) (C:Finset (Finset V⊕(V×U))) (I:Finset V) (J:Finset U)
    (hC:∀ e∈C,¬markedInnerResource I J e) (removed:Finset (V×U)):
    let DS:=markedFiniteSpokeGraph (markedReservedSpokePairs C)
    let H':=markedDeletePhysicalSpokes H DS;
    (Finset.univ.filter (fun z:V×U=>(H' false z.1 z.2∨H' true z.1 z.2)∧z.1∈I∧z.2∈J))\removed =
      (Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧z.1∈I∧z.2∈J))\removed:=by
  intro DS H'
  have hh:= (marked_reserved_graphs_avoid_internal_resources C I J hC).2
  ext z
  simp only [Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hi:z.1∈I∧z.2∈J
  · have hdel:¬DS.Adj (Sum.inl z.1) (Sum.inr z.2):=hh z.1 hi.1 z.2 hi.2
    simp [H',markedDeletePhysicalSpokes,hdel]
  · simp [hi]
end Oberwolfach
