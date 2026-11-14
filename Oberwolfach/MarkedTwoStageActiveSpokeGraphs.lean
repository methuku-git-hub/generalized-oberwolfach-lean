module

public import Oberwolfach.MarkedFiniteResourceOperations
public import Oberwolfach.MarkedFinitePhysicalDeletion

@[expose] public section
/-! The two cover-down deletion graphs contain no spoke inside the active
inner pair. This holds as a graph statement, including absent host spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K':Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K] [Fintype E'] [Fintype K']
  [LinearOrder V] [DecidableEq U] [DecidableEq E] [DecidableEq K] [DecidableEq E'] [DecidableEq K']
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}
  {tail' head':E'→V} {ktail' khead':K'→V} {π':Equiv.Perm V} {m' b':ℕ} {H₀' HK':V→U→Prop}
theorem marked_two_stage_deletion_spoke_graphs_avoid_active_pair
    (I T:Finset V) (J W:Finset U) (S₀:Finset (V×U))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (R:Finset (Finset V⊕(V×U)))
    (hM:(M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
      R.filter (markedStarResource T W))
    (N:Finset (MarkedWheel tail' head' ktail' khead' m' π' b' H₀' HK'))
    (hN:(N.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅):
    let S:=S₀.filter (fun z=>z.1∈T∨z.2∈W)
    let DS₁:=markedFiniteSpokeGraph (S∪M.biUnion markedWheelSpokePairs)
    let DS₂:=markedFiniteSpokeGraph (N.biUnion markedWheelSpokePairs);
    ∀ v∈I\T,∀ u∈J\W,¬DS₁.Adj (Sum.inl v) (Sum.inr u)∧¬DS₂.Adj (Sum.inl v) (Sum.inr u):=by
  intro S DS₁ DS₂ v hv u hu
  have hvI: v∈I:=(Finset.mem_sdiff.mp hv).1
  have hvT: v∉T:=(Finset.mem_sdiff.mp hv).2
  have huJ: u∈J:=(Finset.mem_sdiff.mp hu).1
  have huW: u∉W:=(Finset.mem_sdiff.mp hu).2
  constructor
  · intro hadj
    have hz:(v,u)∈S∪M.biUnion markedWheelSpokePairs:=(markedFiniteSpokeGraph_adj _ v u).mp hadj
    rcases Finset.mem_union.mp hz with hz|hz
    · exact (Finset.mem_filter.mp hz).2.elim hvT huW
    · have hr:Sum.inr (v,u)∈(M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J):=by
        apply Finset.mem_filter.mpr
        constructor
        · rw [←markedPackingResources_eq_finite tail head ktail khead π M]
          exact (markedFiniteResources_spoke tail head ktail khead π _ _ (v,u)).mpr hz
        · exact ⟨hvI,huJ⟩
      rw [hM] at hr
      exact (Finset.mem_filter.mp hr).2.elim hvT huW
  · intro hadj
    have hz:(v,u)∈N.biUnion markedWheelSpokePairs:=(markedFiniteSpokeGraph_adj _ v u).mp hadj
    have hr:Sum.inr (v,u)∈(N.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J):=by
      apply Finset.mem_filter.mpr
      constructor
      · rw [←markedPackingResources_eq_finite tail' head' ktail' khead' π' N]
        exact (markedFiniteResources_spoke tail' head' ktail' khead' π' _ _ (v,u)).mpr hz
      · exact ⟨hvI,huJ⟩
    rw [hN] at hr
    exact Finset.notMem_empty _ hr
end Oberwolfach
