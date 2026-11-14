module

public import Oberwolfach.MarkedVortexRestrictionChain
public import Oberwolfach.MarkedReservedResourceGraphs
public import Oberwolfach.MarkedProtectedResourceRestoration

@[expose] public section
/-! The physical deletion graphs formed from all covered layers avoid the
preselected reserve. If each layer avoids the terminal spoke pair, so does
the cumulative spoke deletion. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem marked_resource_layers_cumulative_deletion_protects
    (B C:ℕ→Finset (Finset V⊕(V×U))) (n:ℕ)
    (Full Reserve:Finset (Finset V⊕(V×U))) (X:Finset V) (Z:Finset U)
    (hB:∀ i,i<n→B (i+1)⊆B i)
    (hC:∀ i,i<n→C i=B i\B (i+1))
    (hInitial:B 0=Full\Reserve)
    (hTerminal:∀ i,i<n→∀ v∈X,∀ u∈Z,Sum.inr (v,u)∉C i):
    let Covered:=(Finset.range n).biUnion C
    let DR:=physicalEdgeGraph (markedReservedRimPairs Covered)
    let DS:=markedFiniteSpokeGraph (markedReservedSpokePairs Covered);
    (∀ x y,Sum.inl ({x,y}:Finset V)∈Reserve→¬DR.Adj x y)∧
    (∀ v u,Sum.inr (v,u)∈Reserve→¬DS.Adj (Sum.inl v) (Sum.inr u))∧
    (∀ v∈X,∀ u∈Z,¬DS.Adj (Sum.inl v) (Sum.inr u)):=by
  intro Covered DR DS
  have hsub:Covered⊆B 0:=by
    intro z hz
    have hpart:=finite_resource_layers_partition B C n hB hC
    apply hpart ▸ Finset.mem_union_left (B n) hz
  have hdis:Disjoint Reserve Covered:=by
    apply Finset.disjoint_left.mpr
    intro z hzC hzD
    have hz:=hsub hzD
    rw [hInitial] at hz
    exact (Finset.mem_sdiff.mp hz).2 hzC
  have hgraphs:=marked_reserved_resource_graphs Covered
  refine ⟨?_,?_,?_⟩
  · intro x y he hadj
    have hh:Sum.inl ({x,y}:Finset V)∈Covered:=(hgraphs.1 x y).mp hadj |>.2
    exact Finset.disjoint_left.mp hdis he hh
  · intro v u he hadj
    have hh:Sum.inr (v,u)∈Covered:=(hgraphs.2.1 v u).mp hadj
    exact Finset.disjoint_left.mp hdis he hh
  · intro v hv u hu hadj
    have hh:Sum.inr (v,u)∈Covered:=(hgraphs.2.1 v u).mp hadj
    obtain ⟨i,hi,hz⟩:=Finset.mem_biUnion.mp hh
    exact hTerminal i (Finset.mem_range.mp hi) v hv u hu hz
/-- The first cover-down may use inner spokes only in its specified star.
It therefore avoids spokes between vertices in I\T and hubs in J\W. -/
theorem marked_cover_down_avoids_deeper_spokes
    (C R:Finset (Finset V⊕(V×U))) (I T X:Finset V) (J W Z:Finset U)
    (hX:X⊆I\T) (hZ:Z⊆J\W)
    (hcover:C.filter (markedInnerResource I J)=R.filter (markedStarResource T W)):
    ∀ v∈X,∀ u∈Z,Sum.inr (v,u)∉C:=by
  intro v hv u hu hc
  have hv':=Finset.mem_sdiff.mp (hX hv)
  have hu':=Finset.mem_sdiff.mp (hZ hu)
  have hi:markedInnerResource I J (Sum.inr (v,u)):=⟨hv'.1,hu'.1⟩
  have hf:Sum.inr (v,u)∈R.filter (markedStarResource T W):=by
    rw [←hcover]
    exact Finset.mem_filter.mpr ⟨hc,hi⟩
  have hs:= (Finset.mem_filter.mp hf).2
  change v∈T∨u∈W at hs
  exact hs.elim hv'.2 hu'.2

end Oberwolfach
