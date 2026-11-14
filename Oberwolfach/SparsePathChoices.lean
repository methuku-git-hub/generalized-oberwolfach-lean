module

public import Oberwolfach.FixedLengthPaths
public import Oberwolfach.DenseCommonNeighbourBounds

@[expose] public section

/-! Choosing an internal path vertex using an actual common-neighbour
count. Vertex exclusions and forbidden graph neighbours are subtracted
without a sampling-density factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sparse_common_neighbour_avoiding (Q F : SimpleGraph V) (A W Z : Finset V)
    (x y : V) (L b : ℝ) (hL : 0≤L) (hF : ∀ v,(F.degree v:ℝ)≤L)
    (hcount : b≤((A∩Q.neighborFinset x∩Q.neighborFinset y).card:ℝ))
    (hbudget : W.card+(Z.card:ℝ)*(L+1)<b) :
    ∃ v∈A,v∉W ∧ v∉Z ∧ Q.Adj x v ∧ Q.Adj y v ∧ ∀ z∈Z,¬F.Adj v z := by
  let D:=W∪(Z∪Z.biUnion (fun z=>F.neighborFinset z))
  have hZ:=forbidden_used_neighbours_card F Z L hF
  have hD : (D.card:ℝ)≤W.card+(Z.card:ℝ)*(L+1):=by
    have hh : (D.card:ℝ)≤W.card+(Z∪Z.biUnion (fun z=>F.neighborFinset z)).card:=by
      exact_mod_cast Finset.card_union_le W (Z∪Z.biUnion (fun z=>F.neighborFinset z))
    linarith only [hh,hZ]
  have hlt : D.card<(A∩Q.neighborFinset x∩Q.neighborFinset y).card:=by
    exact_mod_cast hD.trans_lt (hbudget.trans_le hcount)
  obtain ⟨v,hv,hvD⟩:=Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨hvAx,hvy⟩:=Finset.mem_inter.mp hv
  obtain ⟨hvA,hvx⟩:=Finset.mem_inter.mp hvAx
  have hout : v∉W ∧ v∉Z ∧ v∉Z.biUnion (fun z=>F.neighborFinset z):=by
    simpa only [D,Finset.mem_union,not_or] using hvD
  refine ⟨v,hvA,hout.1,hout.2.1,(Q.mem_neighborFinset x v).mp hvx,
    (Q.mem_neighborFinset y v).mp hvy,?_⟩
  intro z hz he
  exact hout.2.2 (Finset.mem_biUnion.mpr ⟨z,hz,(F.mem_neighborFinset z v).mpr he.symm⟩)

end Oberwolfach
