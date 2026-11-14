module

public import Oberwolfach.MarkedCoverPackingAvoidance
public import Oberwolfach.MarkedPackingResourceDetermination
public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section

/-! An actual earlier wheel packing outside the reserved inner pair and
sampled boundary satisfies the exclusions used by the outside cover.
Its global maximum degree is unrestricted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {m b:ℕ}

theorem marked_packing_rim_pair_adj (hm:1≤m) (hb:1≤b)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (x y:V)
    (he:Sum.inl ({x,y}:Finset V)∈M.biUnion markedWheelPhysicalResources):
    (markedPackingRimGraph M).Adj x y:=by
  have hpair:({x,y}:Finset V)∈markedPackingRims M:=(markedPackingResources_rim M _).mp he
  have hcard:({x,y}:Finset V).card=2:=by
    obtain ⟨W,hW,hWe⟩:=Finset.mem_biUnion.mp hpair
    obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hWe
    rw [←ha]
    exact markedCycle_physical_edge_card tail head ktail khead m π b hm hb W.1 a
  exact ⟨by intro h;subst y;simp at hcard,hpair⟩

theorem marked_approximate_packing_reservation_exclusions
    (hm:1≤m) (hb:1≤b) (X:Finset V) (Z:Finset U) (hX:∀ x,π x∈X↔x∈X)
    (σ:Sym2 (V⊕U)→Bool) (Q:SimpleGraph V) (H:V→U→Prop)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hhost:ordinaryPhysicalGraph (markedPackingRimGraph M) (markedPackingSpokes M)≤ordinaryPhysicalGraph Q H)
    (hinner:∀ e∈M.biUnion markedWheelPhysicalResources,¬markedInnerResource X Z e)
    (hreserved:Disjoint (ordinaryPhysicalGraph (markedPackingRimGraph M) (markedPackingSpokes M))
      (retainedGraph (ordinaryBoundaryGraph Q H X Z) σ)):
    (∀ j x y,markedBoundaryRimAllowed π X σ j x y→
      Sum.inl (if j then ({x,π y}:Finset V) else {x,y})∉M.biUnion markedWheelPhysicalResources)∧
    (∀ x u,markedBoundarySpokeAllowed X Z σ x u→Sum.inr (x,u)∉M.biUnion markedWheelPhysicalResources):=by
  let D:=ordinaryPhysicalGraph (markedPackingRimGraph M) (markedPackingSpokes M)
  have hcross (a c:V⊕U) (ha:a∈ordinaryInnerVertices X Z∨c∈ordinaryInnerVertices X Z)
      (hn:¬(a∈ordinaryInnerVertices X Z∧c∈ordinaryInnerVertices X Z))
      (hcoin:σ s(a,c)=true) (hadj:D.Adj a c):False:=by
    have hB:(ordinaryBoundaryGraph Q H X Z).Adj a c:=by
      rw [ordinaryBoundaryGraph_adj]
      exact ⟨hhost hadj,by tauto⟩
    exact disjoint_graphs_no_common_edge _ _ hreserved a c hadj ⟨hB,hcoin⟩
  constructor
  · intro j x y hallow he
    let y':=if j then π y else y
    have hy:y'∈X↔y∈X:=by cases j <;> simp only [y',Bool.false_eq_true,ite_false,ite_true];exact hX y
    have he':Sum.inl ({x,y'}:Finset V)∈M.biUnion markedWheelPhysicalResources:=by cases j <;> exact he
    have hnot:¬(x∈X∧y'∈X):=by
      intro hi
      apply hinner _ he'
      change ({x,y'}:Finset V)⊆X
      simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using hi
    have hadj:D.Adj (Sum.inl x) (Sum.inl y'):=marked_packing_rim_pair_adj hm hb M x y' he'
    rcases hallow with hi|⟨hi,hcoin⟩
    · exact hnot ⟨hi.1,hy.mpr hi.2⟩
    · apply hcross (Sum.inl x) (Sum.inl y') _ _ hcoin hadj
      · simpa only [ordinaryInnerVertices_left] using hi.imp id hy.mpr
      · simpa only [ordinaryInnerVertices_left] using hnot
  · intro x u hallow he
    have hadj:D.Adj (Sum.inl x) (Sum.inr u):=(markedPackingResources_spoke M x u).mp he
    have hnot:¬(x∈X∧u∈Z):=fun hi=>hinner _ he hi
    rcases hallow with hi|⟨hi,hcoin⟩
    · exact hnot hi
    · apply hcross (Sum.inl x) (Sum.inr u) _ _ hcoin hadj
      · simpa only [ordinaryInnerVertices_left,ordinaryInnerVertices_right] using hi
      · simpa only [ordinaryInnerVertices_left,ordinaryInnerVertices_right] using hnot
end Oberwolfach
