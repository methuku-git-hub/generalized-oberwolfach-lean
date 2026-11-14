module

public import Oberwolfach.EndpointRowCover
public import Oberwolfach.BipartiteRelationGraph
public import Oberwolfach.RowComparisonCover

@[expose] public section

/-! Triangle row covers in the comparison host. The symmetric graph used
for deleted spokes has the same row-to-hub edges as the previous packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem triangle_comparison_cover_of_factor (Q H F : SimpleGraph V) (A B X : Finset V)
    (hAB : Disjoint A B) (hXA : X⊆A) (x : V) (hxA : x∉X) (hxB : x∉B)
    (hA : Q.neighborFinset x⊆X) (hB : H.neighborFinset x⊆B)
    (hHA : ∀ a∈X,H.neighborFinset a⊆B)
    (hF : ∀ a,Q.Adj x a → ¬F.Adj x a)
    (M : Finset (OrdinaryWheel Q F H.Adj 3))
    (hM : ∀ W∈M,x∉(ordinaryWheelRim W).support)
    (hfactor : HasResourceDecomposition
      (endpointTriangleVertices
        (Q:=endpointHostGraph
          (Q\spanningRestriction (ordinaryWheelRimGraph M) X)
          (H\bipartiteRelationGraph X B (hAB.mono_left hXA) (ordinaryPackingSpokes M)) A B)
        (F:=F) (S:=Q.neighborFinset x) (T:=H.neighborFinset x))
      (Q.neighborFinset x∪H.neighborFinset x)) :
    ∃ N : Finset (OrdinaryWheel Q F H.Adj 3), OrdinaryRowCover N x X 0 ∧
      Disjoint (N.biUnion ordinaryWheelResources) (M.biUnion ordinaryWheelResources) := by
  let D:=spanningRestriction (ordinaryWheelRimGraph M) X
  let E:=bipartiteRelationGraph X B (hAB.mono_left hXA) (ordinaryPackingSpokes M)
  have hxD (a:V):¬D.Adj x a:=by
    intro h;exact hxA ((spanningRestriction_adj _ X x a).mp h).2.1
  have hxE (a:V):¬E.Adj x a:=bipartiteRelationGraph_outside X B (hAB.mono_left hXA) _ hxA hxB
  have hQr (a:V):(Q\D).Adj x a ↔ Q.Adj x a:=by simp [SimpleGraph.sdiff_adj,hxD]
  have hHr (a:V):(H\E).Adj x a ↔ H.Adj x a:=by simp [SimpleGraph.sdiff_adj,hxE]
  have hQN:(Q\D).neighborFinset x=Q.neighborFinset x:=by
    ext a;simp only [SimpleGraph.mem_neighborFinset,hQr]
  have hHN:(H\E).neighborFinset x=H.neighborFinset x:=by
    ext a;simp only [SimpleGraph.mem_neighborFinset,hHr]
  obtain ⟨N,hN⟩:=endpoint_factor_row_cover (Q\D) (H\E) F A B X
    (Q.neighborFinset x) (H.neighborFinset x) hAB hXA x hA hB
    (fun a=>(hQr a).trans (Q.mem_neighborFinset x a).symm)
    (fun u=>(hHr u).trans (H.mem_neighborFinset x u).symm)
    (fun a ha=>hF a ha.1) hfactor
  have hspoke (a u:V) (h:(H\E).Adj a u):H.Adj a u ∧ ¬(a∈X∧ordinaryPackingSpokes M a u):=by
    refine ⟨h.1,?_⟩
    rintro ⟨ha,hold⟩
    have hu:u∈B:=hHA a ha ((H.mem_neighborFinset a u).mpr h.1)
    exact h.2 (Or.inl ⟨ha,hu,hold⟩)
  let C:N→OrdinaryWheel (Q\D) F (fun a u=>H.Adj a u∧¬(a∈X∧ordinaryPackingSpokes M a u)) 3:=
    fun W=>ordinaryWheelToLarger le_rfl hspoke W.val
  have he:Finset.univ.image (fun W:N=>W.val)=N:=by ext W;simp
  have hr:wheelFamilyRim C=ordinaryWheelRimGraph N:=by
    change wheelFamilyRim (fun W:N=>W.val)=_
    rw [←ordinary_family_image_rim,he]
  have hs:wheelFamilySpokes C=ordinaryPackingSpokes N:=by
    change wheelFamilySpokes (fun W:N=>W.val)=_
    rw [←ordinary_family_image_spokes,he]
  apply row_comparison_cover_image M X x 0 hM C
  · intro W a ha;exact hN.support W.val W.property a ha
  · intro W Z hne
    exact hN.disjoint W.val W.property Z.val Z.property (fun h=>hne (Subtype.ext h))
  · intro a;rw [hr];exact (hN.rims a).trans (hQr a)
  · intro u;rw [hs];exact (hN.spokes u).trans (hHr u)
  · intro a ha;rw [hr];exact hN.rimDegree a ha
  · intro a ha;rw [hs];exact hN.rowDegree a ha
  · intro u;rw [hs];exact hN.columnDegree u

end Oberwolfach
