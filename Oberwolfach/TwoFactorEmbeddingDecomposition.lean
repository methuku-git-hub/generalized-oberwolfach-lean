module

public import Oberwolfach.TwoFactorEdgePartitionCount
public import Oberwolfach.ResidualTwoFactorEdgeCount
public import Oberwolfach.ResidualActualEdgePartition
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section
/-! Convert edge-disjoint spanning embeddings in a host of matching regular
degree into the manuscript's exact decomposition definition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem spanning_two_factor_embeddings_give_decomposition {n q:ℕ}
    (G:SimpleGraph (Fin n)) (hG:G.IsRegularOfDegree (2*q))
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀i,(F i).IsRegularOfDegree 2)
    (f:Fin q→Fin n→Fin n) (hinj:∀i,Function.Injective (f i))
    (hsub:∀i,((F i).edgeFinset).image (Sym2.map (f i))⊆G.edgeFinset)
    (hdis:PairwisePhysicalDisjoint (fun i=>((F i).edgeFinset).image (Sym2.map (f i)))):
    HasFactorDecomposition G F :=by
  let e:Fin q→Fin n≃Fin n:=fun i=>Equiv.ofBijective (f i)
    ⟨hinj i,(Finite.injective_iff_surjective).mp (hinj i)⟩
  let P:Fin q→SimpleGraph (Fin n):=fun i=>(F i).map (e i).toEmbedding
  have hPE:∀i,(P i).edgeFinset=((F i).edgeFinset).image (Sym2.map (f i)):=by
    intro i
    have hh:=SimpleGraph.edgeFinset_map (e i).toEmbedding (F i)
    rw [Finset.map_eq_image] at hh
    convert hh using 1
    · apply graph_edge_finset_instance_eq
    · rfl
  have hcard:∀i,(((F i).edgeFinset).image (Sym2.map (f i))).card=n:=by
    intro i
    rw [Finset.card_image_of_injective _ (Sym2.map.injective (hinj i))]
    simpa using two_factor_edge_count (F i) (hF i)
  have hexhaust:=regular_host_two_factor_edge_sets_exhaust G hG
    (fun i=>((F i).edgeFinset).image (Sym2.map (f i))) hcard hsub hdis
  refine ⟨P,?_,?_⟩
  · intro x y
    constructor
    · constructor
      · intro hxy
        have he:s(x,y)∈Finset.univ.biUnion (fun i=>((F i).edgeFinset).image (Sym2.map (f i))):=by
          rw [hexhaust]
          exact SimpleGraph.mem_edgeFinset.mpr hxy
        obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
        exact ⟨i,SimpleGraph.mem_edgeFinset.mp (by rw [hPE i];exact hi)⟩
      · rintro ⟨i,hi⟩
        have hip:s(x,y)∈(P i).edgeFinset:=by
          simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hi
        have he:s(x,y)∈G.edgeFinset:=hsub i (by rw [←hPE i];exact hip)
        simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he
    · intro i j hi hj
      by_contra hne
      have hi':s(x,y)∈((F i).edgeFinset).image (Sym2.map (f i)):=by
        rw [←hPE i];exact SimpleGraph.mem_edgeFinset.mpr hi
      have hj':s(x,y)∈((F j).edgeFinset).image (Sym2.map (f j)):=by
        rw [←hPE j];exact SimpleGraph.mem_edgeFinset.mpr hj
      exact (Finset.disjoint_left.mp (hdis i j hne)) hi' hj'
  · intro i
    exact ⟨(SimpleGraph.Iso.map (e i) (F i)).symm⟩
theorem even_regular_two_factor_embeddings_give_decomposition {n D:ℕ}
    (hEven:Even D) (G:SimpleGraph (Fin n)) (hG:G.IsRegularOfDegree D)
    (F:Fin (D/2)→SimpleGraph (Fin n)) (hF:∀i,(F i).IsRegularOfDegree 2)
    (f:Fin (D/2)→Fin n→Fin n) (hinj:∀i,Function.Injective (f i))
    (hsub:∀i,((F i).edgeFinset).image (Sym2.map (f i))⊆G.edgeFinset)
    (hdis:PairwisePhysicalDisjoint (fun i=>((F i).edgeFinset).image (Sym2.map (f i)))):
    HasFactorDecomposition G F :=by
  have hD:2*(D/2)=D:=by obtain ⟨k,rfl⟩:=hEven;omega
  apply spanning_two_factor_embeddings_give_decomposition G _ F hF f hinj hsub hdis
  simpa only [hD] using hG
end Oberwolfach
