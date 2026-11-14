module

public import Oberwolfach.PrescribedDependentPositions
public import Oberwolfach.PrescribedEmbeddingDisjointUpdate

@[expose] public section
/-! If the matching edge sets assigned to different factors are physically
disjoint and contained in a graph, the number of matching endpoint sets
containing a fixed vertex is at most its degree in that graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

theorem prescribed_matching_endpoint_occurrences (M:I→Finset (V×V)) (K:SimpleGraph V)
    (hsub:∀i,(M i).image prescribedArcPhysical⊆K.edgeFinset)
    (hpair:PairwisePhysicalDisjoint (fun i=>(M i).image prescribedArcPhysical)) (v:V):
    (Finset.univ.filter (fun i=>v∈prescribedMatchingEndpoints (M i))).card≤K.degree v := by
  let S:=Finset.univ.filter (fun i=>v∈prescribedMatchingEndpoints (M i))
  have hex:∀ i∈S,∃e,e∈(M i).image prescribedArcPhysical ∧ e∈K.incidenceFinset v:=by
    intro i hi
    have hv:v∈prescribedMatchingEndpoints (M i):=(Finset.mem_filter.mp hi).2
    obtain ⟨a,ha,hv⟩:=Finset.mem_biUnion.mp hv
    let e:Sym2 V:=prescribedArcPhysical a
    have he:e∈(M i).image prescribedArcPhysical:=Finset.mem_image.mpr ⟨a,ha,rfl⟩
    refine ⟨e,he,?_⟩
    rw [SimpleGraph.incidenceFinset_eq_filter,Finset.mem_filter]
    refine ⟨hsub i he,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    simpa [e,prescribedArcPhysical,Sym2.mem_iff] using hv
  let pick:I→Sym2 V:=fun i=>if hi:i∈S then Classical.choose (hex i hi) else s(v,v)
  have hmem:∀ i∈S,pick i∈(M i).image prescribedArcPhysical ∧ pick i∈K.incidenceFinset v:=by
    intro i hi
    simpa [pick,hi] using (Classical.choose_spec (hex i hi))
  have hmap:Set.MapsTo pick (↑S:Set I) (↑(K.incidenceFinset v):Set (Sym2 V)):=by
    intro i hi;exact (hmem i hi).2
  have hinj:Set.InjOn pick (↑S:Set I):=by
    intro i hi j hj heq
    by_contra hij
    have heI:pick i∈(M i).image prescribedArcPhysical:=(hmem i hi).1
    have heJ:pick i∈(M j).image prescribedArcPhysical:=by rw [heq];exact (hmem j hj).1
    exact (Finset.disjoint_left.mp (hpair i j hij)) heI heJ
  have hc:=Finset.card_le_card_of_injOn pick hmap hinj
  rw [SimpleGraph.card_incidenceFinset_eq_degree] at hc
  exact hc
end Oberwolfach
