module

public import Oberwolfach.EndpointMatchingMass

@[expose] public section

/-! Extending weights on graph edges by zero preserves every incident sum.
This makes the total functions used in finite sums a proved representation,
not an extra fractional-matching assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem graph_weighted_incidence_sum (G : SimpleGraph V) (weight : Sym2 V→ℝ) (v : V) :
    (∑ w,if G.Adj v w then weight s(v,w) else 0)=
      ∑ e∈G.edgeFinset,if v∈e then weight e else 0 := by
  have hl : (∑ w,if G.Adj v w then weight s(v,w) else 0)=
      ∑ w∈G.neighborFinset v,weight s(v,w) := by
    rw [SimpleGraph.neighborFinset_eq_filter,Finset.sum_filter]
  have hr : (∑ e∈G.edgeFinset,if v∈e then weight e else 0)=
      ∑ e∈G.incidenceFinset v,weight e := by
    rw [SimpleGraph.incidenceFinset_eq_filter,Finset.sum_filter]
  rw [hl,hr]
  apply Finset.sum_bij (fun w _=>s(v,w))
  · intro w hw
    simpa using hw
  · intro w hw z hz he
    exact Sym2.congr_right.mp he
  · intro e he
    have he' : e∈G.edgeSet ∧ v∈e := by simpa [SimpleGraph.incidenceSet] using he
    obtain ⟨w,rfl⟩:=Sym2.mem_iff_exists.mp he'.2
    exact ⟨w,by simpa using he'.1,rfl⟩
  · intro w hw;rfl

def graphEdgeWeightExtension (G : SimpleGraph V) (weight : G.edgeSet→ℝ) (e : Sym2 V) : ℝ :=
  if h:e∈G.edgeSet then weight ⟨e,h⟩ else 0

theorem graphEdgeWeightExtension_edge (G : SimpleGraph V) (weight : G.edgeSet→ℝ)
    (e : Sym2 V) (he : e∈G.edgeSet) : graphEdgeWeightExtension G weight e=weight ⟨e,he⟩ := by
  simp [graphEdgeWeightExtension,he]

theorem graphEdgeWeightExtension_nonedge (G : SimpleGraph V) (weight : G.edgeSet→ℝ)
    (e : Sym2 V) (he : e∉G.edgeSet) : graphEdgeWeightExtension G weight e=0 := by
  simp [graphEdgeWeightExtension,he]

theorem graphEdgeWeightExtension_incident (G : SimpleGraph V) (weight : G.edgeSet→ℝ) (v : V) :
    (∑ w,graphEdgeWeightExtension G weight s(v,w))=
      ∑ e:G.edgeSet,if v∈e.val then weight e else 0 := by
  have hleft : (∑ w,graphEdgeWeightExtension G weight s(v,w))=
      ∑ w,if G.Adj v w then graphEdgeWeightExtension G weight s(v,w) else 0 := by
    apply Finset.sum_congr rfl
    intro w hw
    by_cases h:G.Adj v w
    · simp [h]
    · simp [h,graphEdgeWeightExtension]
  rw [hleft,graph_weighted_incidence_sum]
  have hh:=Finset.sum_subtype (F:=inferInstance) (p:=fun e:Sym2 V=>e∈G.edgeSet)
    G.edgeFinset (fun e=>by simp) (fun e=>if v∈e then graphEdgeWeightExtension G weight e else 0)
  rw [hh]
  apply Finset.sum_congr rfl
  intro e he
  rw [graphEdgeWeightExtension_edge G weight e.val e.property]

end Oberwolfach
