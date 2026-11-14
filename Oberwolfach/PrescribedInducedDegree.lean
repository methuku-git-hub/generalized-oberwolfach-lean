module

public import Oberwolfach.Definitions

@[expose] public section
/-! Restricting a source graph to its assigned vertices does not increase
its degrees. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_induced_degree_le (Q:SimpleGraph X) (A:Finset X)
    (x:{v // v∈A}):
    letI : DecidableRel (Q.induce (↑A:Set X)).Adj := fun _ _=>Classical.propDecidable _;
    (Q.induce (↑A:Set X)).degree x≤Q.degree x.1 := by
  letI : DecidableRel (Q.induce (↑A:Set X)).Adj := fun _ _=>Classical.propDecidable _
  have hsub:((Q.induce (↑A:Set X)).neighborFinset x).map (Function.Embedding.subtype (fun v=>v∈A))⊆Q.neighborFinset x.1:=by
    intro y hy
    obtain ⟨z,hz,rfl⟩:=Finset.mem_map.mp hy
    simp only [SimpleGraph.mem_neighborFinset] at hz ⊢
    exact hz
  have hc:=Finset.card_le_card hsub
  simpa only [Finset.card_map,SimpleGraph.card_neighborFinset_eq_degree] using hc
end Oberwolfach
