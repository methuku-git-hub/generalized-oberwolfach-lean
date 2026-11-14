module

public import Oberwolfach.MarkedEmptyPhysicalDeletion

@[expose] public section
/-! The empty graph has no edges for every finite edge-set instance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {V:Type} [Fintype V] [DecidableEq V]
theorem graph_bottom_edgeFinset_any_instance
    (I:Fintype (⊥:SimpleGraph V).edgeSet):
    @SimpleGraph.edgeFinset V ⊥ I=∅ := by
  ext e
  simp only [Finset.notMem_empty,iff_false]
  intro he
  have hx:e∈(⊥:SimpleGraph V).edgeSet := by
    letI := I
    exact SimpleGraph.mem_edgeFinset.mp he
  simpa using hx
end Oberwolfach
