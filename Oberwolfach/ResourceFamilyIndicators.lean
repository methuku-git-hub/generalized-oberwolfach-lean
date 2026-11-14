module

public import Oberwolfach.ResourceDecompositionCounts

@[expose] public section

/-! Convert an indexed family of pairwise edge-disjoint actual pieces into
its physical edge set and exact integer indicators. -/
set_option autoImplicit false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X W I:Type} [DecidableEq X] [DecidableEq W] [Fintype I] [DecidableEq I]

 theorem resource_indexed_family_decomposition (R:W→Finset X) (C:I→W)
    (hC:∀ i j,i≠j→Disjoint (R (C i)) (R (C j))):
    HasResourceDecomposition R (Finset.univ.biUnion (fun i=>R (C i))):=by
  exact resource_decomposition_biUnion R _ Finset.univ
    (fun i _=>resource_decomposition_singleton R (C i)) (fun i _ j _=>hC i j)

 theorem resource_indexed_family_int_indicator (R:W→Finset X) (C:I→W)
    (hC:∀ i j,i≠j→Disjoint (R (C i)) (R (C j))) (e:X):
    (∑ i,if e∈R (C i) then (1:ℤ) else 0)=
      if e∈Finset.univ.biUnion (fun i=>R (C i)) then 1 else 0:=by
  have hh:=resource_decomposition_indicator (fun i=>R (C i)) Finset.univ _
    (fun i _ j _=>hC i j) rfl e
  exact_mod_cast hh

 theorem resource_indexed_family_supported {V:Type} (R:W→Finset X) (C:I→W)
    (S:V→X→Prop) (v:V) (hC:∀ i,∀ e∈R (C i),S v e):
    ∀ e∈Finset.univ.biUnion (fun i=>R (C i)),S v e:=by
  intro e he
  obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
  exact hC i e hi

end Oberwolfach
