module

public import Oberwolfach.ActualReservedPairListsFromCommonIndices
public import Oberwolfach.ActualReservedOuterCodegreeLoss

@[expose] public section
/-! The manuscript's common-spoke estimate, the small inner set and the
bounded absorber yield the exact matching-list slack for all bad edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_outer_codegree_common_slack
    (α:ℝ) (hα:0<α) (B:ℕ):
    ∃ N:ℕ,∀ (V I:Type) [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I],
    N≤Fintype.card V→∀(C:Finset (Finset V⊕(V×I))) (Outer:I→Finset V) (Inner:Finset I)
    (K:SimpleGraph V) (ε:ℝ),ε≤α/2→(Inner.card:ℝ)≤ε*Fintype.card V→C.card≤B→
    (∀x y,x≠y→2*α*Fintype.card V≤
      ((((Finset.univ:Finset I).filter (fun i=>x∈Outer i))∩
        ((Finset.univ:Finset I).filter (fun i=>y∈Outer i))).card:ℝ))→
    ∀e∈K.edgeFinset,α*Fintype.card V+Inner.card+2*C.card≤
      ((commonOuterPairIndices Outer e).card:ℝ) :=by
  obtain ⟨N,hN⟩:=actual_reserved_outer_codegree_loss α hα B
  refine ⟨N,?_⟩
  intro V I _ _ _ _ hn C Outer Inner K ε hε hInner hC hPairs
  have hloss:=hN (Fintype.card V) hn Inner.card C.card ε hε hInner hC
  exact actual_common_outer_pair_slack_from_codegrees C Outer Inner K α hPairs hloss
end Oberwolfach
