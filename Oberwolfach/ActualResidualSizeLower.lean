module

public import Oberwolfach.ResidualActualData
public import Oberwolfach.ResidualActualFullSelection
public import Oberwolfach.ActualResidualSumIndices

@[expose] public section
/-! The true residual cannot be smaller than the residual obtained by
selecting every position of every buffered path. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_residual_size_lower
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (a:ActualResidualData (K:=K) (J:=J) F):
    Fintype.card X≤a.remaining.card+(a.t.biUnion (fun j=>(a.C j).support.toFinset)).card+
      (a.c*a.d-1)*(a.s₁.card+a.s₂.card):=by
  have hh:=residual_actual_full_selection_comparison F a.s₁ a.s₂ a.hs a.u a.v a.P a.hp a.hP a.c a.d (by have hh:=a.hc;omega) a.hd a.hlen a.T a.hT a.t a.root a.C a.hcross
  dsimp only at hh
  have hrem:=hh.2.1
  have heq:=hh.1
  change _≤a.remaining.card at hrem
  omega

/-- For the sum-indexed path family, the number of parent paths is exactly
the total number of retained and raw indices. -/
theorem actual_residual_size_lower_sum_indices
    {X A B J:Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [DecidableEq J]
    {F:SimpleGraph X} (a:ActualResidualData (K:=A⊕B) (J:=J) F)
    (hs1:a.s₁=firstSumIndices) (hs2:a.s₂=secondSumIndices):
    Fintype.card X≤a.remaining.card+(a.t.biUnion (fun j=>(a.C j).support.toFinset)).card+
      (a.c*a.d-1)*(Fintype.card (A⊕B)):=by
  have h1:a.s₁.card=Fintype.card A:=by
    rw [hs1]
    simpa only [Fintype.card_coe] using (Fintype.card_congr (firstSumIndexEquiv (A:=A) (B:=B))).symm
  have h2:a.s₂.card=Fintype.card B:=by
    rw [hs2]
    simpa only [Fintype.card_coe] using (Fintype.card_congr (secondSumIndexEquiv (A:=A) (B:=B))).symm
  have hh:=actual_residual_size_lower a
  rw [h1,h2,←Fintype.card_sum] at hh
  exact hh
end Oberwolfach
