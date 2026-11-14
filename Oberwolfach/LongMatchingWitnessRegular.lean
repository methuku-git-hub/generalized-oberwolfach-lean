module

public import Oberwolfach.LongEveryClassSameDeletionReady

@[expose] public section
/-! The balanced matching orientation already certifies the degree of its
selected class, so reconstruction needs no independent regularity premise. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_matching_witness_regular
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (P S Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n))
    (K:ℕ) (θ Dmatch alpha γ eps βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (M:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ P π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C S M Del):
    S.IsRegularOfDegree (2*Fintype.card U) :=by
  intro v
  calc
    S.degree v = ∑x:Fin n,if S.Adj v x then 1 else 0 := by
      unfold SimpleGraph.degree SimpleGraph.neighborFinset SimpleGraph.neighborSet
      rw [Finset.sum_boole, Set.toFinset_ofPred]
      congr 1
    _ = ∑x:Fin n,(M v x+M x v) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (hw.1 v x).symm
    _ = Fintype.card U+Fintype.card U := by
      rw [Finset.sum_add_distrib,(hw.2.1 v).1,(hw.2.1 v).2]
    _ = 2*Fintype.card U := by omega
end Oberwolfach
