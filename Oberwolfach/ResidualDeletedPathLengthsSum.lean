module

public import Oberwolfach.ResidualDeletedPathLengths

@[expose] public section
/-! The selected-run paths have total length c times the number of
selected segments, with each final path contributing cd. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem deleted_path_lengths_sum (F:SimpleGraph V) (s₁ s₂:Finset I)
    (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i∈s₁∪s₂,(P i).IsPath) (c d:ℕ) (hc:0<c)
    (hlen:∀i∈s₁∪s₂,(P i).length=c*d+4)
    (T:I→Finset ℕ) (hT:∀i∈s₂,T i⊆Finset.range d):
    (∑ z:DeletedPathIndex s₁ s₂ d T,(deletedPathWalk F s₁ s₂ u v P c d T hT z).length)=
      c*d*s₁.card+c*(∑i∈s₂,(T i).card) := by
  have hlen' := deleted_path_lengths F s₁ s₂ u v P hp c d hc hlen T hT
  change (∑ z:({i // i∈s₁} ⊕ SelectedRunIndex s₂ d T),
    (deletedPathWalk F s₁ s₂ u v P c d T hT z).length)=_
  rw [Fintype.sum_sum_type]
  have hleft:(∑ i:{i // i∈s₁},(deletedPathWalk F s₁ s₂ u v P c d T hT (.inl i)).length)=c*d*s₁.card := by
    simp only [hlen'.1,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,Nat.cast_id]
    ring
  rw [hleft]
  congr 1
  change (∑ z: (Σ i:{i // i∈s₂},{r // r∈selectedSegmentRuns d (T i.1)}),
    (deletedPathWalk F s₁ s₂ u v P c d T hT (.inr z)).length)=_
  rw [Fintype.sum_sigma]
  have hrun:∀i:{i // i∈s₂},
      (∑ r:{r // r∈selectedSegmentRuns d (T i.1)},
        (deletedPathWalk F s₁ s₂ u v P c d T hT (.inr ⟨i,r⟩)).length)=c*(T i.1).card := by
    intro i
    simp only [hlen'.2]
    calc
      _ = ∑ p∈selectedSegmentRuns d (T i.1),c*(p.2+1-p.1) := by
        exact (Finset.sum_subtype (selectedSegmentRuns d (T i.1)) (fun _=>Iff.rfl)
          (fun p:ℕ×ℕ=>c*(p.2+1-p.1))).symm
      _ = c*(T i.1).card := selected_run_scaled_lengths_sum d c (T i.1) (hT i.1 i.2)
  simp_rw [hrun]
  calc
    _ = ∑ i∈s₂,c*(T i).card := by
      exact (Finset.sum_subtype s₂ (fun _=>Iff.rfl) (fun i=>c*(T i).card)).symm
    _ = _ := by rw [Finset.mul_sum]
end Oberwolfach
