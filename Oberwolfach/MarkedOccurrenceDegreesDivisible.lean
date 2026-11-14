module

public import Oberwolfach.MarkedMatrixDivisibility

@[expose] public section
/-! Exact occurrence-degree identities give the four finite divisibility
conditions needed by the fixed absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_occurrence_degrees_divisible
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (m:ℕ)
    (hH:∀v u,¬(H₀ v u∧HK v u))
    (hdir:∀v,occurrenceDegree (Sum.elim tail ktail) v=occurrenceDegree (Sum.elim head khead) v)
    (hmark:∀v,occurrenceDegree khead v=∑u,if HK v u then (1:ℝ) else 0)
    (hrow:∀v,occurrenceDegree (Sum.elim tail ktail) v=
      (∑u,if H₀ v u then (1:ℝ) else 0)+(∑u,if HK v u then (1:ℝ) else 0))
    (hhub:∀u,(∑v,if H₀ v u then (1:ℝ) else 0)=(m:ℝ)*(∑v,if HK v u then (1:ℝ) else 0)):
    MarkedRemainderDivisible tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2)) m:=by
  apply marked_matrix_balanced_divisible tail head ktail khead H₀ HK m hH
  unfold TypedMatrixBalanced
  refine ⟨?_,?_,?_,?_⟩
  · intro v
    have hh:=hrow v
    simp only [occurrenceDegree_sum] at hh
    have hr:((∑x,occurrenceMultiplicity tail head v x)+(∑x,occurrenceMultiplicity ktail khead v x):ℕ)=(∑u,relationMultiplicity H₀ v u)+(∑u,relationMultiplicity HK v u):=by
      apply Nat.cast_injective (R:=ℝ)
      simpa only [Nat.cast_add,Nat.cast_sum,occurrenceMultiplicity_row,relationMultiplicity_cast] using hh
    exact hr
  · intro v
    have hh:occurrenceDegree (Sum.elim head khead) v=
        (∑u,if H₀ v u then (1:ℝ) else 0)+(∑u,if HK v u then (1:ℝ) else 0):=(hdir v).symm.trans (hrow v)
    simp only [occurrenceDegree_sum] at hh
    apply Nat.cast_injective (R:=ℝ)
    simpa only [Nat.cast_add,Nat.cast_sum,occurrenceMultiplicity_col,relationMultiplicity_cast] using hh
  · intro v
    apply Nat.cast_injective (R:=ℝ)
    simpa only [Nat.cast_sum,occurrenceMultiplicity_col,relationMultiplicity_cast] using hmark v
  · intro u
    apply Nat.cast_injective (R:=ℝ)
    simpa only [Nat.cast_sum,Nat.cast_mul,relationMultiplicity_cast] using hhub u
end Oberwolfach
