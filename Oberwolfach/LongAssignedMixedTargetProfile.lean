module

public import Oberwolfach.LongAssignedCombinedCoefficients

@[expose] public section
/-! The actual long-class coefficients as functions on the four types of
marked resource. The ordinary families contribute zero on marked resources. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U]

def longAssignedMixedTarget (F:U→SimpleGraph (Fin n))
    (hF:∀u,(F u).IsRegularOfDegree 2) (K m:ℕ) (θ D p k:ℝ):
    Option (Fin K)→(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→ℝ
  | none, .inl (.inl _) => (m:ℝ)*k/p
  | none, .inl (.inr _) => 1
  | none, .inr (false,_,u) => (m:ℝ)*longAssignedApproxMarkedWeight F hF K m θ u/
      longAssignedApproxOrdinaryWeight F hF K m θ u
  | none, .inr (true,_,_) => 1
  | some i, .inl (.inl _) =>
      (∑u,longAssignedKeptOrdinaryContribution F hF K θ i u)/(D*p)
  | some _, .inl (.inr _) => 0
  | some i, .inr (false,_,u) => longAssignedKeptOrdinaryContribution F hF K θ i u/
      longAssignedApproxOrdinaryWeight F hF K m θ u
  | some _, .inr (true,_,_) => 0

theorem long_assigned_mixed_target_sum_one
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ D p k:ℝ) (hD:0<D) (hp:0<p)
    (hb:∀u,0<longAssignedApproxOrdinaryWeight F hF K m θ u)
    (hpdef:p=(∑u,longAssignedApproxOrdinaryWeight F hF K m θ u)/D)
    (hkdef:k=(∑u,longAssignedApproxMarkedWeight F hF K m θ u)/D)
    (root:((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)):
    ∑i,longAssignedMixedTarget F hF K m θ D p k i root=1 := by
  have hh:=long_assigned_approximate_coefficients_sum_one F hF K m θ D p k hD hp hb hpdef hkdef
  cases root with
  | inl e =>
    cases e with
    | inl e => simpa [Fintype.sum_option,longAssignedMixedTarget] using hh.2
    | inr e => simp [Fintype.sum_option,longAssignedMixedTarget]
  | inr a =>
    rcases a with ⟨b,v,u⟩
    cases b
    · simpa [Fintype.sum_option,longAssignedMixedTarget] using hh.1 u
    · simp [Fintype.sum_option,longAssignedMixedTarget]
end Oberwolfach
