module

public import Oberwolfach.LongRegularHostNumericInputs

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- A reference margin may be chosen from the original margin before the
host, its order, and the allowed cycle-length set are specified. -/
theorem long_original_host_reference_margin (α:ℝ) (hα:0<α):
    ∃ αRef:ℝ, 0<αRef ∧ 2*αRef≤1 ∧ 2*αRef≤α ∧
      ∀(n D:ℕ),0<n→∀(U:Type) [Fintype U] (Allowed:Set ℕ),
      Allowed.Nonempty → (∀r∈Allowed,3≤r) →
      ∀G:SimpleGraph (Fin n),G.IsRegularOfDegree D →
      (allowedThreshold Allowed+α)*n≤(D:ℝ) →
      0<D ∧ (n:ℝ)/2≤D ∧ (D:ℝ)≤2*n ∧
      (1/2+2*αRef)*n≤(D:ℝ) ∧
      (∀v,|(G.degree v:ℝ)-D|≤(0:ℝ)*n) ∧
      initialIndexDensity U D*(D:ℝ)=2*Fintype.card U :=by
  refine ⟨min α 1 / 2,by positivity,?_,?_,?_⟩
  · linarith [min_le_right α (1:ℝ)]
  · linarith [min_le_left α (1:ℝ)]
  intro n D hn U _ Allowed hAllowed hvalid G hreg hmin
  obtain ⟨hD,hlo,hhi,hmargin,hdeg,hdensity⟩:=
    long_regular_host_numeric_inputs n D hn U Allowed hAllowed hvalid α hα G hreg hmin
  refine ⟨hD,hlo,hhi,?_,hdeg,hdensity⟩
  have hcoeff:(1/2:ℝ)+2*(min α 1/2)≤1/2+α:=by linarith [min_le_left α (1:ℝ)]
  exact (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg n)).trans hmargin
end Oberwolfach
