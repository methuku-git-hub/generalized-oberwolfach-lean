module

public import Oberwolfach.OrdinaryAssignedClassRecipe

@[expose] public section
/-! Exact marked-class interval and spoke probabilities from the manuscript's
component frequencies. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U]

def longAssignedApproxMarkedWeight (F:U→SimpleGraph (Fin n))
    (hF:∀u,(F u).IsRegularOfDegree 2) (K m:ℕ) (θ:ℝ) (u:U):ℝ:=
  (1-θ)*ordinaryAssignedFraction F hF K u none/((m:ℝ)+1)-(1/100)/(m:ℝ)

def longAssignedApproxOrdinaryWeight (F:U→SimpleGraph (Fin n))
    (hF:∀u,(F u).IsRegularOfDegree 2) (K m:ℕ) (θ:ℝ) (u:U):ℝ:=
  let a:=longAssignedApproxMarkedWeight F hF K m θ u
  (m:ℝ)*a+(1-θ)*∑i:Fin K,
    (if θ/(100*(K:ℝ))≤ordinaryAssignedFraction F hF K u (some i)
      then ordinaryAssignedFraction F hF K u (some i) else 0)

def longAssignedIntervalProbability (F:U→SimpleGraph (Fin n))
    (hF:∀u,(F u).IsRegularOfDegree 2) (K m:ℕ) (θ:ℝ) (u:U) (j:Bool):ℝ:=
  if j then longAssignedApproxMarkedWeight F hF K m θ u else (1/100)/(m:ℝ)

def longAssignedSpokeProbability (F:U→SimpleGraph (Fin n))
    (hF:∀u,(F u).IsRegularOfDegree 2) (K m:ℕ) (θ:ℝ) (u:U) (j:Bool):ℝ:=
  if j then longAssignedApproxOrdinaryWeight F hF K m θ u else 1/100
end Oberwolfach
