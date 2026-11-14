module

public import Oberwolfach.OrdinaryAssignedSamplingParameters

@[expose] public section
/-! Name the manuscript's actual class frequencies and sampling probabilities.
The definitions retain the same reserved fraction and pruning thresholds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {n:ℕ} {U:Type} [Fintype U]

def ordinaryAssignedFraction (F:U→SimpleGraph (Fin n))
    (hF:∀w,(F w).IsRegularOfDegree 2) (K:ℕ) (w:U) (j:Option (Fin K)):ℝ :=
  ((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=j)).card:ℝ)/n

def ordinaryAssignedLongWeight (F:U→SimpleGraph (Fin n))
    (hF:∀w,(F w).IsRegularOfDegree 2) (K:ℕ) (θ c:ℝ) (w:U):ℝ :=
  let x:=ordinaryAssignedFraction F hF K w none
  (1-θ)*(if x<θ/100 then 0 else x)/c

def ordinaryAssignedShortWeight (F:U→SimpleGraph (Fin n))
    (hF:∀w,(F w).IsRegularOfDegree 2) (K:ℕ) (i₀:Fin K) (s θ c:ℝ) (w:U):ℝ :=
  let a:=ordinaryAssignedLongWeight F hF K θ c w
  let f:=fun i:Fin K=>ordinaryAssignedFraction F hF K w (some i)-(if i=i₀ then s else 0)
  let kept:=∑i:Fin K,(if f i<θ/(100*(K:ℝ)) then 0 else f i)
  (c-1)*a+(1-θ)*kept

def ordinaryAssignedMarkedProbability (F:U→SimpleGraph (Fin n))
    (hF:∀w,(F w).IsRegularOfDegree 2) (K:ℕ) (θ c:ℝ) (w:U) (j:Bool):ℝ :=
  if j then ordinaryAssignedLongWeight F hF K θ c w else 0

def ordinaryAssignedSpokeProbability (F:U→SimpleGraph (Fin n))
    (hF:∀w,(F w).IsRegularOfDegree 2) (K:ℕ) (i₀:Fin K) (s θ c:ℝ) (w:U) (j:Bool):ℝ :=
  if j then ordinaryAssignedShortWeight F hF K i₀ s θ c w else s
end Oberwolfach
