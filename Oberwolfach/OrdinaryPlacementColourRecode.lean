module

public import Oberwolfach.MarkedExpandedPhysicalLaw

@[expose] public section
/-! Reassign the previously unused sampled colour to the ordinary directed
placement colour, keeping the underlying physical edge and its orientation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryPlacementColourRecode (z:Fin 6×Bool):Fin 6×Bool:=
  (if z.1=4 then 0 else z.1,z.2)

theorem ordinary_placement_colour_recode_law
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1):
    (FiniteLaw.categoricalDirection (markedExpandedPhysicalProbability p k p₂ k₂ u)
      (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (markedExpandedPhysicalProbability_sum p k p₂ k₂ u)).map ordinaryPlacementColourRecode =
    FiniteLaw.categoricalDirection (markedExpandedPhysicalProbability (p+u/2) k p₂ k₂ 0)
      (markedExpandedPhysicalProbability_nonneg (p+u/2) k p₂ k₂ 0 (by positivity) hk hp₂ hk₂ (by norm_num) (by linarith))
      (markedExpandedPhysicalProbability_sum (p+u/2) k p₂ k₂ 0) :=by
  apply finiteLaw_ext
  intro z
  rcases z with ⟨a,b⟩
  fin_cases a <;> cases b <;>
    simp [FiniteLaw.map,FiniteLaw.categoricalDirection,markedExpandedPhysicalProbability,
      ordinaryPlacementColourRecode,Fintype.sum_prod_type,Fin.sum_univ_succ,Fintype.sum_bool] <;> ring
end Oberwolfach
