module

public import Oberwolfach.FactorClassAssignment
public import Oberwolfach.PreparationWeightsFromAllowedThreshold

@[expose] public section
/-! In the triangle branch, the original allowed-length assumptions imply
that the ambient threshold dominates the triangle threshold. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_class_allowed_threshold
    {n K:ℕ} (hn:0<n) (hK:0<K) (F:SimpleGraph (Fin n))
    (hF:F.IsRegularOfDegree 2) (Allowed:Set ℕ) (hAllowed:AllowedCycleLengths F Allowed)
    (i:Fin K) (hclass:factorPreparationClass F K=some i) (htri:i.val+1=3):
    cycleThreshold 3≤allowedThreshold Allowed :=by
  have hlen: i.val+1∈Allowed:=((factor_preparation_class hn F hF Allowed hAllowed K hK).2 i hclass).2.1
  have hbdd:BddAbove (cycleThreshold '' Allowed):=by
    refine ⟨1,?_⟩
    rintro x ⟨s,hs,rfl⟩
    exact cycleThreshold_le_one s
  apply le_csSup hbdd
  exact ⟨3,by simpa [htri] using hlen,rfl⟩
end Oberwolfach
