module

public import Oberwolfach.MarkedSpokeToleranceMonotone

@[expose] public section
/-! Convert full-parent retained estimates and raw-retained discrepancy
bounds to the four record tolerances on their original row and column domains. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_parent_neighbourhood_record_inputs
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (p k:ℝ)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (e ζ κ:ℝ)
    (he:0≤e) (heκ:e≤κ/4) (hζκ:ζ≤κ/4) (hUV:Fintype.card U≤Fintype.card V)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hrow:MarkedRowsWithSpokes P π d h Finset.univ p k q s g j (e*Fintype.card V) σ H)
    (hidx:MarkedIndicesWithSpokes π d h Finset.univ q s g j (e*Fintype.card U) σ H)
    (hrowchange:∀ b x,(∑ u,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)≤ζ*Fintype.card U)
    (hcolchange:∀ b u,(∑ x,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)≤ζ*Fintype.card V):
    MarkedRowsWithSpokes P π d h Finset.univ p k q s g j ((κ/4)*Fintype.card V) σ H ∧
    MarkedIndicesWithSpokes π d h Finset.univ q s g j ((κ/4)*Fintype.card V) σ H ∧
    (∀ b x,(∑ u,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card U) ∧
    (∀ b u,(∑ x,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card V):=by
  have hcard:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hUV
  have hr:e*Fintype.card V≤(κ/4)*Fintype.card V:=mul_le_mul_of_nonneg_right heκ (Nat.cast_nonneg _)
  have hi:e*Fintype.card U≤(κ/4)*Fintype.card V:=
    (mul_le_mul_of_nonneg_left hcard he).trans hr
  refine ⟨marked_rows_with_spokes_tolerance_mono P π d h Finset.univ p k q s g j _ _ σ H hr hrow,
    marked_indices_with_spokes_tolerance_mono π d h Finset.univ q s g j _ _ σ H hi hidx,?_,?_⟩
  · intro b x
    exact (hrowchange b x).trans (mul_le_mul_of_nonneg_right hζκ (Nat.cast_nonneg _))
  · intro b u
    exact (hcolchange b u).trans (mul_le_mul_of_nonneg_right hζκ (Nat.cast_nonneg _))
end Oberwolfach
