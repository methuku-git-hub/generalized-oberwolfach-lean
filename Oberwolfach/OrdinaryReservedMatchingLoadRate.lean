module

public import Oberwolfach.OrdinaryReservedPlacementHierarchy

@[expose] public section
/-! The matching row error can be shrunk after the early placement rates are
chosen, so the boundary-based prescribed load fits the same tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_reserved_matching_load_rate
    (δ κ:ℝ) (hδ:0<δ) (hκ:0<κ):
    ∃κ':ℝ,0<κ' ∧ κ'≤κ ∧ κ'≤δ/64 ∧
      ∀(a γ n:ℝ),0≤n→a≤κ'→γ≤κ'→2*((max a γ)*n)≤δ*n/8 :=by
  let κ':ℝ:=min κ (δ/64)
  have hp:0<κ':=by dsimp [κ'];positivity
  have hk:κ'≤κ:=min_le_left _ _
  have hd:κ'≤δ/64:=min_le_right _ _
  refine ⟨κ',hp,hk,hd,?_⟩
  intro a γ n hn ha hγ
  have hm:max a γ≤κ':=max_le ha hγ
  have hh:=mul_le_mul_of_nonneg_right hm hn
  have hh':=mul_le_mul_of_nonneg_right hd hn
  nlinarith
end Oberwolfach
