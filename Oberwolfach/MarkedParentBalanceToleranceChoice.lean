module

public import Oberwolfach.MarkedInnerDeepBalanceOrderedCaps

@[expose] public section
/-! The parent balance event can use positive tolerances below any earlier
cap while leaving the two margins required by the corrected level chain. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_parent_balance_tolerance_choice
    (r:ℕ) (etaBal x upper:ℝ) (hη:0<etaBal) (hx:0<x) (hupper:0<upper):
    ∃epsBal ζBal:ℝ,0<epsBal ∧ 0<ζBal ∧ epsBal≤upper ∧ ζBal≤upper ∧
      epsBal+((r+4)+2:ℕ)*ζBal≤etaBal/2 ∧
      epsBal+((r+4)+2:ℕ)*ζBal≤x/4 :=by
  let m:ℝ:=((r+4)+2:ℕ)
  let T:ℝ:=min (etaBal/2) (x/4)
  have hT:0<T:=by dsimp [T];positivity
  have hm:0<m+1:=by dsimp [m];positivity
  let δ:ℝ:=min upper (T/(2*(m+1)))
  have hδ:0<δ:=by dsimp [δ];positivity
  have hδupper:δ≤upper:=min_le_left _ _
  have hδT:δ≤T/(2*(m+1)):=min_le_right _ _
  have hsum:δ+m*δ≤T:=by
    have hh:δ*(2*(m+1))≤T:=(le_div_iff₀ (by positivity)).mp hδT
    nlinarith
  have hTη:T≤etaBal/2:=min_le_left _ _
  have hTx:T≤x/4:=min_le_right _ _
  refine ⟨δ,δ,hδ,hδ,hδupper,hδupper,?_,?_⟩
  · exact hsum.trans hTη
  · exact hsum.trans hTx
end Oberwolfach
