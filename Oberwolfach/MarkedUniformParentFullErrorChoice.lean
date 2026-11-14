module

public import Oberwolfach.MarkedUniformParentErrorChoice

@[expose] public section
/-! One parent-event error meets both active and wider load bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_uniform_parent_full_error_choice
    (r:ℕ) (κ theta x eta tstar hIcut Cparent Clocal Cwide:ℝ)
    (tolRef ζActive τParent tolParent ζParent τ tolLocal ζLocal ζWide rowErr ζRow ζCut ζCfg ζCommon:ℝ)
    (h0:0<tolRef) (h1:0<ζActive) (h2:0<τParent) (h3:0<tolParent) (h4:0<ζParent) (h5:0<τ) (h6:0<tolLocal) (h7:0<ζLocal) (h8:0<ζWide) (h9:0<rowErr) (h10:0<ζRow) (h11:0<ζCut) (h12:0<ζCfg) (h13:0<ζCommon) 
    (hCp:0≤Cparent) (hCl:0≤Clocal) (hCw:0≤Cwide)
    (hκref:tolRef+(r+12:ℕ)*ζActive≤κ/4)
    (hxref:tolRef+(r+12:ℕ)*ζActive≤x/2)
    (hκp:τParent+tolParent+Cparent*ζParent≤κ/4)
    (hθp:τParent+tolParent+Cparent*ζParent≤theta/4)
    (hlocal:τ+tolLocal+Clocal*ζLocal≤eta/4)
    (hwide:τ+tolLocal+Cwide*ζWide≤eta/4)
    (hrow:rowErr+ζRow≤tstar/8)
    (hcut:2*hIcut≤tstar/8-ζCut):
    ∃ δ:ℝ,0<δ ∧ δ≤ζCfg ∧ δ≤ζCommon ∧ δ≤ζCut ∧ δ≤κ/4 ∧
      δ+(r+12:ℕ)*δ≤κ/4 ∧ δ+(r+12:ℕ)*δ≤x/2 ∧
      δ+δ+Cparent*δ≤κ/4 ∧ δ+δ+Cparent*δ≤theta/4 ∧
      δ+δ+Clocal*δ≤eta/4 ∧ δ+δ+Cwide*δ≤eta/4 ∧
      δ+δ≤tstar/8 ∧ 2*hIcut≤tstar/8-δ := by
  have hp:∀ z∈[tolRef,ζActive,τParent,tolParent,ζParent,τ,tolLocal,ζLocal,ζWide,rowErr,ζRow,ζCut,ζCfg,ζCommon],(0:ℝ)<z:=by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro z hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals assumption
  obtain ⟨δ,hδ,hbelow⟩:=marked_positive_list_common_lower [tolRef,ζActive,τParent,tolParent,ζParent,τ,tolLocal,ζLocal,ζWide,rowErr,ζRow,ζCut,ζCfg,ζCommon] hp
  have hd0:δ≤tolRef:=hbelow tolRef (by simp)
  have hd1:δ≤ζActive:=hbelow ζActive (by simp)
  have hd2:δ≤τParent:=hbelow τParent (by simp)
  have hd3:δ≤tolParent:=hbelow tolParent (by simp)
  have hd4:δ≤ζParent:=hbelow ζParent (by simp)
  have hd5:δ≤τ:=hbelow τ (by simp)
  have hd6:δ≤tolLocal:=hbelow tolLocal (by simp)
  have hd7:δ≤ζLocal:=hbelow ζLocal (by simp)
  have hd8:δ≤ζWide:=hbelow ζWide (by simp)
  have hd9:δ≤rowErr:=hbelow rowErr (by simp)
  have hd10:δ≤ζRow:=hbelow ζRow (by simp)
  have hd11:δ≤ζCut:=hbelow ζCut (by simp)
  have hd12:δ≤ζCfg:=hbelow ζCfg (by simp)
  have hd13:δ≤ζCommon:=hbelow ζCommon (by simp)
  have hr:0≤((r+12:ℕ):ℝ):=by positivity
  have h1:=mul_le_mul_of_nonneg_left hd1 hr
  have h2:=mul_le_mul_of_nonneg_left hd4 hCp
  have h3:=mul_le_mul_of_nonneg_left hd7 hCl
  have h4:=mul_le_mul_of_nonneg_left hd8 hCw
  have h5:0≤Cparent*δ:=mul_nonneg hCp hδ.le
  refine ⟨δ,hδ,hd12,hd13,hd11,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith
end Oberwolfach
