module

public import Oberwolfach.OrdinaryReferenceCertificateGapChoices

@[expose] public section
/-! Choose the induced-cut and root-reserve scales from the original
positive cut, sampling and parent margins. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_parent_deep_cut_scale_choices
    (αcut pstar h:ℝ) (hα:0<αcut) (hp:0<pstar) (hh:0<h):
    ∃href δlimit geomCap:ℝ,0<href ∧ href≤αcut*pstar/64 ∧
      0<δlimit ∧ δlimit≤min (αcut/32) (pstar/512) ∧
      0<geomCap ∧ 2*geomCap≤h/2 :=by
  let href:=αcut*pstar/128
  let δlimit:=min (αcut/64) (pstar/1024)
  let geomCap:=h/8
  have href0:0<href:=by dsimp [href];positivity
  have hrefBound:href≤αcut*pstar/64:=by dsimp [href];nlinarith [mul_pos hα hp]
  have hδ:0<δlimit:=by dsimp [δlimit];positivity
  have hδa:δlimit≤αcut/64:=min_le_left _ _
  have hδp:δlimit≤pstar/1024:=min_le_right _ _
  have hδBound:δlimit≤min (αcut/32) (pstar/512):=by
    apply le_min <;> linarith
  exact ⟨href,δlimit,geomCap,href0,hrefBound,hδ,hδBound,by dsimp [geomCap];positivity,by dsimp [geomCap];linarith⟩
end Oberwolfach
