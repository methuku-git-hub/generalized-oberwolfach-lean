module

public import Oberwolfach.OrdinaryDeepCertificateRowMargins

@[expose] public section
/-! The row tolerances also meet the independently chosen initial matching
edit tolerance, while retaining all certificate and later-level bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_certificate_rows_with_edit
    (δcap δInitial εsample δDeep δend δedit:ℝ)
    (hcap:0<δcap) (hInitial:0<δInitial) (hsample:0<εsample)
    (hDeep:0<δDeep) (hend:0<δend) (hedit:0<δedit):
    ∃εR εH:ℝ,0<εR ∧ 0<εH ∧
      εR≤δcap ∧ εH≤δcap ∧ εR≤δInitial ∧ εH≤δInitial ∧
      εR≤εsample ∧ εH≤εsample ∧ εR≤δDeep ∧ εH≤δDeep ∧
      εR≤δend/4 ∧ εH≤δend/4 ∧ εR≤δedit ∧ εH≤δedit :=by
  obtain ⟨εR,εH,hR,hH,hRcap,hHcap,hRI,hHI,hRs,hHs,hRd,hHd,hRe,hHe⟩:=
    ordinary_deep_certificate_row_margins (min δcap δedit) δInitial εsample δDeep δend
      (lt_min hcap hedit) hInitial hsample hDeep hend
  exact ⟨εR,εH,hR,hH,hRcap.trans (min_le_left _ _),hHcap.trans (min_le_left _ _),
    hRI,hHI,hRs,hHs,hRd,hHd,hRe,hHe,hRcap.trans (min_le_right _ _),hHcap.trans (min_le_right _ _)⟩
end Oberwolfach
