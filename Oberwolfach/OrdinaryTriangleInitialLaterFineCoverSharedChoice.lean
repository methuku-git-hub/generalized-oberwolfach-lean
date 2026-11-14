module

public import Oberwolfach.OrdinaryInitialTriangleFineCoverFromSharedAt
public import Oberwolfach.OrdinaryActualTraceTriangleFineCoverShared

@[expose] public section
/-! One set of selected fine-cover parameters gives the initial and every
later-history fine-cover callback before the host and sample are chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_initial_later_fine_cover_shared_choice
    (d:ℕ) (ρ₀ pmin href κ δcut ζcut εcut ζlimit εsample εvortex ε ξroot aLoad ηbal αcut pstar β:ℝ)
    (hnum:OrdinaryFixedVortexNonrootNumericAt ρ₀ pmin href κ κ κ δcut ζcut εcut ζlimit εsample εvortex)
    (hρ₀:0<ρ₀) (hε:0<ε) (hεv:ε≤εvortex) (hδ:0<δcut) (hδsmall:δcut<1/4)
    (hξ:0<ξroot) (hξEq:ξroot=min (ε/200) (aLoad^2/160)) (ha:0<aLoad) (ha1:aLoad≤1)
    (hbal:0≤ηbal) (hbalcap:ηbal≤δcut*(ρ₀/8)*ξroot/1000) (hβ:0≤β) (hβ1:β≤1/4)
    (hζcut:0≤ζcut) (hεcut:0≤εcut) (hζlimit:0≤ζlimit)
    (hδlim:δcut≤min (αcut/32) (pstar/512)) (hhref:href≤αcut*pstar/64):
    ∃mFine mInitial mLater:ℕ,1≤mFine ∧ mInitial≤mFine ∧ mLater≤mFine ∧
      OrdinaryInitialTriangleFineCoverFromSharedAt d ρ₀ pmin href κ δcut ζcut εcut ζlimit εsample ε ξroot aLoad ηbal αcut pstar β mInitial ∧
      OrdinaryActualTraceTriangleFineCoverAtLocalBalance 2 ρ₀ pmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad κ β ηbal d mLater :=by
  have hξε:ξroot≤ε/100:=by
    rw [hξEq]
    have hh:=min_le_left (ε/200) (aLoad^2/160)
    linarith
  have hξsmall:80*ξroot≤aLoad^2:=by
    rw [hξEq]
    have hh:=min_le_right (ε/200) (aLoad^2/160)
    have hs:0≤aLoad^2:=sq_nonneg aLoad
    linarith
  obtain ⟨mInitial,hmInitial,hInitial⟩:=ordinary_initial_triangle_fine_cover_from_shared_at d
    ρ₀ pmin href κ δcut ζcut εcut ζlimit εsample εvortex ε ξroot aLoad ηbal αcut pstar
    hnum hρ₀ hε hεv hδ hδsmall hξ hξε ha ha1 hξsmall hbal hbalcap hζcut hεcut hζlimit hδlim hhref β hβ hβ1
  obtain ⟨mLater,hmLater,hLater⟩:=ordinary_actual_trace_triangle_fine_cover_shared_numeric 2 (by omega)
    ρ₀ pmin href κ δcut ζcut εcut ζlimit εsample εvortex hρ₀ hδ hδsmall hnum
    ε ξroot aLoad ηbal β d hε hεv ha ha1 hξEq hbal hbalcap hβ hβ1
  exact ⟨max mInitial mLater,mInitial,mLater,le_trans hmInitial (le_max_left _ _),le_max_left _ _,le_max_right _ _,hInitial,hLater⟩
end Oberwolfach
