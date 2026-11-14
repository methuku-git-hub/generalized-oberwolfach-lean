module

public import Oberwolfach.OrdinaryColourZeroCorrectionBeforeSpacingShape

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_colour_zero_constructed_correction_before_spacing
    (r:ℕ) (hr:3≤r) (α pstar ω:ℝ)
    (hα:0<α) (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω):
    OrdinaryColourZeroCorrectionBeforeSpacingShape r hr α pstar ω hα hpstar hpstar1 hω :=by
  unfold OrdinaryColourZeroCorrectionBeforeSpacingShape
  obtain ⟨δ,h,εabs,εv,hδ,hδ1,hh,hεabs,hεv,hmain⟩:=
    ordinary_matching_prior_constructed_reservoir_probability_before_spacing r hr α pstar ω hα hpstar hpstar1 hω
  refine ⟨δ,h,εabs,εv,hδ,hδ1,hh,hεabs,hεv,?_⟩
  intro ξ hξ hξh d hd L hL m
  obtain ⟨a,b,hmain⟩:=hmain ξ hξ hξh d hd L hL m
  refine ⟨a,b,?_⟩
  intro t f q₀ χcol hχcol
  obtain ⟨Nabs,hNabs,hmain⟩:=hmain t f q₀
  obtain ⟨Ncol,hNcol,hcol⟩:=ordinary_colour_zero_on_prior χcol hχcol
  refine ⟨max Nabs Ncol,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hωn hUn P F D hreg hD hdegree hF π hconf hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq q hq hQ s hs hS j hj g₀ hzero
    A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB hZsmall hBsmall R _ ν E lossE μ νcoin hE
  let Prior:=fun z:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)=>
    (E z ∧ OrdinaryExpandedColourDegreeEvent P p k p₂ k₂ u z.1) ∧ OrdinaryZeroRetentionEvent π d g₀ z.1
  have hprior:1-(lossE+χcol)≤(μ.sigma ν).probability Prior:=by
    simpa only [Prior,OrdinaryExpandedColourDegreeEvent] using
      (hcol V (by omega) U Γ Color P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS g₀ hzero ν E lossE hE)
  exact hmain V U Γ Color (by omega) hωn hUn P F D hreg hD hdegree hF π hconf hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq q hq hQ s hs hS j hj
    A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB hZsmall hBsmall ν Prior (lossE+χcol) hprior
end Oberwolfach
