module

public import Oberwolfach.ClassCorrectionFromCommonEvent
public import Oberwolfach.ExpandedClassDiscrepancyMargins
public import Oberwolfach.ClassRoutingFitsDeletion

@[expose] public section
/-! Choose the class error tolerances before the order, and obtain a protected
balanced class orientation whose correction fits the original deletion budget. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance orderedMarginsFin (n:ℕ):DecidableEq (Fin n):=fun a b=>Classical.propDecidable (a=b)
local instance (priority := 2000) orderedMarginsSix : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem class_correction_ordered_margins (α p δ:ℝ) (hα:0<α) (hp:0<p) (hδ:0<δ):
    ∃c:ℝ,0<c ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ {U Γ Color:Type} [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
      (P S Protected:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
      (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)
      (mass:Fin 6→ℝ) (ρ D ε ξ err f:ℝ),
    0≤ρ→ρ≤1→0≤ε→ε≤c/2→0≤ξ→ξ≤min (c/4) (δ/16)→0≤f→
    f≤(α*p^2/16)*n→S.IsRegularOfDegree (2*m)→
    (∑a∈({0,1,2,3,4}:Finset (Fin 6)),mass a)=ρ→ρ*D=2*m→
    (∀v,|(P.degree v:ℝ)-D|≤ε*n)→
    (∀a v,|((∑w,sampledColourOrientation P (fun e=>σ (Sum.inl e)) a v w:ℕ):ℝ)-
      mass a/2*P.degree v|≤(n:ℝ)^(3/5:ℝ))→
    (∀v,((changed ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
    (∀x y,Protected.Adj x y→(S.Adj x y↔(longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y))→
    (∀v,(Protected.degree v:ℝ)≤f)→
    (∀v,(1/2+α)*(n:ℝ)≤P.degree v)→
    (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-err≤
      ((Finset.univ.filter (fun z=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x z ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false z y)).card:ℝ))→
    err+2*(ξ*n)≤α*p^2*n→
    ∃M:Fin n→Fin n→ℕ,
      (∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
      (∀v,(∑w,M v w)=m ∧ (∑w,M w v)=m) ∧
      (∀v,((orientationDisagreementGraph (longPhysicalStateGraph P σ {0,1,2,3,4})
        (fun e=>(σ (Sum.inl e)).2) M).degree v:ℝ)≤δ*n) ∧
      (∀x y,(orientationDisagreementGraph (longPhysicalStateGraph P σ {0,1,2,3,4})
        (fun e=>(σ (Sum.inl e)).2) M).Adj x y→¬Protected.Adj x y):=by
  have hβ:0<α*p^2:=by positivity
  obtain ⟨q,c,hq,hc,N₁,hN₁pos,hN₁⟩:=class_routing_fits_deletion (α*p^2) δ hβ hδ
  obtain ⟨N₂,hN₂⟩:=eventually_expanded_class_discrepancy c hc
  refine ⟨c,hc,max N₁ N₂,le_trans hN₁pos (le_max_left _ _),?_⟩
  intro n hn U Γ Color _ _ _ _ P S Protected π d m σ mass ρ D ε ξ err f hρ hρhi hε hεhi hξ hξhi hf hfhi hreg hmass hsize hdegree hcol hedit hprotected hforbid hmin htest hsupply
  have hnN₁:N₁≤n:=(le_max_left _ _).trans hn
  have hnN₂:N₂≤n:=(le_max_right _ _).trans hn
  have hnpos:0<n:=by omega
  have hn0:0≤(n:ℝ):=Nat.cast_nonneg n
  have hξc:ξ≤c/4:=(hξhi.trans (min_le_left _ _))
  have hξδ:ξ≤δ/16:=(hξhi.trans (min_le_right _ _))
  let a:=5*(n:ℝ)^(3/5:ℝ)+ρ/2*(ε*n)+ξ*n
  have ha:0≤a:=by dsimp [a];positivity
  have hac:a≤c*n:=hN₂ n hnN₂ ρ ε ξ hρ hρhi hε hεhi hξc
  have hξn:ξ*n≤(δ/16)*n:=mul_le_mul_of_nonneg_right hξδ hn0
  obtain ⟨L,hL,hrout,hcorr⟩:=hN₁ n hnN₁ a f (ξ*n) (α*p^2/16) ha hac hfhi (le_refl _) hξn
  have hmin':∀v,(1/2+α)*(Fintype.card (Fin n):ℝ)≤P.degree v:=by simpa using hmin
  have hsupply':err+2*(ξ*n)≤α*p^2*Fintype.card (Fin n):=by simpa using hsupply
  have hrout':(Fintype.card (Fin n):ℝ)*
      (5*(n:ℝ)^(3/5:ℝ)+ρ/2*(ε*n)+ξ*n)/L+
      2*(5*(n:ℝ)^(3/5:ℝ)+ρ/2*(ε*n)+ξ*n)+4*L+2*f<α*p^2*Fintype.card (Fin n):=by
    simpa [a] using hrout
  obtain ⟨M,hphys,hdegrees,hbound,havoid⟩:=class_correction_from_common_event P S Protected π d m L σ mass ρ D
    ((n:ℝ)^(3/5:ℝ)) (ξ*n) (ε*n) α p err f hreg (by simpa using hnpos) hL hρ
    (by positivity) (by positivity) (by positivity) hα hp hf hmass hsize hdegree hcol hedit hprotected hforbid hmin' htest hsupply' hrout'
  refine ⟨M,hphys,hdegrees,?_,havoid⟩
  intro v
  exact (hbound v).trans (by simpa [a] using hcorr)
end Oberwolfach
