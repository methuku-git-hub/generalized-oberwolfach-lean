module

public import Oberwolfach.ClassCorrectionOrderedMargins
public import Oberwolfach.ClassTwoPathSupplyMargins

@[expose] public section
/-! The actual common-event two-path test supplies the ordered class correction
after the spacing and error rates are chosen. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance sampledMarginsFin (n:ℕ):DecidableEq (Fin n):=fun a b=>Classical.propDecidable (a=b)
local instance (priority := 2000) sampledMarginsSix : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem class_correction_from_sampled_tests (α p δ:ℝ) (d:ℕ) (hα:0<α) (hp:0<p) (hδ:0<δ):
    ∃c:ℝ,0<c ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ {U Γ Color:Type} [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
      (P S Protected:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (m:ℕ)
      (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)
      (mass:Fin 6→ℝ) (ρ D ε ξ f:ℝ),
    0≤ρ→ρ≤1→0≤ε→ε≤c/2→0≤ξ→ξ≤min (min (c/4) (δ/16)) (α*p^2/4)→0≤f→
    f≤(α*p^2/16)*n→S.IsRegularOfDegree (2*m)→
    (∑a∈({0,1,2,3,4}:Finset (Fin 6)),mass a)=ρ→ρ*D=2*m→
    (∀v,|(P.degree v:ℝ)-D|≤ε*n)→
    (∀a v,|((∑w,sampledColourOrientation P (fun e=>σ (Sum.inl e)) a v w:ℕ):ℝ)-
      mass a/2*P.degree v|≤(n:ℝ)^(3/5:ℝ))→
    (∀v,((changed ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
    (∀x y,Protected.Adj x y→(S.Adj x y↔(longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y))→
    (∀v,(Protected.degree v:ℝ)≤f)→
    (∀v,(1/2+α)*(n:ℝ)≤P.degree v)→
    (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤
      ((Finset.univ.filter (fun z=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x z ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false z y)).card:ℝ))→
    ∃M:Fin n→Fin n→ℕ,
      (∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
      (∀v,(∑w,M v w)=m ∧ (∑w,M w v)=m) ∧
      (∀v,((orientationDisagreementGraph (longPhysicalStateGraph P σ {0,1,2,3,4})
        (fun e=>(σ (Sum.inl e)).2) M).degree v:ℝ)≤δ*n) ∧
      (∀x y,(orientationDisagreementGraph (longPhysicalStateGraph P σ {0,1,2,3,4})
        (fun e=>(σ (Sum.inl e)).2) M).Adj x y→¬Protected.Adj x y):=by
  have hβ:0<α*p^2:=by positivity
  obtain ⟨c,hc,N₁,hN₁pos,hN₁⟩:=class_correction_ordered_margins α p δ hα hp hδ
  obtain ⟨N₂,hN₂⟩:=eventually_class_two_path_supply (α*p^2) hβ d
  refine ⟨c,hc,max N₁ N₂,le_trans hN₁pos (le_max_left _ _),?_⟩
  intro n hn U Γ Color _ _ _ _ P S Protected π m σ mass ρ D ε ξ f hρ hρhi hε hεhi hξ hξhi hf hfhi hreg hmass hsize hdegree hcol hedit hprotected hforbid hmin htest
  have hn₁:N₁≤n:=(le_max_left _ _).trans hn
  have hn₂:N₂≤n:=(le_max_right _ _).trans hn
  have hξold:ξ≤min (c/4) (δ/16):=hξhi.trans (min_le_left _ _)
  have hξpath:ξ≤α*p^2/4:=hξhi.trans (min_le_right _ _)
  let err:ℝ:=(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)
  have hsupply:err+2*(ξ*n)≤α*p^2*n:=hN₂ n hn₂ ξ hξpath
  have htest':∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-err≤
      ((Finset.univ.filter (fun z=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x z ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false z y)).card:ℝ):=by
    intro x y hxy
    have hh:=htest x y hxy
    dsimp [err]
    linarith
  exact hN₁ n hn₁ P S Protected π d m σ mass ρ D ε ξ err f hρ hρhi hε hεhi hξ hξold hf hfhi
    hreg hmass hsize hdegree hcol hedit hprotected hforbid hmin htest' hsupply
end Oberwolfach
