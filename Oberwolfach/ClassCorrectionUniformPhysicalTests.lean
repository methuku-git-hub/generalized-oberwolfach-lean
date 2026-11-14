module

public import Oberwolfach.ClassCorrectionOrderedMargins
public import Oberwolfach.ClassTwoPathSupplyMargins
public import Oberwolfach.ExpandedClassMass

@[expose] public section
/-! The routing tolerances and order threshold are uniform in the physical
selected density once a positive lower bound has been fixed. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance uniformPhysicalFin (n:ℕ):DecidableEq (Fin n):=fun a b=>Classical.propDecidable (a=b)
local instance (priority := 2000) uniformPhysicalSix : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem class_correction_uniform_physical_tests (α pMin δ:ℝ) (d:ℕ) (hα:0<α) (hpMin:0<pMin) (hδ:0<δ):
    ∃c:ℝ,0<c ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ {U Γ Color:Type} [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
      (P S Protected:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (m:ℕ)
      (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)
      (p k p₂ k₂ u D ε ξ f:ℝ),
    pMin≤p→0≤k→0≤p₂→0≤k₂→0≤u→2*p+2*k+2*p₂+2*k₂+u≤1→0≤ε→ε≤c/2→0≤ξ→ξ≤min (min (c/4) (δ/16)) (α*pMin^2/4)→0≤f→
    f≤(α*pMin^2/16)*n→S.IsRegularOfDegree (2*m)→
    (2*p+2*k+2*p₂+2*k₂+u)*D=2*m→
    (∀v,|(P.degree v:ℝ)-D|≤ε*n)→
    (∀a v,|((∑w,sampledColourOrientation P (fun e=>σ (Sum.inl e)) a v w:ℕ):ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u a/2*P.degree v|≤(n:ℝ)^(3/5:ℝ))→
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
  let β₀:=α*pMin^2
  have hβ₀:0<β₀:=by dsimp [β₀];positivity
  obtain ⟨q,c,hq,hc,N₁,hN₁pos,hN₁⟩:=class_routing_fits_deletion β₀ δ hβ₀ hδ
  obtain ⟨N₂,hN₂⟩:=eventually_expanded_class_discrepancy c hc
  obtain ⟨N₃,hN₃⟩:=eventually_class_two_path_supply β₀ hβ₀ d
  refine ⟨c,hc,max N₁ (max N₂ N₃),le_trans hN₁pos (le_max_left _ _),?_⟩
  intro n hn U Γ Color _ _ _ _ P S Protected π m σ p k p₂ k₂ u D ε ξ f hpFloor hk hp₂ hk₂ hu hsum hε hεhi hξ hξhi hf hfhi hreg hsize hdegree hcol hedit hprotected hforbid hmin htest
  have hn₁:N₁≤n:=(le_max_left _ _).trans hn
  have hn₂:N₂≤n:=(le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₃:N₃≤n:=(le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnpos:0<n:=by omega
  have hn0:0≤(n:ℝ):=Nat.cast_nonneg n
  have hp:0<p:=lt_of_lt_of_le hpMin hpFloor
  have hp2:pMin^2≤p^2:=by nlinarith
  have hβle:β₀≤α*p^2:=mul_le_mul_of_nonneg_left hp2 hα.le
  have hβn:β₀*n≤α*p^2*n:=mul_le_mul_of_nonneg_right hβle hn0
  let ρ:=2*p+2*k+2*p₂+2*k₂+u
  have hρ:0≤ρ:=by dsimp [ρ];positivity
  have hρhi:ρ≤1:=hsum
  have hξbase:ξ≤min (c/4) (δ/16):=hξhi.trans (min_le_left _ _)
  have hξc:ξ≤c/4:=hξbase.trans (min_le_left _ _)
  have hξδ:ξ≤δ/16:=hξbase.trans (min_le_right _ _)
  have hξβ:ξ≤β₀/4:=hξhi.trans (min_le_right _ _)
  let a:=5*(n:ℝ)^(3/5:ℝ)+ρ/2*(ε*n)+ξ*n
  have ha:0≤a:=by dsimp [a];positivity
  have hac:a≤c*n:=hN₂ n hn₂ ρ ε ξ hρ hρhi hε hεhi hξc
  have hξn:ξ*n≤(δ/16)*n:=mul_le_mul_of_nonneg_right hξδ hn0
  obtain ⟨L,hL,hrout,hcorr⟩:=hN₁ n hn₁ a f (ξ*n) (β₀/16) ha hac hfhi (le_refl _) hξn
  let err:ℝ:=(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)
  have hsupply:err+2*(ξ*n)≤α*p^2*n:=(hN₃ n hn₃ ξ hξβ).trans hβn
  have htest':∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-err≤
      ((Finset.univ.filter (fun z=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x z ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false z y)).card:ℝ):=by
    intro x y hxy
    have hh:=htest x y hxy
    dsimp [err]
    linarith
  have hmin':∀v,(1/2+α)*(Fintype.card (Fin n):ℝ)≤P.degree v:=by simpa using hmin
  have hsupply':err+2*(ξ*n)≤α*p^2*Fintype.card (Fin n):=by simpa using hsupply
  have hrout':(Fintype.card (Fin n):ℝ)*
      (5*(n:ℝ)^(3/5:ℝ)+ρ/2*(ε*n)+ξ*n)/L+
      2*(5*(n:ℝ)^(3/5:ℝ)+ρ/2*(ε*n)+ξ*n)+4*L+2*f<α*p^2*Fintype.card (Fin n):=by
    have hh:=lt_of_lt_of_le hrout hβn
    simpa [a] using hh
  obtain ⟨M,hphys,hdegrees,hbound,havoid⟩:=class_correction_from_common_event P S Protected π d m L σ
    (markedExpandedPhysicalProbability p k p₂ k₂ u) ρ D ((n:ℝ)^(3/5:ℝ)) (ξ*n) (ε*n) α p err f hreg
    (by simpa using hnpos) hL hρ (by positivity) (by positivity) (by positivity) hα hp hf
    (expanded_physical_class_mass p k p₂ k₂ u) hsize hdegree hcol hedit hprotected hforbid hmin' htest' hsupply' hrout'
  refine ⟨M,hphys,hdegrees,?_,havoid⟩
  intro v
  exact (hbound v).trans (by simpa [a] using hcorr)
end Oberwolfach
