module

public import Oberwolfach.ClassCorrectionFromSampledTests
public import Oberwolfach.ExpandedClassMass

@[expose] public section
/-! Apply the protected correction to the original expanded physical law,
with its class density calculated from the five sampled states. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance physicalMarginsFin (n:ℕ):DecidableEq (Fin n):=fun a b=>Classical.propDecidable (a=b)
local instance (priority := 2000) physicalMarginsSix : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem class_correction_from_physical_tests (α p δ:ℝ) (d:ℕ) (hα:0<α) (hp:0<p) (hδ:0<δ):
    ∃c:ℝ,0<c ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ {U Γ Color:Type} [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
      (P S Protected:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (m:ℕ)
      (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)
      (k p₂ k₂ u D ε ξ f:ℝ),
    0≤k→0≤p₂→0≤k₂→0≤u→2*p+2*k+2*p₂+2*k₂+u≤1→0≤ε→ε≤c/2→0≤ξ→ξ≤min (min (c/4) (δ/16)) (α*p^2/4)→0≤f→
    f≤(α*p^2/16)*n→S.IsRegularOfDegree (2*m)→
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
  obtain ⟨c,hc,N,hNpos,hN⟩:=class_correction_from_sampled_tests α p δ d hα hp hδ
  refine ⟨c,hc,N,hNpos,?_⟩
  intro n hn U Γ Color _ _ _ _ P S Protected π m σ k p₂ k₂ u D ε ξ f hk hp₂ hk₂ hu hsum hε hεhi hξ hξhi hf hfhi hreg hsize hdegree hcol hedit hprotected hforbid hmin htest
  have hρ:0≤2*p+2*k+2*p₂+2*k₂+u:=by positivity
  exact hN n hn P S Protected π m σ (markedExpandedPhysicalProbability p k p₂ k₂ u)
    (2*p+2*k+2*p₂+2*k₂+u) D ε ξ f hρ hsum hε hεhi hξ hξhi hf hfhi hreg
    (expanded_physical_class_mass p k p₂ k₂ u) hsize hdegree hcol hedit hprotected hforbid hmin htest
end Oberwolfach
