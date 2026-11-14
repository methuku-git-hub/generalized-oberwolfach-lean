module

public import Oberwolfach.ClassCorrectionUniformPhysicalTests
public import Oberwolfach.LongExpandedClassDensityAndFloor

@[expose] public section
/-! Apply the uniform class-correction theorem to the long-class sampling
recipe using the original index density and lower bound. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longPhysicalFin (n:ℕ):DecidableEq (Fin n):=fun a b=>Classical.propDecidable (a=b)
local instance (priority := 2000) longPhysicalSix : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem long_class_correction_from_sampled_tests (α ρ₀ δ:ℝ) (d:ℕ) (hα:0<α) (hρ₀:0<ρ₀) (hδ:0<δ):
    ∃c:ℝ,0<c ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ {U Γ Color:Type} [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
      (P S Protected:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (m:ℕ)
      (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)
      (ρ D s ε ξ f:ℝ) (a b:U→ℝ),
    let p:=ρ*(1/100)/2
    let k:=ρ*s/2
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let u:=2*(∑w,(1-1/100-s-a w-b w))/D;
    ρ₀≤ρ→ρ≤1→0<D→0≤k→0≤p₂→0≤k₂→0≤u→0≤ε→ε≤c/2→0≤ξ→ξ≤min (min (c/4) (δ/16)) (α*(ρ₀/200)^2/4)→0≤f→
    f≤(α*(ρ₀/200)^2/16)*n→S.IsRegularOfDegree (2*m)→
    ρ*D=2*Fintype.card U→m=Fintype.card U→
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
  have hpMin:0<ρ₀/200:=by positivity
  obtain ⟨c,hc,N,hNpos,hN⟩:=class_correction_uniform_physical_tests α (ρ₀/200) δ d hα hpMin hδ
  refine ⟨c,hc,N,hNpos,?_⟩
  intro n hn U Γ Color _ _ _ _ P S Protected π m σ ρ D s ε ξ f a b p k p₂ k₂ u hρlo hρhi hD hk hp₂ hk₂ hu hε hεhi hξ hξhi hf hfhi hreg hsize hm hdegree hcol hedit hprotected hforbid hmin htest
  obtain ⟨hfloor,hmass⟩:=long_expanded_class_density_and_floor ρ₀ ρ D s a b hD hρlo hsize
  have hsum:2*p+2*k+2*p₂+2*k₂+u=ρ:=by
    have hmass':=(expanded_physical_class_mass p k p₂ k₂ u).symm.trans hmass
    exact hmass'
  have hsumhi:2*p+2*k+2*p₂+2*k₂+u≤1:=hsum.le.trans hρhi
  have hsize':(2*p+2*k+2*p₂+2*k₂+u)*D=2*m:=by rw [hsum,hm];exact hsize
  exact hN n hn P S Protected π m σ p k p₂ k₂ u D ε ξ f hfloor hk hp₂ hk₂ hu hsumhi hε hεhi hξ hξhi hf hfhi hreg hsize' hdegree hcol hedit hprotected hforbid hmin htest
end Oberwolfach
