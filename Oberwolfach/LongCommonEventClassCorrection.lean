module

public import Oberwolfach.LongClassCorrectionFromSampledTests

@[expose] public section
/-! Preserve the same expanded outcome and every prior event while exposing
the protected balanced correction for every admissible regular class. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance commonClassCorrectionFin (n:ℕ):DecidableEq (Fin n):=fun a b=>Classical.propDecidable (a=b)
local instance (priority := 2000) commonClassCorrectionSix : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem long_common_event_class_correction (α ρ₀ δ:ℝ) (d:ℕ)
    (hα:0<α) (hρ₀:0<ρ₀) (hδ:0<δ):
    ∃c:ℝ,0<c ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ {U Γ Color Ω:Type} [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
      (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
      (σ:Ω→∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)
      (Good:Ω→Prop) (ρ D s ε:ℝ) (a b:U→ℝ),
    let p:=ρ*(1/100)/2
    let k:=ρ*s/2
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let u:=2*(∑w,(1-1/100-s-a w-b w))/D;
    ρ₀≤ρ→ρ≤1→0<D→0≤k→0≤p₂→0≤k₂→0≤u→0≤ε→ε≤c/2→
    ρ*D=2*Fintype.card U→(∀v,|(P.degree v:ℝ)-D|≤ε*n)→
    (∀v,(1/2+α)*(n:ℝ)≤P.degree v)→
    (∃z,Good z ∧
      (∀j v,|((∑w,sampledColourOrientation P (fun e=>σ z (Sum.inl e)) j v w:ℕ):ℝ)-
        markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ)) ∧
      (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤
        ((Finset.univ.filter (fun w=>
          0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ z (Sum.inl e))) false x w ∧
          0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ z (Sum.inl e))) false w y)).card:ℝ)))→
    ∃z,Good z ∧ ∀(S Protected:SimpleGraph (Fin n)) (ξ f:ℝ),
      0≤ξ→ξ≤min (min (c/4) (δ/16)) (α*(ρ₀/200)^2/4)→0≤f→
      f≤(α*(ρ₀/200)^2/16)*n→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P (σ z) {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
      (∀x y,Protected.Adj x y→(S.Adj x y↔(longPhysicalStateGraph P (σ z) {0,1,2,3,4}).Adj x y))→
      (∀v,(Protected.degree v:ℝ)≤f)→
      ∃M:Fin n→Fin n→ℕ,
        (∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
        (∀v,(∑w,M v w)=Fintype.card U ∧ (∑w,M w v)=Fintype.card U) ∧
        (∀v,((orientationDisagreementGraph (longPhysicalStateGraph P (σ z) {0,1,2,3,4})
          (fun e=>(σ z (Sum.inl e)).2) M).degree v:ℝ)≤δ*n) ∧
        (∀x y,(orientationDisagreementGraph (longPhysicalStateGraph P (σ z) {0,1,2,3,4})
          (fun e=>(σ z (Sum.inl e)).2) M).Adj x y→¬Protected.Adj x y):=by
  obtain ⟨c,hc,N,hNpos,hN⟩:=long_class_correction_from_sampled_tests α ρ₀ δ d hα hρ₀ hδ
  refine ⟨c,hc,N,hNpos,?_⟩
  intro n hn U Γ Color Ω _ _ _ _ P π σ Good ρ D s ε a b p k p₂ k₂ u hρlo hρhi hD hk hp₂ hk₂ hu hε hεhi hsize hdegree hmin hsample
  obtain ⟨z,hgood,hcol,htest⟩:=hsample
  refine ⟨z,hgood,?_⟩
  intro S Protected ξ f hξ hξhi hf hfhi hreg hedit hprotected hforbid
  exact hN n hn P S Protected π (Fintype.card U) (σ z) ρ D s ε ξ f a b
    hρlo hρhi hD hk hp₂ hk₂ hu hε hεhi hξ hξhi hf hfhi hreg hsize rfl hdegree
    (fun j v=>(hcol j v).le) hedit hprotected hforbid hmin htest
end Oberwolfach
