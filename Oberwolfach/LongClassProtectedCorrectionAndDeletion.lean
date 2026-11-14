module

public import Oberwolfach.LongClassCorrectionFromSampledTests
public import Oberwolfach.LongClassProtectedMatchingAfterCorrection

@[expose] public section
/-! Sampled colour and path tests supply a balanced orientation of the same
regular class and a small deletion that preserves its protected edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance classProtectedCorrectionFin (n:ℕ):DecidableEq (Fin n):=fun a b=>Classical.propDecidable (a=b)
local instance (priority := 2000) classProtectedCorrectionSix : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem long_class_protected_correction_and_deletion (α ρ₀ δ:ℝ) (d:ℕ)
    (hα:0<α) (hρ₀:0<ρ₀) (hδ:0<δ):
    ∃c:ℝ,0<c ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ {U Γ Color:Type} [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
      (P S Protected D₀:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (m:ℕ)
      (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)
      (ρ D s ε ξ f η:ℝ) (a b:U→ℝ),
    let p:=ρ*(1/100)/2
    let k:=ρ*s/2
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let u:=2*(∑w,(1-1/100-s-a w-b w))/D;
    ρ₀≤ρ→ρ≤1→0<D→0≤k→0≤p₂→0≤k₂→0≤u→0≤ε→ε≤c/2→0≤ξ→
    ξ≤min (min (c/4) (δ/16)) (α*(ρ₀/200)^2/4)→0≤f→
    f≤(α*(ρ₀/200)^2/16)*n→S.IsRegularOfDegree (2*m)→
    ρ*D=2*Fintype.card U→m=Fintype.card U→S≤P→
    (∀v,|(P.degree v:ℝ)-D|≤ε*n)→
    (∀j v,|((∑w,sampledColourOrientation P (fun e=>σ (Sum.inl e)) j v w:ℕ):ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|≤(n:ℝ)^(3/5:ℝ))→
    (∀v,((changed ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
    (∀x y,Protected.Adj x y→(S.Adj x y↔(longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y))→
    (∀v,(Protected.degree v:ℝ)≤f)→(∀v,(D₀.degree v:ℝ)≤η*n)→
    (∀x y,D₀.Adj x y→¬Protected.Adj x y)→
    (∀v,(1/2+α)*(n:ℝ)≤P.degree v)→
    (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤
      ((Finset.univ.filter (fun z=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x z ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false z y)).card:ℝ))→
    ∃(M:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n)),
      (∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
      (∀v,(∑w,M v w)=m ∧ (∑w,M w v)=m) ∧
      D₀≤Del ∧ (longPhysicalStateGraph P σ {0,1,2,3,4}\S)≤Del ∧
      orientationDisagreementGraph (longPhysicalStateGraph P σ {0,1,2,3,4}) (fun e=>(σ (Sum.inl e)).2) M≤Del ∧
      (∀v,(Del.degree v:ℝ)≤(η+ξ+δ)*n) ∧
      (∀x y,Del.Adj x y→¬Protected.Adj x y) ∧
      (∀x y,rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y→¬Del.Adj x y→M x y=1) ∧
      (∀x y,S.Adj x y→M x y=1 ∨ M y x=1) ∧
      (∀x y,M x y=1→P.Adj x y) ∧
      (∀x y,rawMixedPhysicalArc P π d (fun e=>rawExpandedApproximateCollapse e (σ e)) x y→¬Del.Adj x y→M x y=1):=by
  obtain ⟨c,hc,N,hNpos,hN⟩:=long_class_correction_from_sampled_tests α ρ₀ δ d hα hρ₀ hδ
  refine ⟨c,hc,N,hNpos,?_⟩
  intro n hn U Γ Color _ _ _ _ P S Protected D₀ π m σ ρ D s ε ξ f η a b p k p₂ k₂ u
    hρlo hρhi hD hk hp₂ hk₂ hu hε hεhi hξ hξhi hf hfhi hreg hsize hm hSP hdegree hcol hedit hprotect hforbid hD₀ hD₀protect hmin htest
  have hN':=hN n hn P S Protected π m σ ρ D s ε ξ f a b
  have hdec:longPhysicalFin n=classProtectedCorrectionFin n:=Subsingleton.elim _ _
  have hdec6:longPhysicalSix=classProtectedCorrectionSix:=Subsingleton.elim _ _
  try rw [hdec] at hN'
  try rw [hdec6] at hN'
  obtain ⟨M,hphysical,hbalance,hcorrect,hcorrprotect⟩:=hN' hρlo hρhi hD hk hp₂ hk₂ hu hε hεhi hξ hξhi hf hfhi hreg hsize hm hdegree hcol hedit hprotect hforbid hmin htest
  have hD₀':∀v,(D₀.degree v:ℝ)≤η*Fintype.card (Fin n):=by simpa only [Fintype.card_fin] using hD₀
  have hedit':∀v,((changed ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*Fintype.card (Fin n):=by simpa only [Fintype.card_fin] using hedit
  have hcorr':∀v,((orientationDisagreementGraph (longPhysicalStateGraph P σ {0,1,2,3,4}) (fun e=>(σ (Sum.inl e)).2) M).degree v:ℝ)≤δ*Fintype.card (Fin n):=by simpa only [Fintype.card_fin] using hcorrect
  obtain ⟨Del,hD,hdelEdit,hdelCorr,hdelDegree,hdelProtect,hfree,hS,hhost,harc⟩:=long_class_protected_matching_after_correction P S S D₀ Protected π d σ M ξ δ η hSP le_rfl hphysical hedit' hcorr' hD₀' hprotect hD₀protect hcorrprotect
  exact ⟨M,Del,hphysical,hbalance,hD,hdelEdit,hdelCorr,(by simpa only [Fintype.card_fin] using hdelDegree),hdelProtect,hfree,hS,hhost,harc⟩
end Oberwolfach
