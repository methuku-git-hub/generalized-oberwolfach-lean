module

public import Oberwolfach.LongClassSpacingOrderedProtectedCorrection
public import Oberwolfach.LongClassOrderedProtectedCorrection
public import Oberwolfach.PrunedClassCorrectionInputs

@[expose] public section
/-! On a pruned regular host the ordered correction theorem uses the actual
selected index subtype and preserves every admissible protected graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance prunedClassSpacingCorrectionFin (n:ℕ):DecidableEq (Fin n):=fun a b=>Classical.propDecidable (a=b)
local instance (priority := 2000) prunedClassSpacingCorrectionSix : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem pruned_class_spacing_ordered_protected_correction
    (αHost αAssign ρ₀ εV Δ ξBudget δold δlocal lam lam₀:ℝ)
    (hαHost:0<αHost) (hαAssign:0<αAssign) (hρ₀:0<ρ₀) (hεV:0<εV)
    (hΔ:0<Δ) (hξBudget:0<ξBudget) (hgap:δold<δlocal) (hlam:lam₀<lam):
    ∃δcorr:ℝ,0<δcorr ∧ ∃c:ℝ,0<c ∧ ∃ξPart:ℝ,0<ξPart ∧
      ξPart+δcorr≤Δ ∧ ξPart+δcorr≤ξBudget ∧ ξPart≤αAssign/32 ∧
      ξPart/2≤(lam-lam₀)*εV ∧
      (∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n))
        (D m:ℕ) (β:ℝ) (Q:Vortex U G D β εV m),0<m→
        ξPart*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ)) ∧
    ∀d:ℕ, ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→∀ {U Γ Color:Type} [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
      (P S Protected:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (D B:ℕ)
      (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)
      (ρ s:ℝ) (a b:U→ℝ),
    let p:=ρ*(1/100)/2
    let k:=ρ*s/2
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let u:=2*(∑w,(1-1/100-s-a w-b w))/D;
    ρ₀≤ρ→ρ≤1→0<D→0≤k→0≤p₂→0≤k₂→0≤u→
    P.IsRegularOfDegree D→S.IsRegularOfDegree (2*Fintype.card U)→S≤P→
    ρ*(D:ℝ)=2*Fintype.card U→(∀v,(1/2+αHost)*(n:ℝ)≤P.degree v)→
    (B:ℝ)≤(αHost*(ρ₀/200)^2/16)*n→(∀v,Protected.degree v≤B)→
    (∀j v,|((∑w,sampledColourOrientation P (fun e=>σ (Sum.inl e)) j v w:ℕ):ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|≤(n:ℝ)^(3/5:ℝ))→
    (∀v,((changed ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξPart*n)→
    (∀x y,Protected.Adj x y→(S.Adj x y↔(longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y))→
    (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤
      ((Finset.univ.filter (fun z=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x z ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false z y)).card:ℝ))→
    ∃(M:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n)),
      (∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
      (∀v,(∑w,M v w)=Fintype.card U ∧ (∑w,M w v)=Fintype.card U) ∧
      (longPhysicalStateGraph P σ {0,1,2,3,4}\S)≤Del ∧
      orientationDisagreementGraph (longPhysicalStateGraph P σ {0,1,2,3,4}) (fun e=>(σ (Sum.inl e)).2) M≤Del ∧
      (∀v,(Del.degree v:ℝ)≤(ξPart+δcorr)*n) ∧
      (∀x y,Del.Adj x y→¬Protected.Adj x y):=by
  obtain ⟨δcorr,hδ,c,hc,ξPart,hξ,hΔbudget,hξbudget,hbound,hassign,hedges,hload,hN⟩:=
    long_class_protected_correction_spacing_ordered αHost αAssign ρ₀ εV Δ ξBudget δold δlocal lam lam₀
      hαHost hαAssign hρ₀ hεV hΔ hξBudget hgap hlam
  refine ⟨δcorr,hδ,c,hc,ξPart,hξ,hΔbudget,hξbudget,hassign,hedges,hload,?_⟩
  intro d
  obtain ⟨N,hNpos,hN⟩:=hN d
  refine ⟨N,hNpos,?_⟩
  intro n hn U Γ Color _ _ _ _ P S Protected π D B σ ρ s a b p k p₂ k₂ u
    hρlo hρhi hD hk hp₂ hk₂ hu hregP hregS hSP hsize hmin hB hprotectDegree hcol hedit hprotect htest
  have hN':=hN n hn P S Protected ⊥ π (Fintype.card U) σ ρ D s 0 ξPart B 0 a b
  have hdec:classSpacingOrderedCorrectionFin n=prunedClassSpacingCorrectionFin n:=Subsingleton.elim _ _
  have hdec6:classSpacingOrderedCorrectionSix=prunedClassSpacingCorrectionSix:=Subsingleton.elim _ _
  try rw [hdec] at hN'
  try rw [hdec6] at hN'
  have hdegree:∀v,|(P.degree v:ℝ)-(D:ℝ)|≤(0:ℝ)*n:=by
    intro v
    rw [hregP.degree_eq v]
    simp
  have hprotectDegree':∀v,(Protected.degree v:ℝ)≤B:=by intro v; exact_mod_cast hprotectDegree v
  obtain ⟨M,Del,hphysical,hbalance,_,hedits,hcorrect,hdelDegree,hdelProtect,_,_,_,_⟩:=
    hN' hρlo hρhi (by exact_mod_cast hD) hk hp₂ hk₂ hu (by norm_num) (by linarith) hξ.le hbound (by positivity) hB hregS hsize rfl hSP hdegree hcol hedit hprotect hprotectDegree' (by intro v; simp) (by intro x y h; exact False.elim h) hmin htest
  exact ⟨M,Del,hphysical,hbalance,hedits,hcorrect,(by simpa only [zero_add] using hdelDegree),hdelProtect⟩
end Oberwolfach
