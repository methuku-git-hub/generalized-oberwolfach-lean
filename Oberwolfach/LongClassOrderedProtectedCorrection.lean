module

public import Oberwolfach.LongClassProtectedCorrectionAndDeletion
public import Oberwolfach.FirstVortexClassDualDeletionBudgets

@[expose] public section
/-! The correction scale is selected before its threshold and the class edit,
with both matching budgets and the vortex load margin available uniformly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance classOrderedCorrectionFin (n:ℕ):DecidableEq (Fin n):=fun a b=>Classical.propDecidable (a=b)
local instance (priority := 2000) classOrderedCorrectionSix : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem long_class_protected_correction_ordered_budgets
    (αHost αAssign ρ₀ εV Δ ξBudget δold δlocal lam lam₀:ℝ) (d:ℕ)
    (hαHost:0<αHost) (hαAssign:0<αAssign) (hρ₀:0<ρ₀) (hεV:0<εV)
    (hΔ:0<Δ) (hξBudget:0<ξBudget) (hgap:δold<δlocal) (hlam:lam₀<lam):
    ∃δcorr:ℝ,0<δcorr ∧ ∃c:ℝ,0<c ∧ ∃N:ℕ,1≤N ∧ ∃ξPart:ℝ,0<ξPart ∧
      ξPart+δcorr≤Δ ∧ ξPart+δcorr≤ξBudget ∧
      ξPart≤min (min (c/4) (δcorr/16)) (αHost*(ρ₀/200)^2/4) ∧
      ξPart≤αAssign/32 ∧ ξPart/2≤(lam-lam₀)*εV ∧
      (∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n))
        (D m:ℕ) (β:ℝ) (Q:Vortex U G D β εV m),0<m→
        ξPart*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ)) ∧
      (∀n:ℕ,N≤n→
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
    ξ≤min (min (c/4) (δcorr/16)) (αHost*(ρ₀/200)^2/4)→0≤f→
    f≤(αHost*(ρ₀/200)^2/16)*n→S.IsRegularOfDegree (2*m)→
    ρ*D=2*Fintype.card U→m=Fintype.card U→S≤P→
    (∀v,|(P.degree v:ℝ)-D|≤ε*n)→
    (∀j v,|((∑w,sampledColourOrientation P (fun e=>σ (Sum.inl e)) j v w:ℕ):ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|≤(n:ℝ)^(3/5:ℝ))→
    (∀v,((changed ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
    (∀x y,Protected.Adj x y→(S.Adj x y↔(longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y))→
    (∀v,(Protected.degree v:ℝ)≤f)→(∀v,(D₀.degree v:ℝ)≤η*n)→
    (∀x y,D₀.Adj x y→¬Protected.Adj x y)→
    (∀v,(1/2+αHost)*(n:ℝ)≤P.degree v)→
    (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤
      ((Finset.univ.filter (fun z=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x z ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false z y)).card:ℝ))→
    ∃(M:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n)),
      (∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
      (∀v,(∑w,M v w)=m ∧ (∑w,M w v)=m) ∧
      D₀≤Del ∧ (longPhysicalStateGraph P σ {0,1,2,3,4}\S)≤Del ∧
      orientationDisagreementGraph (longPhysicalStateGraph P σ {0,1,2,3,4}) (fun e=>(σ (Sum.inl e)).2) M≤Del ∧
      (∀v,(Del.degree v:ℝ)≤(η+ξ+δcorr)*n) ∧
      (∀x y,Del.Adj x y→¬Protected.Adj x y) ∧
      (∀x y,rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y→¬Del.Adj x y→M x y=1) ∧
      (∀x y,S.Adj x y→M x y=1 ∨ M y x=1) ∧
      (∀x y,M x y=1→P.Adj x y) ∧
      (∀x y,rawMixedPhysicalArc P π d (fun e=>rawExpandedApproximateCollapse e (σ e)) x y→¬Del.Adj x y→M x y=1) ) :=by
  obtain ⟨δcorr,hδ,hchoose⟩:=first_vortex_class_dual_deletion_budgets αHost αAssign ρ₀ εV Δ ξBudget δold δlocal lam lam₀ hαHost hαAssign hρ₀ hεV hΔ hξBudget hgap hlam
  obtain ⟨c,hc,N,hNpos,hN⟩:=long_class_protected_correction_and_deletion αHost ρ₀ δcorr d hαHost hρ₀ hδ
  obtain ⟨ξPart,hξ,hΔbudget,hξbudget,hbound,hdegree,hedges,hload⟩:=hchoose c hc
  have hdec:classProtectedCorrectionFin=classOrderedCorrectionFin:=by funext n; exact Subsingleton.elim _ _
  have hdec6:classProtectedCorrectionSix=classOrderedCorrectionSix:=Subsingleton.elim _ _
  try rw [hdec] at hN
  try rw [hdec6] at hN
  refine ⟨δcorr,hδ,c,hc,N,hNpos,ξPart,hξ,?_,?_,hbound,hdegree,hedges,hload,hN⟩ <;> linarith
end Oberwolfach
