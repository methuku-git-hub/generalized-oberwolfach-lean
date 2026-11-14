module

public import Oberwolfach.LongCommonEventClassCorrection

@[expose] public section
/-! A protected regular-class witness and the matching tests on one sample
jointly produce its balanced orientation correction on that same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance commonProtectedBalancedFin (n:ℕ):DecidableEq (Fin n):=fun a b=>Classical.propDecidable (a=b)
local instance (priority := 2000) commonProtectedBalancedSix : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem long_common_protected_balanced_class (α ρ₀ δ:ℝ) (d:ℕ)
    (hα:0<α) (hρ₀:0<ρ₀) (hδ:0<δ):
    ∃c:ℝ,0<c ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ {U Γ Color Ω:Type} [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
      (P Z:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
      (σ:Ω→∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)
      (Good:Ω→Prop) (ρ D s ε ξ f:ℝ) (a b:U→ℝ) (B:ℕ),
    let p:=ρ*(1/100)/2
    let k:=ρ*s/2
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let u:=2*(∑w,(1-1/100-s-a w-b w))/D;
    ρ₀≤ρ→ρ≤1→0<D→0≤k→0≤p₂→0≤k₂→0≤u→0≤ε→ε≤c/2→
    ρ*D=2*Fintype.card U→(∀v,|(P.degree v:ℝ)-D|≤ε*n)→
    (∀v,(1/2+α)*(n:ℝ)≤P.degree v)→
    0≤ξ→ξ≤min (min (c/4) (δ/16)) (α*(ρ₀/200)^2/4)→0≤f→
    f≤(α*(ρ₀/200)^2/16)*n→
    (∃z,Good z ∧
      (∀A:SimpleGraph (Fin n),(∀v,A.degree v≤B)→
        ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
          (∀x y,(Z⊔A).Adj x y→(S.Adj x y↔(longPhysicalStateGraph P (σ z) {0,1,2,3,4}).Adj x y)) ∧
          (∀v,((changed ((longPhysicalStateGraph P (σ z) {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)) ∧
      (∀j v,|((∑w,sampledColourOrientation P (fun e=>σ z (Sum.inl e)) j v w:ℕ):ℝ)-
        markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ)) ∧
      (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤
        ((Finset.univ.filter (fun w=>
          0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ z (Sum.inl e))) false x w ∧
          0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ z (Sum.inl e))) false w y)).card:ℝ)))→
    ∃z,Good z ∧ ∀A:SimpleGraph (Fin n),(∀v,A.degree v≤B)→
      (∀v,((Z⊔A).degree v:ℝ)≤f)→
      ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
        (∀x y,(Z⊔A).Adj x y→(S.Adj x y↔(longPhysicalStateGraph P (σ z) {0,1,2,3,4}).Adj x y)) ∧
        (∀v,((changed ((longPhysicalStateGraph P (σ z) {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n) ∧
        ∃M:Fin n→Fin n→ℕ,
          (∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
          (∀v,(∑w,M v w)=Fintype.card U ∧ (∑w,M w v)=Fintype.card U) ∧
          (∀v,((orientationDisagreementGraph (longPhysicalStateGraph P (σ z) {0,1,2,3,4})
            (fun e=>(σ z (Sum.inl e)).2) M).degree v:ℝ)≤δ*n) ∧
          (∀x y,(orientationDisagreementGraph (longPhysicalStateGraph P (σ z) {0,1,2,3,4})
            (fun e=>(σ z (Sum.inl e)).2) M).Adj x y→¬(Z⊔A).Adj x y):=by
  obtain ⟨c,hc,N,hNpos,hN⟩:=long_common_event_class_correction α ρ₀ δ d hα hρ₀ hδ
  refine ⟨c,hc,N,hNpos,?_⟩
  intro n hn U Γ Color Ω _ _ _ _ P Z π σ Good ρ D s ε ξ f a b B p k p₂ k₂ u
    hρlo hρhi hD hk hp₂ hk₂ hu hε hεhi hsize hdegree hmin hξ hξhi hf hfhi hsample
  let Part:=fun z:Ω=>∀A:SimpleGraph (Fin n),(∀v,A.degree v≤B)→
    ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
      (∀x y,(Z⊔A).Adj x y→(S.Adj x y↔(longPhysicalStateGraph P (σ z) {0,1,2,3,4}).Adj x y)) ∧
      (∀v,((changed ((longPhysicalStateGraph P (σ z) {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)
  obtain ⟨z,hgood,hpart,hcol,hpair⟩:=hsample
  have hsample':∃z,(Good z ∧ Part z) ∧
      (∀j v,|((∑w,sampledColourOrientation P (fun e=>σ z (Sum.inl e)) j v w:ℕ):ℝ)-
        markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ)) ∧
      (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤
        ((Finset.univ.filter (fun w=>
          0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ z (Sum.inl e))) false x w ∧
          0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ z (Sum.inl e))) false w y)).card:ℝ)):=
    ⟨z,⟨hgood,hpart⟩,hcol,hpair⟩
  have hN':=hN n hn P π σ (fun z=>Good z ∧ Part z) ρ D s ε a b
  have hdec:commonClassCorrectionFin n=commonProtectedBalancedFin n:=Subsingleton.elim _ _
  have hdec6:commonClassCorrectionSix=commonProtectedBalancedSix:=Subsingleton.elim _ _
  try rw [hdec] at hN'
  try rw [hdec6] at hN'
  obtain ⟨z,hboth,hcorrect⟩:=hN' hρlo hρhi hD hk hp₂ hk₂ hu hε hεhi hsize hdegree hmin hsample'
  refine ⟨z,hboth.1,?_⟩
  intro A hA hforbid
  obtain ⟨S,hSP,hreg,hprotect,hedit⟩:=hboth.2 A hA
  letI : DecidableRel (Z⊔A).Adj := fun x y=>Classical.propDecidable _
  have hforbid':∀v,((Z⊔A).degree v:ℝ)≤f:=by
    intro v
    convert hforbid v using 1
    congr 1
    simp only [← SimpleGraph.ncard_neighborSet]
  obtain ⟨M,hM,hbal,hsmall,hdis⟩:=hcorrect S (Z⊔A) ξ f hξ hξhi hf hfhi hreg hedit hprotect hforbid'
  exact ⟨S,hSP,hreg,hprotect,hedit,M,hM,hbal,hsmall,hdis⟩
end Oberwolfach
