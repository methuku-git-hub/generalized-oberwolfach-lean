module

public import Oberwolfach.LongFixedSampleProtectedBalancedClass
public import Oberwolfach.MarkedExpandedActualSample

@[expose] public section
/-! Balance the protected regular class on the already selected actual
expanded-and-retained sample, preserving every accompanying property. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance actualProtectedOrientationFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
theorem long_actual_expanded_sample_protected_orientation (α ρ₀ δ:ℝ) (d:ℕ)
    (hα:0<α) (hρ₀:0<ρ₀) (hδ:0<δ):
    ∃c:ℝ,0<c ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
      (P Z:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
      (sample:MarkedExpandedActualOutcome (U:=U) π d)
      (Good:MarkedExpandedActualOutcome (U:=U) π d→Prop) (ρ D s ε ξ f:ℝ) (a b:U→ℝ) (B:ℕ),
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
    (Good sample ∧
      (∀A:SimpleGraph (Fin n),(∀v,A.degree v≤B)→
        ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
          (∀x y,(Z⊔A).Adj x y→(S.Adj x y↔(longPhysicalStateGraph P (sample.1) {0,1,2,3,4}).Adj x y)) ∧
          (∀v,((changed ((longPhysicalStateGraph P (sample.1) {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)) ∧
      (∀j v,|((∑w,sampledColourOrientation P (fun e=>sample.1 (Sum.inl e)) j v w:ℕ):ℝ)-
        markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ)) ∧
      (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤
        ((Finset.univ.filter (fun w=>
          0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (sample.1 (Sum.inl e))) false x w ∧
          0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (sample.1 (Sum.inl e))) false w y)).card:ℝ)))→
    Good sample ∧ ∀A:SimpleGraph (Fin n),(∀v,A.degree v≤B)→
      (∀v,((Z⊔A).degree v:ℝ)≤f)→
      ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
        (∀x y,(Z⊔A).Adj x y→(S.Adj x y↔(longPhysicalStateGraph P (sample.1) {0,1,2,3,4}).Adj x y)) ∧
        (∀v,((changed ((longPhysicalStateGraph P (sample.1) {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n) ∧
        ∃M:Fin n→Fin n→ℕ,
          (∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
          (∀v,(∑w,M v w)=Fintype.card U ∧ (∑w,M w v)=Fintype.card U) ∧
          (∀v,((orientationDisagreementGraph (longPhysicalStateGraph P (sample.1) {0,1,2,3,4})
            (fun e=>(sample.1 (Sum.inl e)).2) M).degree v:ℝ)≤δ*n) ∧
          (∀x y,(orientationDisagreementGraph (longPhysicalStateGraph P (sample.1) {0,1,2,3,4})
            (fun e=>(sample.1 (Sum.inl e)).2) M).Adj x y→¬(Z⊔A).Adj x y):= by
  obtain ⟨c,hc,N,hN,hMain⟩:=long_fixed_sample_protected_balanced_class α ρ₀ δ d hα hρ₀ hδ
  refine ⟨c,hc,N,hN,?_⟩
  intro n hn U _ _ _ P Z π sample Good ρ D s ε ξ f a b B
  dsimp only
  intro hρlo hρhi hD hk hp₂ hk₂ hu hε hεhi hsize hdegree hmin hξ hξhi hf hfhi hsample
  have hh:=hMain n hn P Z π (fun z:MarkedExpandedActualOutcome (U:=U) π d=>z.1) sample Good ρ D s ε ξ f a b B
  have hdec:instDecidableEqFin n=actualProtectedOrientationFin n:=Subsingleton.elim _ _
  have hdec6:instDecidableEqFin 6=actualProtectedOrientationFin 6:=Subsingleton.elim _ _
  try rw [hdec] at hh
  try rw [hdec6] at hh
  exact hh hρlo hρhi hD hk hp₂ hk₂ hu hε hεhi hsize hdegree hmin hξ hξhi hf hfhi hsample
end Oberwolfach
