module

public import Oberwolfach.LongBinaryPrunedParameters

@[expose] public section
/-! The pruned-class parameters provide the precise alternatives required by
one joint matching, boundary, and protected regular-class event. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem long_binary_pruned_common_event_parameters
    {I U:Type} [Fintype I] [DecidableEq I] [Fintype U] (ρclass:I→ℝ) (r ρ₀ s:ℝ)
    (i:I) (D:ℕ) (a b:U→ℝ) (hD:0<D) (heven:Even D)
    (hnonneg:∀j,0≤ρclass j) (htotal:∑j,ρclass j=1) (hlow:∀j,r≤ρclass j)
    (hclass:ρclass i/2*D=Fintype.card U) (hρlo:ρ₀ ≤ initialIndexDensity U D):
    let ρ:=initialIndexDensity U D
    let p:=ρ*(1/100)/2
    let k:=ρ*s/2
    let p₂:=(∑w,b w)/(D:ℝ)
    let k₂:=(∑w,a w)/(D:ℝ)
    let u:=2*(∑w,(1-1/100-s-a w-b w))/(D:ℝ)
    let m:=binaryClassMultiplicity D (Fintype.card U);
    (∑j,m j)=D/2 ∧
      (∀j,expandedBinaryProbability p k p₂ k₂ u j/2*D=(m j:ℝ)) ∧
      ((2*p+2*k+2*p₂+2*k₂+u=1) ∨ ∀j,r≤expandedBinaryProbability p k p₂ k₂ u j):=by
  intro ρ p k p₂ k₂ u m
  obtain ⟨hs,hm,hcase⟩:=long_binary_pruned_parameters ρclass r ρ₀ s i D a b hD heven hnonneg htotal hlow hclass hρlo
  refine ⟨hs,hm,?_⟩
  rcases hcase with hone | hboth
  · left
    have hDreal:(D:ℝ)≠0:=by exact_mod_cast (ne_of_gt hD)
    have hsize:ρ*(D:ℝ)=2*Fintype.card U:=by
      dsimp [ρ,initialIndexDensity]
      field_simp
    have hρhi:ρ≤1:=by linarith
    obtain ⟨_,_,hzero,_⟩:=long_binary_partition_parameters ρ₀ ρ s D a b hD heven hρlo hρhi hsize
    change 2*p+2*k+2*p₂+2*k₂+u=ρ at hzero
    exact hzero.trans hone
  · exact Or.inr hboth
end Oberwolfach
