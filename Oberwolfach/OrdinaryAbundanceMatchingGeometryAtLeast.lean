module

public import Oberwolfach.OrdinaryAbundanceSpacingAtLeast
public import Oberwolfach.LongRetainedPaddedIndexSet

@[expose] public section
/-! Choose the spacing, cutoff and matching rank before the host, preserving
both the specified abundant length and the reserved-path capacity margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem ordinary_abundance_matching_geometry_at_least (β θ:ℝ) (hβ:0<β) (hθ:0<θ) (rstar m dMin:ℕ):
    ∃d K rank:ℕ,dMin≤d ∧ 2≤d ∧ 3≤K ∧ rstar≤K ∧ 2≤rank ∧ 2*(m+1)≤rank ∧
      (∀i:Fin K,2*(longPaddedSeedExponent i+2)≤rank) ∧
      1/θ≤(d:ℝ) ∧ 1/(4*(d:ℝ))≤5*θ^2/256 ∧
      1/(2*(K:ℝ))≤β ∧
      5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2:=by
  obtain ⟨d,hdMin,hd2,hdθ,hspace,hbase⟩:=ordinary_abundance_spacing_choice_at_least θ hθ m dMin
  obtain ⟨K,hK3,hr,hβK,hcap⟩:=ordinary_abundance_capacity_cutoff β θ hβ hθ rstar m d hbase
  let rank:=max 2 (max (2*(m+1)) (Finset.univ.sup (fun i:Fin K=>2*(longPaddedSeedExponent i+2))))
  refine ⟨d,K,rank,hdMin,hd2,hK3,hr,le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),?_,hdθ,hspace,hβK,hcap⟩
  intro i
  have hi:2*(longPaddedSeedExponent i+2)≤
      Finset.univ.sup (fun j:Fin K=>2*(longPaddedSeedExponent j+2)):=
    Finset.le_sup (f:=fun j:Fin K=>2*(longPaddedSeedExponent j+2)) (Finset.mem_univ i)
  dsimp [rank]
  omega
end Oberwolfach
