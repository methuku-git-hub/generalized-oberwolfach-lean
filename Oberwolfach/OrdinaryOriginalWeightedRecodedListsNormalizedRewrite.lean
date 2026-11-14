module

public import Oberwolfach.OrdinaryOriginalWeightedRecodedListsNormalizedNoFinShape

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_weighted_core_recoded_lists_normalized_rewrite
    (K d m k:ℕ) (hd:2≤d) (hm:7≤m) (hlen:m+1=(k+2)*2)
    (ρ₀ smin θhost α θ:ℝ) (hρ₀:0<ρ₀) (hsmin:0<smin)
    (hθhost:1/2≤θhost) (hα:0<α) (hθ:0<θ) (hθ1:θ≤1/100) (hda:1/θ≤d)
    (hspace:1/(4*(d:ℝ))≤5*θ^2/256)
    (hratio:successorCycleRatio k+α/2≤1/2+α):
    OrdinaryOriginalWeightedRecodedListsNormalizedNoFinShape K d m k hd hm hlen ρ₀ smin θhost α θ
      hρ₀ hsmin hθhost hα hθ hθ1 hda hspace hratio :=by
  unfold OrdinaryOriginalWeightedRecodedListsNormalizedNoFinShape

  obtain ⟨BO,hBO,hweights⟩:=ordinary_original_regular_joint_seed_weights_with_normalization K k θhost α θ hα hθ hθhost hratio
  refine ⟨BO,hBO,?_⟩
  intro τ hτ
  obtain ⟨Nweights,hweights⟩:=hweights τ hτ d
  intro t ξ ζ χpair χlist ht hξ hζ hχpair hχlist
  have hBM:0<successorWeightUpper k (α/4):=(successorWeightConstants_pos k (α/4) (by positivity)).2
  obtain ⟨a,ha,Ncore,hcore⟩:=ordinary_original_regular_core_recoded_lists_candidate_direct_reserve K d m hd hm θ hθ hθ1 hda hspace ρ₀
    (successorWeightUpper k (α/4)) t ξ ζ smin χpair χlist hρ₀ hBM ht hξ hζ hsmin hχpair hχlist BO hBO
  refine ⟨a,ha,max Nweights Ncore,?_⟩
  intro n hn hn2 U _ _ hUn F hF hK i₀ rsv c D hslo hs1 hc hcEq hρlo hρ1 hD
    Allowed hAllowed hthreshold hClassReserve P hreg π hdegree hnoshort
  have hn0:0<n:=by omega
  obtain ⟨sampling,hcore⟩:=hcore n (by omega) hn2 U hUn F hF hK i₀ rsv c D hslo hs1 hc hcEq hρlo hρ1 hD
    Allowed hAllowed hClassReserve
  have hFin:candidateOriginalCoreRecodedListsFin_direct_reserve n=instDecidableEqFin n:=Subsingleton.elim _ _
  rw [hFin] at hcore
  obtain ⟨w,seed,hweight,hNorm,hzero,hseed⟩:=hweights n (by omega) hn0 U F hF hK Allowed hAllowed hthreshold P π D hreg hdegree
  have hseed':∃seed':(Fin (m+1)→Fin n)→ℝ,
      SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ
        (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) seed':=by
    rw [hlen]
    exact ⟨seed,hseed⟩
  obtain ⟨seed',hseed'⟩:=hseed'
  refine ⟨sampling,w,seed',hweight,hNorm,hzero,hseed',?_⟩
  intro γList βList lamList ζDel hγList hβList hlamList hζDel hdegList herrorList hmarginList hbudgetList R _ ν E εE p q s p₂ μ wM wO hE
  have hw0:∀i C,0≤w i C:=fun i C=>(hweight i C).1
  have hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i):=fun i C=>(hweight i C).2
  exact hcore P hreg π θhost α hθhost hα hdegree τ (successorWeightLower k (α/4)) seed'
    hseed' w hw0 hwupper hnoshort γList βList lamList ζDel hγList hβList hlamList hζDel hdegList herrorList hmarginList hbudgetList ν E εE hE
end Oberwolfach
