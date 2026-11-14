module

public import Oberwolfach.FirstVortexOriginalMarginLongRepeatedPositiveCutoff
public import Oberwolfach.FactorPrunedRemovalReassemblyFromCopies
public import Oberwolfach.FactorDecompositionSingleCopy
public import Oberwolfach.UniformGrid

@[expose] public section
/-! Remove all small classes using the proved original-margin long-factor
case and a separately stated ordinary-factor input, then assemble the
remaining classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem original_margin_pruned_long_remaining_reduction (α:ℝ) (hα:0<α):
    ∃K N:ℕ,3≤K ∧ ∀n≥N,∀Allowed:Set ℕ,Allowed.Nonempty→(∀s∈Allowed,3≤s)→
    ∀(D:ℕ) (G:SimpleGraph (Fin n)) (F:Fin (D/2)→SimpleGraph (Fin n)),
      G.IsRegularOfDegree D→Even D→(allowedThreshold Allowed+α)*(n:ℝ)≤D→
      (∀w,(F w).IsRegularOfDegree 2)→(∀w,AllowedCycleLengths (F w) Allowed)→
    ∀κL κS:ℝ,0≤κL→0≤κS→κL≤α/1000→κS≤α/(1000*(K:ℝ))→
    let classify:=fun w=>factorPreparationClass (F w) K
    let fibres:=fun j:Option (Fin K)=>Finset.univ.filter (fun w=>classify w=j)
    let small:=fun j:Option (Fin K)=>((fibres j).card:ℝ)<(if j=none then κL*n else κS*n)
    let removed:=Finset.univ.filter (fun w=>small (classify w))
    let e:Fin (Fintype.card {i:Fin (D/2) // i∉removed})≃{i:Fin (D/2) // i∉removed}:=
      (Fintype.equivFin {i:Fin (D/2) // i∉removed}).symm;
    (∀P:SimpleGraph (Fin n),∀d:ℕ,P.IsRegularOfDegree d→Even d→
      (allowedThreshold Allowed+α/2)*(n:ℝ)≤d→∀w∈removed,classify w≠none→
      ∃H:SimpleGraph (Fin n),H≤P ∧ H.IsRegularOfDegree 2 ∧ Nonempty (H ≃g F w))→
    (∀R:SimpleGraph (Fin n),R.IsRegularOfDegree (D-2*removed.card)→R≤G→
      (allowedThreshold Allowed+α/2)*(n:ℝ)≤((D-2*removed.card:ℕ):ℝ)→
      HasFactorDecomposition R (fun j=>F (e j).val))→
    HasFactorDecomposition G F :=by
  obtain ⟨K,N,hK,hLong⟩:=first_vortex_original_margin_long_repeated_factor_positive_cutoff α hα
  refine ⟨K,max N 1,hK,?_⟩
  intro n hn Allowed hAllowed hValid D G F hG hEven hdegree hF hFAllowed κL κS hL0 hS0 hL hS classify fibres small removed e hOrd hClasses
  have hnpos:0<n:=by omega
  have hδ:0≤allowedThreshold Allowed:=allowedThreshold_nonneg hAllowed
  apply factor_pruned_removal_reassembly_from_copies hnpos K (by omega) classify D (allowedThreshold Allowed) α κL κS hδ hα hL0 hS0 hL hS G hG hEven hdegree F hF
  · intro P d hp he hd w hw
    by_cases hc:classify w=none
    · have hdec:=hLong n (by omega) P d hp he (F w) (hF w) Allowed hAllowed hValid (hFAllowed w) hc hd
      have hnR:0<(n:ℝ):=by exact_mod_cast hnpos
      have hbound:0<((allowedThreshold Allowed+α/2)*(n:ℝ)):=mul_pos (by linarith) hnR
      have hdpos:0<d:=by exact_mod_cast (lt_of_lt_of_le hbound hd)
      have hdhalf:0<d/2:=by have hdiv:=he.two_dvd;omega
      exact factor_decomposition_single_copy hdhalf P (F w) (hF w) hdec
    · exact hOrd P d hp he hd w hw hc
  · exact hClasses
end Oberwolfach
