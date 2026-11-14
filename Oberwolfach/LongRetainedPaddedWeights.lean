module

public import Oberwolfach.PreparationPaddedWeightsUniformD
public import Oberwolfach.LongRetainedPaddedIndexSet

@[expose] public section
/-! Preparation supplies fractional weights exactly for the lengths retained
by the actual factor family. The hierarchy is fixed before the allowed set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_retained_padded_weights_uniform_d
    (L:ℕ) (α:ℝ) (hα:0<α):
    ∃ m:ℕ,3≤m ∧ L≤m ∧ Even (m+1) ∧
    ∃ A BK:ℝ,0<A ∧ 0<BK ∧
    ∀ K:ℕ,∃ B:Fin K→ℝ,(∀i,0<B i) ∧
    ∀ (d:ℕ),2≤d→∀ τ:ℝ,0<τ→∃ ε:ℝ,0<ε ∧ ε≤τ/4 ∧ ∃ N:ℕ,1≤N ∧
    ∀ n:ℕ,N≤n→∀ (U:Type) [Fintype U]
      (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (Allowed:Set ℕ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (D θ:ℝ),
      0<K→0<θ→Allowed.Nonempty→(∀r∈Allowed,3≤r)→
      (∀u,AllowedCycleLengths (F u) Allowed)→
      ((n:ℝ)/2≤D)→D≤2*n→
      (∀v,|(G.degree v:ℝ)-D|≤ε*n)→
      (∀v,(allowedThreshold Allowed+α)*n≤(G.degree v:ℝ))→
    ∃ w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ,
    ∃ wK:(Fin (m+1)→Fin n)→ℝ,
      (∀i C,0≤w i C ∧ w i C≤B i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
      (∀i∈longRetainedSeedIndices F hF K θ,∀x y,
        (∑C,if C.val.val.Adj x y then w i C else 0)=if G.Adj x y then 1 else 0) ∧
      (∀i∉longRetainedSeedIndices F hF K θ,∀C,w i C=0) ∧
      (∀i∈longRetainedSeedIndices F hF K θ,
        5*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*B i*(2*(3*d))/n≤τ ∧
        6*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*B i*(2*(3*d))+ε*n≤τ*D) ∧
      SuccessorSequenceWeightConditions G π (3*d) D τ A BK wK :=by
  obtain ⟨m,hm,hL,heven,A,BK,hA,hBK,hcore⟩:=preparation_padded_weights_from_allowed_threshold_uniform_d L α hα
  refine ⟨m,hm,hL,heven,A,BK,hA,hBK,?_⟩
  intro K
  obtain ⟨B,hB,hcore⟩:=hcore K longPaddedSeedExponent long_padded_seed_exponent_positive
  refine ⟨B,hB,?_⟩
  intro d hd τ hτ
  obtain ⟨ε,hε,hετ,N,hN,hcore⟩:=hcore d hd τ hτ
  refine ⟨ε,hε,hετ,N,hN,?_⟩
  intro n hn U _ F hF Allowed G π D θ hK hθ hAllowed hvalid hFallowed hDlo hDhi hreg hdeg
  have hn0:0<n:=by omega
  have hmem:∀i:{i:Fin K // i∈longRetainedSeedIndices F hF K θ},longPaddedSeedExponent i.val+2∈Allowed:=
    fun i=>long_retained_padded_length_allowed hn0 F hF Allowed hFallowed K hK θ hθ i.val i.property
  obtain ⟨w,wK,hw,he,hoff,hbudget,hwK⟩:=hcore (Fin n) (by simpa using hn)
    (longRetainedSeedIndices F hF K θ) Allowed G π D hAllowed hvalid
    (by simpa using hDlo) (by simpa using hDhi) (by simpa using hreg) hmem (by simpa using hdeg)
  refine ⟨w,wK,by simpa using hw,?_,hoff,?_,hwK⟩
  · intro i hi
    exact he ⟨i,hi⟩
  · intro i hi
    simpa using hbudget ⟨i,hi⟩
end Oberwolfach
