module

public import Oberwolfach.LongRetainedPaddedWeights
public import Oberwolfach.LongSeedBoundsFromPreparation

@[expose] public section
/-! Uniform parent and seed weights for the manuscript's retained family;
no parent decomposition is requested for discarded cycle lengths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_retained_seed_weights_uniform_d
    (L:ℕ) (α:ℝ) (hα:0<α):
    ∃ m:ℕ,7≤m ∧ L≤m ∧ Even (m+1) ∧
    ∃ A BK:ℝ,0<A ∧ 0<BK ∧
    ∀ K:ℕ,∃ B:Fin K→ℝ,(∀i,0<B i) ∧
    ∀ (d:ℕ),2≤d→∀ τ:ℝ,0<τ→∃ ε:ℝ,0<ε ∧ ε≤τ/4 ∧ ∃ N:ℕ,1≤N ∧
    ∀ n:ℕ,N≤n→∀ (U:Type) [Fintype U] [DecidableEq U]
      (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (Allowed:Set ℕ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
      (D θ ρ₀ ρ:ℝ),
      0<K→0<θ→θ≤1/100→0<ρ₀→ρ₀≤ρ→ρ≤1→0<D→
      ρ*D=2*Fintype.card U→(1/((m:ℝ)+1))/(d:ℝ)≤θ→
      (∀u,factorPreparationClass (F u) K=none)→
      Allowed.Nonempty→(∀r∈Allowed,3≤r)→(∀u,AllowedCycleLengths (F u) Allowed)→
      ((n:ℝ)/2≤D)→D≤2*n→(∀v,|(G.degree v:ℝ)-D|≤ε*n)→
      (∀v,(allowedThreshold Allowed+α)*n≤(G.degree v:ℝ))→
    ∃ w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ,
    ∃ wK:(Fin (m+1)→Fin n)→ℝ,
    let s:=longAssignedApproxOrdinaryWeight F hF K m θ
    let a:=longAssignedApproxMarkedWeight F hF K m θ
    let p:=(∑u,s u)/D
    let k:=(∑u,a u)/D
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((m:ℝ)+1))))
    let η:=fun i u=>longAssignedKeptOrdinaryContribution F hF K θ i u/s u
    let wM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>wK W.1.val/(D*p^m*k*(s W.2.val)^m)
    let wO:=fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>
      η i W.2*physicalOrdinaryTupleWeight (π:=π) (b:=3*d) (long_padded_seed_exponent_positive i) (w i) W.1.val/
        (((longPaddedSeedExponent i+2:ℕ):ℝ)*D*p^(longPaddedSeedExponent i+2)*(s W.2)^(longPaddedSeedExponent i+1))
    (∀i∈longRetainedSeedIndices F hF K θ,∀x y,
      (∑C,if C.val.val.Adj x y then w i C else 0)=if G.Adj x y then 1 else 0) ∧
    (∀i∉longRetainedSeedIndices F hF K θ,∀C,w i C=0) ∧
    (∀i∈longRetainedSeedIndices F hF K θ,
      5*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*B i*(2*(3*d))/n≤τ ∧
      6*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*B i*(2*(3*d))+ε*n≤τ*D) ∧
    SuccessorSequenceWeightConditions G π (3*d) D τ A BK wK ∧ 0<pstar ∧
    (∀W,0≤wM W ∧ wM W≤(2*BK/pstar^(2*m+1))/(n:ℝ)^m) ∧
    (∀i W,0≤wO i W ∧ wO i W≤(2*B i/pstar^(2*(longPaddedSeedExponent i+2)))/(n:ℝ)^(longPaddedSeedExponent i+1)) :=by
  obtain ⟨m,hm,hL,heven,A,BK,hA,hBK,hcore⟩:=long_retained_padded_weights_uniform_d (max L 7) α hα
  have hm7:7≤m:=le_trans (le_max_right _ _) hL
  have hmL:L≤m:=le_trans (le_max_left _ _) hL
  refine ⟨m,hm7,hmL,heven,A,BK,hA,hBK,?_⟩
  intro K
  obtain ⟨B,hB,hcore⟩:=hcore K
  refine ⟨B,hB,?_⟩
  intro d hd τ hτ
  obtain ⟨ε,hε,hετ,N,hN,hcore⟩:=hcore d hd τ hτ
  refine ⟨ε,hε,hετ,N,hN,?_⟩
  intro n hn U _ _ F hF Allowed G π D θ ρ₀ ρ hK hθ hθhi hρ₀ hρlo hρ1 hD hsize hcut hclass hAllowed hvalid hFallowed hDlo hDhi hreg hdeg
  obtain ⟨w,wK,hw,he,hoff,hbudget,hwK⟩:=hcore n hn U F hF Allowed G π D θ hK hθ hAllowed hvalid hFallowed hDlo hDhi hreg hdeg
  refine ⟨w,wK,?_,?_,?_,hwK,?_⟩
  · exact he
  · exact hoff
  · exact hbudget
  · have hbound:=long_assigned_seed_bounds_from_preparation (by omega) F hF Allowed hFallowed K hK m d hm7 hd
      θ ρ₀ ρ D hθ.le hθhi hρ₀ hρlo hρ1 hD hsize hcut hclass G π longPaddedSeedExponent long_padded_seed_exponent_positive
      τ A BK wK hwK hDlo hDhi hBK.le B (fun i=>(hB i).le) w (fun i C=>(hw i C).1) (fun i C=>(hw i C).2)
    exact hbound
end Oberwolfach
