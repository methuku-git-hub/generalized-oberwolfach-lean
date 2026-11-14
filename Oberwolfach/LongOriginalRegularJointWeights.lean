module

public import Oberwolfach.PreparationWeightsFromAllowedThreshold
public import Oberwolfach.OrdinaryAssignedNonretainedZero
public import Oberwolfach.OrdinaryCycleSumInstance

@[expose] public section
/-! Select the long successor length and construct its marked weights and
all retained ordinary-cycle weights directly on the original regular host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := 100000) longOriginalJointWeightsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_original_regular_joint_weights
    (L:ℕ) (α:ℝ) (hα:0<α):
    ∃m:ℕ,7≤m ∧ L≤m ∧ Even (m+1) ∧
    ∃A BM:ℝ,0<A ∧ 0<BM ∧
    ∀(K d:ℕ),2≤d→∀θ:ℝ,0<θ→
    ∃BO:Fin K→ℝ,(∀i,0<BO i) ∧ ∀τ:ℝ,0<τ→∃N:ℕ,1≤N ∧
    ∀n:ℕ,N≤n→0<n→∀(U:Type) [Fintype U] (F:U→SimpleGraph (Fin n))
      (hF:∀u,(F u).IsRegularOfDegree 2) (hK:0<K) (Allowed:Set ℕ)
      (hSet:Allowed.Nonempty) (hValid:∀s∈Allowed,3≤s) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (D:ℕ),
    P.IsRegularOfDegree D→(allowedThreshold Allowed+α)*(n:ℝ)≤D→
    ∃w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ,
    ∃seed:(Fin (m+1)→Fin n)→ℝ,
      (∀i C,0≤w i C ∧ w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
      (∀i∈longRetainedSeedIndices F hF K θ,∀x y,
        (∑C,if C.val.val.Adj x y then w i C else 0)=if P.Adj x y then 1 else 0) ∧
      (∀i∉longRetainedSeedIndices F hF K θ,∀C,w i C=0) ∧
      SuccessorSequenceWeightConditions P π (3*d) D τ A BM seed :=by
  obtain ⟨m,hm,hL,heven,A,BM,hA,hBM,hchoose⟩:=
    preparation_weights_from_allowed_threshold (max 7 L) α hα
  refine ⟨m,by omega,by omega,heven,A,BM,hA,hBM,?_⟩
  intro K d hd θ hθ
  obtain ⟨BO,hBO,hchoose⟩:=hchoose K d hd (fun i=>longPaddedSeedExponent i)
    (fun i=>long_padded_seed_exponent_positive i)
  refine ⟨BO,hBO,?_⟩
  intro τ hτ
  obtain ⟨ε,hε,hετ,N,hN,hchoose⟩:=hchoose τ hτ
  refine ⟨N,hN,?_⟩
  intro n hn hn0 U _ F hF hK Allowed hSet hValid hAllowed P π D hreg hdegree
  letI:Nonempty (Fin n):=⟨⟨0,hn0⟩⟩
  let S:=longRetainedSeedIndices F hF K θ
  have hmem:∀i:{i:Fin K // i∈S},longPaddedSeedExponent i.val+2∈Allowed:=by
    intro i
    exact long_retained_padded_length_allowed hn0 F hF Allowed hAllowed K hK θ hθ i.val i.property
  have hhalf:1/2≤allowedThreshold Allowed:=allowedThreshold_half_le hSet hValid
  have hnR:0≤(n:ℝ):=by positivity
  have hDlo:(Fintype.card (Fin n):ℝ)/2≤D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤allowedThreshold Allowed+α by linarith) hnR
    simpa only [Fintype.card_fin] using (show (n:ℝ)/2≤D by nlinarith only [hh,hdegree])
  have hDn:D≤n:=by
    have hh:=Finset.card_le_univ (P.neighborFinset (⟨0,hn0⟩:Fin n))
    simpa only [SimpleGraph.card_neighborFinset_eq_degree,hreg ⟨0,hn0⟩,Fintype.card_fin] using hh
  have hDhi:(D:ℝ)≤2*Fintype.card (Fin n):=by
    have hh:(D:ℝ)≤n:=by exact_mod_cast hDn
    simpa only [Fintype.card_fin] using (show (D:ℝ)≤2*n by nlinarith)
  have hnear:∀v,|(P.degree v:ℝ)-D|≤ε*Fintype.card (Fin n):=by
    intro v
    rw [hreg v]
    simp only [sub_self,abs_zero]
    positivity
  have hmin:∀v,(allowedThreshold Allowed+α)*Fintype.card (Fin n)≤(P.degree v:ℝ):=by
    intro v
    simpa only [hreg v,Fintype.card_fin] using hdegree
  obtain ⟨w,seed,hw,he,hbudget,hseed⟩:=hchoose (Fin n) (by simpa using hn) S Allowed P π D
    hSet hValid hDlo hDhi hnear hmem hmin
  let wall:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ:=
    fun i C=>if hi:i∈S then w ⟨i,hi⟩ C else 0
  refine ⟨wall,seed,?_,?_,?_,?_⟩
  · intro i C
    by_cases hi:i∈S
    · simpa only [wall,dif_pos hi,Fintype.card_fin] using hw ⟨i,hi⟩ C
    · simp only [wall,dif_neg hi]
      exact ⟨le_rfl,div_nonneg (hBO i).le (by positivity)⟩
  · intro i hi x y
    change i∈S at hi
    have hh:=he ⟨i,hi⟩ x y
    simpa only [wall,dif_pos hi] using hh
  · intro i hi C
    change i∉S at hi
    simp only [wall,dif_neg hi]
  · exact hseed
end Oberwolfach
