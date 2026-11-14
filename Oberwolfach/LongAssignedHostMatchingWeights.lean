module

public import Oberwolfach.LongAssignedPreparationReferenceReady
public import Oberwolfach.LongRetainedPaddedIndexSet

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_host_matching_weights (L₀:ℕ) (α:ℝ) (hα:0<α):
    ∃ m r k₀:ℕ,7≤m ∧ L₀≤m ∧ Even (m+1) ∧ 2≤r ∧ r+4=m ∧ r+4+1=(k₀+2)*2 ∧
      successorCycleRatio k₀+α/4≤1/2+α/2 ∧
    ∃ A BK:ℝ,0<A ∧ 0<BK ∧
    ∀ (K d:ℕ),0<K→2≤d→
    let nO:=fun i:Fin K=>max 1 (i.val-1);
    ∃ B:Fin K→ℝ,(∀ i,0<B i) ∧
    ∀ τ:ℝ,0<τ→∃ ε:ℝ,0<ε ∧ ε≤τ/4 ∧ ∃ N:ℕ,0<N ∧
    ∀ n:ℕ,N≤n→∀ (U:Type) [Fintype U]
      (F:U→SimpleGraph (Fin n)) (hF:∀ u,(F u).IsRegularOfDegree 2)
      (Allowed:Set ℕ) (hAllowed:Allowed.Nonempty) (hvalid:∀ r∈Allowed,3≤r)
      (hS:∀ u,AllowedCycleLengths (F u) Allowed)
      (θ ρ₀ ρ D:ℝ) (hθ:0<θ) (hθmax:θ≤1/100) (hρ₀:0<ρ₀)
      (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*Fintype.card U)
      (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
      (hclass:∀u,factorPreparationClass (F u) K=none)
      (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
      (hDlo:(Fintype.card (Fin n):ℝ)/2≤D) (hDhi:D≤2*Fintype.card (Fin n))
      (hreg:∀ v,|(G.degree v:ℝ)-D|≤ε*Fintype.card (Fin n))
      (hdeg:∀ v,(allowedThreshold Allowed+α)*Fintype.card (Fin n)≤(G.degree v:ℝ)),
    ∃ w:∀ i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ,
    ∃ wK:(Fin (m+1)→Fin n)→ℝ,
      (∀ i C,0≤w i C ∧ w i C≤B i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
      (∀ i∈longRetainedSeedIndices F hF K θ,∀ x y,
        (∑ C,if C.val.val.Adj x y then w i C else 0)=if G.Adj x y then 1 else 0) ∧
      (∀ i∈longRetainedSeedIndices F hF K θ,
        5*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*B i*(2*(3*d))/n≤τ ∧
        6*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*B i*(2*(3*d))+ε*n≤τ*D) ∧
      SuccessorSequenceWeightConditions G π (3*d) D τ A BK wK :=by
  obtain ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmargin,A,BK,hA,hBK,hcore⟩:=long_assigned_preparation_actual_reference_ready L₀ α hα
  refine ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmargin,A,BK,hA,hBK,?_⟩
  intro K d hK hd nO
  obtain ⟨B,hB,hcore⟩:=hcore K d hK hd
  refine ⟨B,hB,?_⟩
  intro τ hτ
  obtain ⟨ε,hε,hετ,N,hN,hcore⟩:=hcore τ hτ
  refine ⟨ε,hε,hετ,N,hN,?_⟩
  intro n hn U _ F hF Allowed hAllowed hvalid hS θ ρ₀ ρ D hθ hθmax hρ₀ hρlo hρ1 hD hsize hcut hclass G π hDlo hDhi hreg hdeg
  have hh:=hcore n hn U F hF Allowed hAllowed hvalid hS θ ρ₀ ρ D hθ hθmax hρ₀ hρlo hρ1 hD hsize hcut hclass G π hDlo hDhi hreg hdeg
  have hlen: nO = @longPaddedSeedExponent K:=by
    funext i
    dsimp [nO,longPaddedSeedExponent,longAssignedPaddedLength]
    omega
  change (fun i:Fin K=>max 1 (i.val-1)) = @longPaddedSeedExponent K at hlen
  rw [hlen] at hh
  obtain ⟨w,wK,hh⟩:=hh
  rcases hh with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hw,hedge,_,hbudget,hwK⟩
  refine ⟨w,wK,?_,?_,?_,hwK⟩
  · simpa only [Fintype.card_fin] using hw
  · intro i hi x y
    have hi':i∈Finset.univ.filter (fun i=>∃u,θ/(100*(K:ℝ))≤
        (((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i)).card:ℝ)/n)):=by
      simpa only [longRetainedSeedIndices,ordinaryAssignedFraction] using hi
    exact hedge ⟨i,hi'⟩ x y
  · intro i hi
    have hi':i∈Finset.univ.filter (fun i=>∃u,θ/(100*(K:ℝ))≤
        (((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i)).card:ℝ)/n)):=by
      simpa only [longRetainedSeedIndices,ordinaryAssignedFraction] using hi
    simpa only [Fintype.card_fin] using hbudget ⟨i,hi'⟩
end Oberwolfach
