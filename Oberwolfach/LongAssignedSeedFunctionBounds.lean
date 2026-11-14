module

public import Oberwolfach.LongAssignedSeedFunctions

@[expose] public section
/-! Uniform positive constants for the named actual seed functions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_assigned_named_seed_bounds
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (ni:Fin K→ℕ) (hni:∀i,1≤ni i)
    (τ A BM:ℝ) (hBM:0<BM) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(ni i)):
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((m:ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*m+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2))
    0<BMseed ∧ (∀i,0<BOseed i) ∧
    (∀W,0≤longAssignedMarkedSeed F hF K m d θ D π weight W ∧
      longAssignedMarkedSeed F hF K m d θ D π weight W≤BMseed/(n:ℝ)^m) ∧
    (∀i W,0≤longAssignedOrdinarySeed F hF K m d θ D P π ni hni w i W ∧
      longAssignedOrdinarySeed F hF K m d θ D P π ni hni w i W≤BOseed i/(n:ℝ)^(ni i+1)):=by
  intro pstar BMseed BOseed
  have h:=long_assigned_seed_bounds_from_preparation hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass P π ni hni τ A BM weight hw hDlo hDhi hBM.le BO (fun i=>(hBO i).le) w hw0 hwupper
  obtain ⟨hps,hM,hO⟩:=h
  refine ⟨?_,?_,?_,?_⟩
  · dsimp only [BMseed]
    exact div_pos (mul_pos (by norm_num) hBM) (pow_pos hps _)
  · intro i
    dsimp only [BOseed]
    exact div_pos (mul_pos (by norm_num) (hBO i)) (pow_pos hps _)
  · simpa only [longAssignedMarkedSeed,BMseed,pstar] using hM
  · simpa only [longAssignedOrdinarySeed,BOseed,pstar] using hO
end Oberwolfach
