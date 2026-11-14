module

public import Oberwolfach.LongAssignedActualSeedBounds
public import Oberwolfach.LongActualUniformDensity
public import Oberwolfach.LongActualProbabilityBounds

@[expose] public section
/-! The manuscript's preparation hypotheses imply the fixed seed bounds;
their positive density constant is chosen before the factor family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_assigned_seed_bounds_from_preparation
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (ni:Fin K→ℕ) (hni:∀i,1≤ni i)
    (τ A BM:ℝ) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n) (hBM:0≤BM)
    (BO:Fin K→ℝ) (hBO:∀i,0≤BO i)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(ni i)):
    let s:=longAssignedApproxOrdinaryWeight F hF K m θ
    let a:=longAssignedApproxMarkedWeight F hF K m θ
    let p:=(∑u,s u)/D
    let k:=(∑u,a u)/D
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((m:ℝ)+1))))
    let η:=fun i u=>longAssignedKeptOrdinaryContribution F hF K θ i u/s u
    let wM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>weight W.1.val/(D*p^m*k*(s W.2.val)^m)
    let wO:=fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (ni i+2))=>
      η i W.2*physicalOrdinaryTupleWeight (π:=π) (b:=3*d) (hni i) (w i) W.1.val/
        (((ni i+2:ℕ):ℝ)*D*p^(ni i+2)*(s W.2)^(ni i+1))
    0<pstar ∧
    (∀W,0≤wM W ∧ wM W≤(2*BM/pstar^(2*m+1))/(n:ℝ)^m) ∧
    (∀i W,0≤wO i W ∧ wO i W≤(2*BO i/pstar^(2*(ni i+2)))/(n:ℝ)^(ni i+1)):=by
  intro s a p k pstar η wM wO
  have hl:=long_assigned_actual_uniform_seed_density hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
  have hu:=long_assigned_actual_probability_upper hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
  obtain ⟨hps,hp,hk,hs⟩:=hl
  obtain ⟨hp1,hk1,hs1⟩:=hu
  have hh:=long_assigned_actual_seed_uniform_bounds hn F hF P π (3*d) m K (by omega) ni hni θ hθ0 (by linarith)
    D τ A BM p k pstar weight hw hDlo hDhi hps hp hk hp1 hk1 hBM hs hs1 BO hBO w hw0 hwupper
  exact ⟨hps,hh⟩
end Oberwolfach
