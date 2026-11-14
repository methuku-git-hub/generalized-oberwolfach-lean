module

public import Oberwolfach.LongAssignedSeedFunctionBounds
public import Oberwolfach.LongAssignedMixedPhysicalDeletion

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

theorem long_assigned_named_seed_physical_deletion_stability
    (hn:0<n) (hu:Fintype.card U≤n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (ni:Fin K→ℕ) (hni:∀i,1≤ni i)
    (τ A BM:ℝ) (hBM:0<BM) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(ni i))
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (δ:ℝ)
    (hDel:∀x,(Del.degree x:ℝ)≤δ):
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((m:ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*m+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2))
    let ℓ:=fun i=>ni i+2
    let Wm:=longAssignedMarkedSeed F hF K m d θ D π weight
    let Wo:=longAssignedOrdinarySeed F hF K m d θ D P π ni hni w
    let W:=longMixedSeedWeight Wm Wo
    let R:=longRawHubResources (U:=U) π d m ℓ
    let state:=longRawHubState P π d raw g j
    let S:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let survived:=fun z=>decide (z∈S)
    ∀(i:Option (Fin K)) (root:LongRawHubResource n U) (target:ℝ),
      |resourcePatternLoad (R i) (W i) (fun _ _=>true) root survived-target|≤
      |resourcePatternLoad (R i) (W i) (fun _ _=>true) root state-target|+
        match i with
        | none => 10*δ*((m:ℝ)+1)^4*BMseed/(n:ℝ)
        | some i => 10*δ*((ni i:ℝ)+2)^4*BOseed i/(n:ℝ) :=by
  intro pstar BMseed BOseed ℓ Wm Wo W R state S survived
  have hb:=long_assigned_named_seed_bounds hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass P π ni hni τ A BM hBM weight hw hDlo hDhi BO hBO w hw0 hwupper
  obtain ⟨hBm,hBo,hwm,hwo⟩:=hb
  have hh:=long_assigned_mixed_seed_load_after_physical_deletion hn hu
    F hF m d (by omega) θ D P Del π ni hni w weight BMseed BOseed hBm.le (fun i=>(hBo i).le) hwm hwo raw g j δ hDel
  exact hh
end Oberwolfach
