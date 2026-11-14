module

public import Oberwolfach.LongSeedUniformBoundsBridge
public import Oberwolfach.LongAllHubSeedCoefficients

@[expose] public section
/-! Uniform bounds for the manuscript's fixed long-class seed weights,
including all discarded indices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_assigned_actual_seed_uniform_bounds
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (b m K:ℕ) (hm:1≤m)
    (ni:Fin K→ℕ) (hni:∀i,1≤ni i) (θ:ℝ) (hθ0:0≤θ) (hθ1:θ≤1)
    (D τ A BM p k pstar:ℝ) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π b D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n)
    (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hp1:p≤1) (hk1:k≤1) (hBM:0≤BM)
    (hs:∀u,pstar≤longAssignedApproxOrdinaryWeight F hF K m θ u)
    (hs1:∀u,longAssignedApproxOrdinaryWeight F hF K m θ u≤1)
    (BO:Fin K→ℝ) (hBO:∀i,0≤BO i)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(ni i)):
    let s:=longAssignedApproxOrdinaryWeight F hF K m θ
    let η:=fun i u=>longAssignedKeptOrdinaryContribution F hF K θ i u/s u
    let wM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>weight W.1.val/(D*p^m*k*(s W.2.val)^m)
    let wO:=fun i (W:OrderedOrdinaryWheel (U:=U) π b (ni i+2))=>
      η i W.2*physicalOrdinaryTupleWeight (π:=π) (b:=b) (hni i) (w i) W.1.val/
        (((ni i+2:ℕ):ℝ)*D*p^(ni i+2)*(s W.2)^(ni i+1))
    (∀W,0≤wM W ∧ wM W≤(2*BM/pstar^(2*m+1))/(n:ℝ)^m) ∧
    (∀i W,0≤wO i W ∧ wO i W≤(2*BO i/pstar^(2*(ni i+2)))/(n:ℝ)^(ni i+1)):=by
  intro s η wM wO
  have hb:∀u,0<s u:=fun u=>lt_of_lt_of_le hpstar (hs u)
  have hcoeff:=long_assigned_all_ordinary_seed_coefficients hn F hF K m θ hθ0 hθ1 hb
  have hnV:0<Fintype.card (Fin n):=by simpa using hn
  have hh:=long_fixed_seed_uniform_bounds P π b m K hm hnV ni hni D τ A BM p k pstar weight hw
    (by simpa using hDlo) (by simpa using hDhi) hpstar hp hk hp1 hk1 hBM s η hs hs1
    (fun i u=>(hcoeff i u).1) (fun i u=>(hcoeff i u).2) BO hBO w hw0 (by simpa using hwupper)
  simpa only [Fintype.card_fin] using hh
end Oberwolfach
