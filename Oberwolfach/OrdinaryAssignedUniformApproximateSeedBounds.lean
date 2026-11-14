module

public import Oberwolfach.OrdinaryAssignedApproximateDensityBounds
public import Oberwolfach.LongSeedUniformBoundsBridge

@[expose] public section
/-! The ordinary-preparation seed coefficients are uniformly bounded by
constants chosen from the original density and weighting parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_assigned_uniform_approximate_seed_bounds
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c ρ₀ ρ D:ℝ) (d:ℕ) (hd:2≤d)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,factorPreparationClass (F w) K=some i₀)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (b m:ℕ) (hm:1≤m)
    (ni:Fin K→ℕ) (hni:∀i,1≤ni i) (idx:Fin K→Fin K)
    (τ A BM:ℝ) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π b D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n) (hBM:0≤BM)
    (BO:Fin K→ℝ) (hBO:∀i,0≤BO i)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(ni i)):
    let a:=ordinaryAssignedLongWeight F hF K θ c
    let s:=ordinaryAssignedShortWeight F hF K i₀ rsv θ c
    let p:=(∑u,(a u+s u))/D
    let η:=fun i u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u (idx i)
    let pstar:=min (1/2:ℝ) (ρ₀/4)
    let wM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>weight W.1.val/(D*p^(m+1)*(s W.2.val)^m)
    let wO:=fun i (W:OrderedOrdinaryWheel (U:=U) π b (ni i+2))=>
      η i W.2*physicalOrdinaryTupleWeight (π:=π) (b:=b) (hni i) (w i) W.1.val/
        (((ni i+2:ℕ):ℝ)*D*p^(ni i+2)*(s W.2)^(ni i+1));
    0<pstar ∧
    (∀W,0≤wM W ∧ wM W≤(2*BM/pstar^(2*m+1))/(n:ℝ)^m) ∧
    (∀i W,0≤wO i W ∧ wO i W≤(2*BO i/pstar^(2*(ni i+2)))/(n:ℝ)^(ni i+1)):= by
  intro a s p η pstar wM wO
  have hb:=ordinary_assigned_approximate_density_bounds hn F hF K hK i₀ rsv θ c ρ D d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρ1 hD hsize Allowed hAllowed hsclass hclass
  have hps:0<pstar:=by dsimp [pstar];positivity
  have hpsle:pstar≤min (1/2:ℝ) (ρ/4):=by
    dsimp [pstar]
    exact min_le_min (le_refl _) (by linarith)
  have hp:pstar≤p:=hpsle.trans hb.2.1
  have hslo:∀u,pstar≤s u:=fun u=>hpsle.trans (hb.2.2.2.1 u).1
  have hshi:∀u,s u≤1:=fun u=>(hb.2.2.2.1 u).2
  have hη:∀i u,0≤η i u ∧ η i u≤1/s u:=fun i u=>hb.2.2.2.2 (idx i) u
  have hnV:0<Fintype.card (Fin n):=by simpa using hn
  have hh:=long_fixed_seed_uniform_bounds P π b m K hm hnV ni hni D τ A BM p p pstar weight hw
    (by simpa using hDlo) (by simpa using hDhi) hps hp hp hb.2.2.1 hb.2.2.1 hBM s η
    hslo hshi (fun i u=>(hη i u).1) (fun i u=>(hη i u).2)
    BO hBO w hw0 (by simpa using hwupper)
  refine ⟨hps,?_,?_⟩
  · intro W
    have h:=hh.1 W
    change 0≤weight W.1.val/(D*p^m*p*(s W.2.val)^m) ∧
      weight W.1.val/(D*p^m*p*(s W.2.val)^m)≤(2*BM/pstar^(2*m+1))/(Fintype.card (Fin n):ℝ)^m at h
    simpa only [wM,pow_succ,mul_assoc,Fintype.card_fin] using h
  · simpa only [wO,Fintype.card_fin] using hh.2
end Oberwolfach
