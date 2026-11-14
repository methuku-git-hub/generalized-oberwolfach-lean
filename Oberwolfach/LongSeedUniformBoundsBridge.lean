module

public import Oberwolfach.SuccessorSeedBounds
public import Oberwolfach.PhysicalOrdinarySeedBound

@[expose] public section
/-! Uniform upper bounds for the actual marked and ordinary seed weights,
with the supplied hub-dependent spoke probabilities and coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem long_fixed_seed_uniform_bounds
    (P:SimpleGraph V) (π:Equiv.Perm V) (b m K:ℕ) (hm:1≤m) (hnV:0<Fintype.card V)
    (ni:Fin K→ℕ) (hni:∀i,1≤ni i)
    (D τ A BM p k pstar:ℝ) (weight:(Fin (m+1)→V)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π b D τ A BM weight)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hp1:p≤1) (hk1:k≤1) (hBM:0≤BM)
    (s:U→ℝ) (η:Fin K→U→ℝ) (hs:∀u,pstar≤s u) (hs1:∀u,s u≤1)
    (hη0:∀i u,0≤η i u) (hηhi:∀i u,η i u≤1/s u)
    (BO:Fin K→ℝ) (hBO:∀i,0≤BO i)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(Fintype.card V:ℝ)^(ni i)):
    let wM:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>weight W.1.val/(D*p^m*k*(s W.2.val)^m)
    let wO:=fun i (W:OrderedOrdinaryWheel (U:=U) π b (ni i+2))=>
      η i W.2*physicalOrdinaryTupleWeight (π:=π) (b:=b) (hni i) (w i) W.1.val/
        (((ni i+2:ℕ):ℝ)*D*p^(ni i+2)*(s W.2)^(ni i+1))
    (∀W,0≤wM W ∧ wM W≤(2*BM/pstar^(2*m+1))/(Fintype.card V:ℝ)^m) ∧
    (∀i W,0≤wO i W ∧ wO i W≤(2*BO i/pstar^(2*(ni i+2)))/(Fintype.card V:ℝ)^(ni i+1)):=by
  intro wM wO
  constructor
  · intro W
    exact successor_seed_nonneg_upper hw hm hnV hDlo hDhi p k (s W.2.val) pstar hpstar hp hk (hs W.2.val) hp1 hk1 (hs1 W.2.val) hBM W.1.val
  · intro i W
    exact physicalOrdinary_seed_upper (hni i) hnV (w i) (hw0 i) (BO i) (hBO i) (hwupper i)
      D p pstar hDlo hDhi hpstar hp hp1 s (η i) hs hs1 (hη0 i) (hηhi i) W
end Oberwolfach
