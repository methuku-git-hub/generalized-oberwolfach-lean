module

public import Oberwolfach.MarkedVariableHubSeedBound
public import Oberwolfach.PhysicalOrdinarySeedBound

@[expose] public section
/-! The manuscript's original marked and ordinary seed coefficients satisfy
the bounds required by the common approximate-potential event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem approximate_seed_family_bounds
    {V U IM IO:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype IM] [Fintype IO] (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:1≤m)
    (D p₂ k₂ pstar BM:ℝ) (hn:0<Fintype.card V)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpstar:0<pstar) (hp:pstar≤p₂) (hk:pstar≤k₂) (hp1:p₂≤1) (hk1:k₂≤1) (hBM:0≤BM)
    (s:U→Bool→ℝ) (hslo:∀ u j,pstar≤s u j) (hshi:∀ u j,s u j≤1)
    (wM:IM→(Fin (m+1)→V)→ℝ) (τM AM:IM→ℝ)
    (hwM:∀ i,SuccessorSequenceWeightConditions P π (3*d) D (τM i) (AM i) BM (wM i))
    (jM:IM→Bool) (nO:IO→ℕ) (hnO:∀ i,1≤nO i) (BO:IO→ℝ) (hBO:∀ i,0≤BO i)
    (wO:∀ i,OrdinaryCycle P (nO i+2)→ℝ)
    (hwO0:∀ i C,0≤wO i C) (hwO:∀ i C,wO i C≤BO i/(Fintype.card V:ℝ)^(nO i))
    (η:IO→U→ℝ) (jO:IO→Bool) (hη0:∀ i u,0≤η i u) (hηhi:∀ i u,η i u≤1/s u (jO i)):
    let seedM:=fun i (W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_:V) (_:U)=>True) (fun _ _=>True))=>
        wM i W.1.val/(D*p₂^m*k₂*(s W.2.val (jM i))^m)
    let seedO:=fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (nO i+2))=>
      η i W.2*physicalOrdinaryTupleWeight (π:=π) (b:=3*d) (hnO i) (wO i) W.1.val/
        (((nO i+2:ℕ):ℝ)*D*p₂^(nO i+2)*(s W.2 (jO i))^(nO i+1));
    (∀ i W,0≤seedM i W ∧ seedM i W≤(2*BM/pstar^(2*m+1))/(Fintype.card V:ℝ)^m) ∧
    (∀ i W,0≤seedO i W ∧ seedO i W≤(2*BO i/pstar^(2*(nO i+2)))/(Fintype.card V:ℝ)^(nO i+1)):=by
  intro seedM seedO
  constructor
  · intro i W
    exact marked_variable_hub_seed_upper P π m (3*d) hm D (τM i) (AM i) BM p₂ k₂ pstar hn
      hDlo hDhi hpstar hp hk hp1 hk1 (fun u=>s u (jM i)) (fun u=>hslo u (jM i)) (fun u=>hshi u (jM i)) hBM (wM i) (hwM i) W
  · intro i W
    exact physicalOrdinary_seed_upper (P:=P) (π:=π) (b:=3*d) (hnO i) hn (wO i) (hwO0 i) (BO i) (hBO i) (hwO i)
      D p₂ pstar hDlo hDhi hpstar hp hp1 (fun u=>s u (jO i)) (η i)
      (fun u=>hslo u (jO i)) (fun u=>hshi u (jO i)) (hη0 i) (hηhi i) W
end Oberwolfach
