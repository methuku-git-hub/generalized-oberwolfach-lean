module

public import Oberwolfach.MarkedSeedNormalization
public import Oberwolfach.SuccessorSequenceWeights
public import Oberwolfach.MarkedWheels

@[expose] public section
/-! A uniform bound for variable-hub seed coefficients, using the supplied
fixed density lower bound and no division by the marked interval marginal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem marked_variable_hub_seed_upper
    (P:SimpleGraph V) (π:Equiv.Perm V) (m b:ℕ) (hm:1≤m)
    (D τ A B p k pstar:ℝ) (hn:0<Fintype.card V)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hp1:p≤1) (hk1:k≤1)
    (s:U→ℝ) (hs:∀ u,pstar≤s u) (hs1:∀ u,s u≤1) (hB:0≤B)
    (w:(Fin (m+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π b D τ A B w):
    ∀ W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b
      (fun (_:V) (_:U)=>True) (fun _ _=>True),
    0≤w W.1.val/(D*p^m*k*(s W.2.val)^m) ∧
      w W.1.val/(D*p^m*k*(s W.2.val)^m)≤
        (2*B/pstar^(2*m+1))/(Fintype.card V:ℝ)^m :=by
  intro W
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hexp:m+1-2=m-1:=by omega
  have hupper:w W.1.val≤B/(Fintype.card V:ℝ)^(m-1):=by
    simpa only [hexp] using hw.upper W.1.val
  have hnonneg:=hw.nonneg W.1.val
  have hlo:(0:ℝ)/(Fintype.card V:ℝ)^(m-1)≤w W.1.val:=by simpa using hnonneg
  have hh:=marked_seed_coefficient_bounds m hm (Fintype.card V) D p k (s W.2.val) 0 B (w W.1.val) pstar
    hnR hDlo hDhi hpstar hp hk (hs W.2.val) hp1 hk1 (hs1 W.2.val) (by norm_num) hB hlo hupper
  refine ⟨?_,hh.2⟩
  have hD:0<D:=(half_pos hnR).trans_le hDlo
  have hp0:0<p:=hpstar.trans_le hp
  have hk0:0<k:=hpstar.trans_le hk
  have hs0:0<s W.2.val:=hpstar.trans_le (hs W.2.val)
  exact div_nonneg hnonneg (by positivity)
end Oberwolfach
