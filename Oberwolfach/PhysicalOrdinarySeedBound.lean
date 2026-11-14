module

public import Oberwolfach.OrderedOrdinaryWheelResources
public import Oberwolfach.PhysicalOrdinaryTupleWeight
public import Oberwolfach.MarkedSeedNormalization

@[expose] public section
/-! Uniform seed bound with the actual fixed hub coefficients and spoke
marginals; no marked marginal is placed in a denominator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {P:SimpleGraph V} {π:Equiv.Perm V} {b n:ℕ}

theorem physicalOrdinary_seed_upper (hn:1≤n) (hnV:0<Fintype.card V)
    (w:OrdinaryCycle P (n+2)→ℝ) (hw:∀ C,0≤w C) (B:ℝ) (hB:0≤B)
    (hb:∀ C,w C≤B/(Fintype.card V:ℝ)^n)
    (D p pstar:ℝ) (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpstar:0<pstar) (hp:pstar≤p) (hp1:p≤1)
    (s η:U→ℝ) (hs:∀ u,pstar≤s u) (hs1:∀ u,s u≤1)
    (hη0:∀ u,0≤η u) (hηhi:∀ u,η u≤1/s u):
    ∀ W:OrderedOrdinaryWheel (U:=U) π b (n+2),
    0≤η W.2*physicalOrdinaryTupleWeight (π:=π) (b:=b) hn w W.1.val/
      (((n+2:ℕ):ℝ)*D*p^(n+2)*(s W.2)^(n+1)) ∧
    η W.2*physicalOrdinaryTupleWeight (π:=π) (b:=b) hn w W.1.val/
      (((n+2:ℕ):ℝ)*D*p^(n+2)*(s W.2)^(n+1))≤
      (2*B/pstar^(2*(n+2)))/(Fintype.card V:ℝ)^(n+1):=by
  intro W
  let x:ℝ:=physicalOrdinaryTupleWeight (π:=π) (b:=b) hn w W.1.val
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hnV
  have hD:0<D:=(half_pos hnR).trans_le hDlo
  have hp0:0<p:=hpstar.trans_le hp
  have hs0:0<s W.2:=hpstar.trans_le (hs W.2)
  have hr:(1:ℝ)≤((n+2:ℕ):ℝ):=by exact_mod_cast (show 1≤n+2 by omega)
  have hr0:0<((n+2:ℕ):ℝ):=lt_of_lt_of_le (by norm_num) hr
  have hx0:0≤x:=physicalOrdinaryTupleWeight_nonneg hn w hw _
  have hxhi:x≤B/(Fintype.card V:ℝ)^n:=physicalOrdinaryTupleWeight_upper hn w B hB hb _
  have hcore:=marked_seed_coefficient_bounds (n+1) (by omega) (Fintype.card V) D p p (s W.2) 0 B x pstar
    hnR hDlo hDhi hpstar hp hp (hs W.2) hp1 hp1 (hs1 W.2) (by norm_num) hB
    (by simpa using hx0) (by simpa using hxhi)
  let core:ℝ:=x/(D*p^(n+1)*p*(s W.2)^(n+1))
  have hcore0:0≤core:=by dsimp [core];positivity
  have heta:η W.2/((n+2:ℕ):ℝ)≤1/pstar:=by
    calc
      _ ≤ η W.2:=div_le_self (hη0 W.2) hr
      _ ≤ 1/s W.2:=hηhi W.2
      _ ≤ 1/pstar:=one_div_le_one_div_of_le hpstar (hs W.2)
  have hseed:η W.2*x/(((n+2:ℕ):ℝ)*D*p^(n+2)*(s W.2)^(n+1))=
      (η W.2/((n+2:ℕ):ℝ))*core:=by
    dsimp [core]
    rw [pow_succ']
    ring
  constructor
  · exact div_nonneg (mul_nonneg (hη0 W.2) hx0) (by positivity)
  · change η W.2*x/(((n+2:ℕ):ℝ)*D*p^(n+2)*(s W.2)^(n+1))≤_
    rw [hseed]
    calc
      _ ≤ (1/pstar)*core:=mul_le_mul_of_nonneg_right heta hcore0
      _ ≤ (1/pstar)*((2*B/pstar^(2*(n+1)+1))/(Fintype.card V:ℝ)^(n+1)):=
        mul_le_mul_of_nonneg_left hcore.2 (by positivity)
      _ = _:=by
        have hexp:2*(n+2)=2*(n+1)+1+1:=by omega
        rw [hexp,pow_succ]
        field_simp
        <;> ring
end Oberwolfach
