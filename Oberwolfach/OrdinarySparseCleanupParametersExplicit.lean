module

public import Oberwolfach.OrdinaryOutsideSparseCleanup

@[expose] public section
/-! Choose the sparse residual threshold before the order threshold. The
cleanup cap is the ceiling of a small linear fraction of the order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinarySparseCleanupScale (r:ℕ) (bV bU ν:ℝ):ℝ :=
  let A:ℝ:=4*(r:ℝ)+40
  (min (1/2:ℝ) (min (bV/(4*A)) (min (bU/(4*A)) (ν/(4*A)))))^2

theorem ordinary_sparse_cleanup_parameter_choice_explicit (r:ℕ) (hr:3≤r) (bV bU ν:ℝ)
    (hV:0<bV) (hU:0<bU) (hν:0<ν):
    ∃θ:ℝ,θ=ordinarySparseCleanupScale r bV bU ν ∧ 0<θ ∧ θ≤1 ∧ ∀(L:ℝ),0≤L→∃N:ℕ,
    ∀(n D E:ℕ),N≤n→E≤n*D→(D:ℝ)≤θ*n→∃K:ℕ,0<K ∧
      (E*r:ℕ)/(K:ℝ)+(K*r:ℕ)+((r:ℝ)+2)*(L+1)+4*(K+D:ℕ)<bV*n ∧
      (E:ℝ)/K+2*(K+D:ℕ)<bU*n ∧
      (E*r:ℕ)/(K:ℝ)+(D*r:ℕ)+((r:ℝ)+2)*(L+1)+8*(K+D:ℕ)<bV*n ∧
      (max (6*(K+D)) ((K+D)*r):ℝ)≤ν*n:=by
  let A:ℝ:=4*(r:ℝ)+40
  have hA:0<A:=by dsimp [A];positivity
  let κ:=min (1/2:ℝ) (min (bV/(4*A)) (min (bU/(4*A)) (ν/(4*A))))
  have hκ:0<κ:=lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hκ1:κ≤1/2:=min_le_left _ _
  have hκV:κ≤bV/(4*A):=(min_le_right _ _).trans (min_le_left _ _)
  have hκU:κ≤bU/(4*A):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hκν:κ≤ν/(4*A):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsmallV:A*κ≤bV/4:=by have hh:κ*(4*A)≤bV:=(le_div_iff₀ (by positivity:0<4*A)).mp hκV;nlinarith only [hh]
  have hsmallU:A*κ≤bU/4:=by have hh:κ*(4*A)≤bU:=(le_div_iff₀ (by positivity:0<4*A)).mp hκU;nlinarith only [hh]
  have hsmallν:A*κ≤ν/4:=by have hh:κ*(4*A)≤ν:=(le_div_iff₀ (by positivity:0<4*A)).mp hκν;nlinarith only [hh]
  have hκsq:κ^2≤κ:=by nlinarith only [hκ.le,hκ1,mul_nonneg hκ.le (by linarith:0≤1-κ)]
  refine ⟨κ^2,rfl,pow_pos hκ _,by nlinarith only [hκsq,hκ1],?_⟩
  intro L hL
  let C:ℝ:=((r:ℝ)+2)*(L+1)+(r:ℝ)+14
  let b:=min bV (min bU ν)
  have hb:0<b:=lt_min hV (lt_min hU hν)
  have hC:0<C:=by dsimp [C];positivity
  obtain ⟨N,hN⟩:=exists_nat_gt (max 1 (4*C/b))
  refine ⟨N,?_⟩
  intro n D E hn hE hD
  have hn1:1≤(n:ℝ):=(le_max_left _ _).trans (hN.le.trans (Nat.cast_le.mpr hn))
  have hn0:(0:ℝ)<n:=by linarith
  have hbV:b≤bV:=min_le_left _ _
  have hbU:b≤bU:=(min_le_right _ _).trans (min_le_left _ _)
  have hbν:b≤ν:=(min_le_right _ _).trans (min_le_right _ _)
  have hconstant:C<b*n/4:=by
    have ht:4*C/b<(n:ℝ):=(lt_of_le_of_lt (le_max_right _ _) hN).trans_le (Nat.cast_le.mpr hn)
    have hh:4*C<b*n:=by simpa only [mul_comm] using (div_lt_iff₀ hb).mp ht
    linarith
  have hCV:C<bV*n/4:=hconstant.trans_le (by nlinarith only [mul_le_mul_of_nonneg_right hbV hn0.le])
  have hCU:C<bU*n/4:=hconstant.trans_le (by nlinarith only [mul_le_mul_of_nonneg_right hbU hn0.le])
  have hCν:C<ν*n/4:=hconstant.trans_le (by nlinarith only [mul_le_mul_of_nonneg_right hbν hn0.le])
  let K:=Nat.ceil (κ*(n:ℝ))
  have hKpos:0<K:=Nat.ceil_pos.mpr (mul_pos hκ hn0)
  have hKlo:κ*(n:ℝ)≤K:=Nat.le_ceil _
  have hKhi:(K:ℝ)≤κ*n+1:=(Nat.ceil_lt_add_one (by positivity:0≤κ*(n:ℝ))).le
  have hDlin:(D:ℝ)≤κ*n:=hD.trans (mul_le_mul_of_nonneg_right hκsq hn0.le)
  have hEreal:(E:ℝ)≤(n:ℝ)*D:=by exact_mod_cast hE
  have hEbound:(E:ℝ)≤(n:ℝ)*(κ^2*n):=hEreal.trans (mul_le_mul_of_nonneg_left hD hn0.le)
  have hEr:((E*r:ℕ):ℝ)/(K:ℝ)≤r*κ*n:=by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hKpos)).mpr
    calc
      ((E*r:ℕ):ℝ)=(E:ℝ)*r:=by push_cast;ring
      _≤((n:ℝ)*(κ^2*n))*r:=mul_le_mul_of_nonneg_right hEbound (Nat.cast_nonneg _)
      _=(r*κ*n)*(κ*n):=by ring
      _≤(r*κ*n)*K:=mul_le_mul_of_nonneg_left hKlo (by positivity)
  have hEu:(E:ℝ)/(K:ℝ)≤κ*n:=by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hKpos)).mpr
    calc
      (E:ℝ)≤(n:ℝ)*(κ^2*n):=hEbound
      _=(κ*n)*(κ*n):=by ring
      _≤(κ*n)*K:=mul_le_mul_of_nonneg_left hKlo (by positivity)
  have hVlin:A*κ*n≤bV*n/4:=by nlinarith only [mul_le_mul_of_nonneg_right hsmallV hn0.le]
  have hUlin:A*κ*n≤bU*n/4:=by nlinarith only [mul_le_mul_of_nonneg_right hsmallU hn0.le]
  have hνlin:A*κ*n≤ν*n/4:=by nlinarith only [mul_le_mul_of_nonneg_right hsmallν hn0.le]
  have hKn:(K:ℝ)+D≤2*κ*n+1:=by linarith only [hKhi,hDlin]
  have hknon:0≤κ*(n:ℝ):=by positivity
  have hrnon:0≤(r:ℝ):=Nat.cast_nonneg _
  have hprod:0≤(r:ℝ)*(κ*(n:ℝ)):=mul_nonneg hrnon hknon
  have hc0:0≤((r:ℝ)+2)*(L+1):=by positivity
  have hKr:((K:ℝ)*(r:ℝ))≤(κ*n+1)*r:=mul_le_mul_of_nonneg_right hKhi hrnon
  have hVn:0<bV*(n:ℝ):=mul_pos hV hn0
  have hUn:0<bU*(n:ℝ):=mul_pos hU hn0
  have hνn:0<ν*(n:ℝ):=mul_pos hν hn0
  refine ⟨K,hKpos,?_,?_,?_,?_⟩
  · push_cast at hEr ⊢
    dsimp [A,C] at hVlin hCV
    nlinarith only [hEr,hKr,hKn,hVlin,hCV,hknon,hprod,hrnon,hc0,hVn]
  · push_cast at hEu ⊢
    dsimp [A,C] at hUlin hCU
    nlinarith only [hEu,hKn,hUlin,hCU,hknon,hprod,hrnon,hc0,hUn]
  · push_cast at hEr ⊢
    dsimp [A,C] at hVlin hCV
    have hDr:((D:ℝ)*(r:ℝ))≤(κ*n)*r:=mul_le_mul_of_nonneg_right hDlin (Nat.cast_nonneg _)
    nlinarith only [hEr,hDr,hKn,hVlin,hCV,hknon,hprod,hrnon,hc0,hVn]
  · push_cast
    apply max_le
    · dsimp [A,C] at hνlin hCν
      nlinarith only [hKn,hνlin,hCν,hknon,hprod,hrnon,hc0,hνn]
    · dsimp [A,C] at hνlin hCν
      have hrKn:((K:ℝ)+D)*(r:ℝ)≤(2*κ*n+1)*r:=mul_le_mul_of_nonneg_right hKn (Nat.cast_nonneg _)
      nlinarith only [hrKn,hνlin,hCν,hknon,hprod,hrnon,hc0,hνn]
end Oberwolfach
