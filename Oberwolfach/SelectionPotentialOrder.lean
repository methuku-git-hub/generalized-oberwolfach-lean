module

public import Oberwolfach.AdaptiveSelectionPotential
public import Oberwolfach.AsymptoticMargins

@[expose] public section

/-! The uniform order choice for bounded-degree selection. The scale
p*sqrt(p)*n equals p^(3/2)*n for p>0. The estimate is uniform in the
number of supports and in the entire fixed family of tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selectionPotential_zero_bound {I : Type*} [Fintype I] {N : ℕ}
    (active : Fin N→I→Prop) (q M L : ℝ) (hq : 0≤q)
    (hcount : (Fintype.card I:ℝ)≤L)
    (hremaining : ∀ x,(selectionRemaining active 0 x:ℝ)≤M) :
    selectionPotential active q 0 (fun _=>0)≤L*Real.exp (q*M) := by
  have hbase : 1+q≤Real.exp q := by simpa only [add_comm] using Real.add_one_le_exp q
  have hp (x : I) : (1+q)^selectionRemaining active 0 x≤Real.exp (q*M) := by
    calc
      _ ≤ (Real.exp q)^selectionRemaining active 0 x := pow_le_pow_left₀ (by linarith) hbase _
      _ = Real.exp (q*(selectionRemaining active 0 x:ℝ)) := by rw [← Real.exp_nat_mul,mul_comm]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hremaining x) hq)
  calc
    _ = ∑ x,(1+q)^selectionRemaining active 0 x := by simp [selectionPotential]
    _ ≤ ∑ _x : I,Real.exp (q*M) := Finset.sum_le_sum (fun x _=>hp x)
    _ = (Fintype.card I:ℝ)*Real.exp (q*M) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le

theorem half_le_log_two : (1/2:ℝ)≤Real.log 2 := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hh
  linarith

theorem exp_half_le_two_pow (s : ℝ) (hs : 0≤s) (B : ℕ) (hB : s≤B) :
    Real.exp (s/2)≤(2:ℝ)^B := by
  have hh : s/2≤(B:ℝ)*Real.log 2 := by
    have ht := mul_le_mul_of_nonneg_left half_le_log_two (Nat.cast_nonneg B)
    linarith
  have he := Real.exp_le_exp.mpr hh
  simpa only [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)] using he

theorem bounded_degree_selection_order (p : ℝ) (hp : 0<p) :
    ∃ n₀ : ℕ,2≤n₀ ∧ ∀ n : ℕ,n₀≤n →
    ∀ (I : Type*) [Fintype I] (N : ℕ) (active : Fin N→I→Prop),
      (Fintype.card I:ℝ)≤p*(n:ℝ)^2 →
      (∀ x,(selectionRemaining active 0 x:ℝ)≤p*n) →
      selectionPotential active (Real.sqrt p/4) 0 (fun _=>0)<
        (2:ℝ)^(Nat.floor (p*Real.sqrt p*n)+1) := by
  have hsqrt : 0<Real.sqrt p := Real.sqrt_pos.2 hp
  let c := p*Real.sqrt p/4
  have hc : 0<c := by dsimp [c];positivity
  obtain ⟨n₁,hn₁⟩ := eventually_stretchedExp_le_inv_pow p 2 hc (p:=1) (by norm_num) 1
  refine ⟨max 2 n₁,le_max_left _ _,?_⟩
  intro n hn I _ N active hcount hremaining
  have hn2 : 2≤n := (le_max_left _ _).trans hn
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  let s := p*Real.sqrt p*n
  have hs : 0<s := by dsimp [s];positivity
  have htail := hn₁ n ((le_max_right _ _).trans hn)
  simp only [Real.rpow_two,Real.rpow_one,pow_one] at htail
  have hinv : 1/(n:ℝ)<1 := (div_lt_one hnR).mpr (by exact_mod_cast (show 1<n by omega))
  have ht : p*(n:ℝ)^2*Real.exp (-s/4)<1 := by
    have he : -c*(n:ℝ)= -s/4 := by dsimp [c,s];ring
    rw [he] at htail
    exact htail.trans_lt hinv
  have hsmall : p*(n:ℝ)^2*Real.exp (s/4)<Real.exp (s/2) := by
    have hh := mul_lt_mul_of_pos_right ht (Real.exp_pos (s/2))
    rw [one_mul,mul_assoc,← Real.exp_add] at hh
    have he : -s/4+s/2=s/4 := by ring
    rwa [he] at hh
  have hpot := selectionPotential_zero_bound active (Real.sqrt p/4) (p*n) (p*(n:ℝ)^2)
    (by positivity) hcount hremaining
  have he : (Real.sqrt p/4)*(p*n)=s/4 := by dsimp [s];ring
  rw [he] at hpot
  exact (hpot.trans_lt hsmall).trans_le (exp_half_le_two_pow s hs.le (Nat.floor s+1)
    (le_of_lt (by exact_mod_cast Nat.lt_floor_add_one s)))

theorem selection_candidate_scale (p n : ℝ) (hp : 0<p) (hn : 0<n) :
    let s := p*Real.sqrt p*n
    let t := Nat.ceil (4*s)
    0<t ∧ (p^2*n)≤(Real.sqrt p/4)*t ∧ ((Nat.floor s:ℕ):ℝ)≤s := by
  intro s t
  have hsqrt : 0<Real.sqrt p := Real.sqrt_pos.2 hp
  have hs : 0<s := by dsimp [s];positivity
  have ht : 4*s≤(t:ℝ) := Nat.le_ceil _
  have ht0 : 0<(t:ℝ) := (by linarith : (0:ℝ)<4*s).trans_le ht
  have hsq := Real.sq_sqrt hp.le
  have hm := mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ)≤Real.sqrt p/4)
  refine ⟨by exact_mod_cast ht0,?_,Nat.floor_le hs.le⟩
  have he : (Real.sqrt p/4)*(4*s)=p^2*n := by
    dsimp [s]
    nlinarith only [congrArg (fun z=>p*z*n) hsq]
  simpa only [he] using hm

end Oberwolfach
