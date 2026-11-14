module

public import Oberwolfach.RootedSubsets

@[expose] public section

/-! Conditional intersection tails retain the original ambient-density
normalisation. The fixed roots contribute an explicitly bounded error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fixedSubset_intersection_tail_at_size {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} [Nonempty (FixedSubset V k)] (hk : k≤Fintype.card V)
    (A : Finset V) (t : ℝ) (ht : 0≤t) :
    (FiniteLaw.uniform (FixedSubset V k)).probability
      (fun S => t≤|((A∩S.val).card:ℝ)-(A.card:ℝ)*(k:ℝ)/Fintype.card V|)≤
        2*Real.exp (-2*t^2/k) := by
  let f (S : FixedSubset V k) := ((A∩S.val).card:ℝ)
  have hm (s : ℝ) : (FiniteLaw.uniform (FixedSubset V k)).expectation
      (fun S => Real.exp (s*(f S-(FiniteLaw.uniform (FixedSubset V k)).expectation f)))≤
        Real.exp (s^2*(k:ℝ)/8) := by
    have hh := fixedSubset_mgf hk f (b:=1) (by norm_num)
      (fun S u v => by
        simpa only [f,fixedSubsetMap,← Set.ncard_coe_finset,Finset.coe_inter]
          using swap_subset_intersection_change A S.val u v) s
    simpa only [one_pow,mul_one] using hh
  have hh := finiteLaw_mgf_absolute_tail (FiniteLaw.uniform (FixedSubset V k)) f
    (show (0:ℝ)≤k by positivity) hm ht
  have he : (FiniteLaw.uniform (FixedSubset V k)).expectation f=
      (A.card:ℝ)*((k:ℝ)/Fintype.card V) := by
    convert fixedSubset_intersection_mean hk A using 1
    unfold FiniteLaw.expectation
    apply Finset.sum_congr rfl
    intro S _
    congr 1
    simp only [f,← Set.ncard_coe_finset,Finset.coe_inter]
  rw [he] at hh
  simpa only [f,mul_div_assoc] using hh

theorem rooted_subset_mean_error {n t k a q : ℝ}
    (hn : 0<n) (ht : 0≤t) (htn : t<n) (hk : 0≤k) (hkt : k≤n-t)
    (ha : 0≤a) (han : a≤n) (hq : 0≤q) (hqt : q≤t) :
    |q+(a-q)*k/(n-t)-a*(t+k)/n|≤t := by
  have hn' : 0<n-t := sub_pos.mpr htn
  have hfactor : 0≤1-k/(n-t) := by
    have hh := (div_le_one hn').mpr hkt
    linarith
  have hfactor' : 1-k/(n-t)≤1 := by linarith [div_nonneg hk hn'.le]
  have hmid : 0≤a*t/n := by positivity
  have hmid' : a*t/n≤t := by
    apply (div_le_iff₀ hn).mpr
    nlinarith
  have hb : |q-a*t/n|≤t := abs_le.mpr ⟨by linarith,by linarith⟩
  have he : q+(a-q)*k/(n-t)-a*(t+k)/n=(1-k/(n-t))*(q-a*t/n) := by
    field_simp
    ring
  rw [he,abs_mul,abs_of_nonneg hfactor]
  calc
    _ ≤ (1-k/(n-t))*t := mul_le_mul_of_nonneg_left hb hfactor
    _ ≤ t := by nlinarith

theorem rootedSubset_intersection_tail {V : Type*} [Fintype V] [DecidableEq V]
    (T A : Finset V) (k : ℕ) (hk : T.card+k≤Fintype.card V) (hkpos : 0<k)
    [Nonempty (RootedSubset V T k)] [Nonempty (FixedSubset {x : V // x∉T} k)]
    (s : ℝ) (hs : 0≤s) :
    (FiniteLaw.uniform (RootedSubset V T k)).probability
      (fun S => s+T.card≤|((A∩S.val.val).card:ℝ)-
        (A.card:ℝ)*(T.card+k:ℝ)/Fintype.card V|)≤
      2*Real.exp (-2*s^2/k) := by
  let Y := {x : V // x∉T}
  let B : Finset Y := A.subtype (fun x => x∉T)
  have hY : Fintype.card Y=Fintype.card V-T.card := by
    rw [Fintype.card_subtype_compl]
    simp
  have hky : k≤Fintype.card Y := by rw [hY];omega
  have hsum : (A∩T).card+B.card=A.card := by
    dsimp only [B]
    rw [Finset.card_subtype]
    have he : A.filter (fun x => x∉T)=A\T := by ext x;simp
    rw [he]
    exact Finset.card_inter_add_card_sdiff A T
  have hqr : ((A∩T).card:ℝ)+(B.card:ℝ)=A.card := by exact_mod_cast hsum
  have hn : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr (by omega)
  have htn : (T.card:ℝ)<Fintype.card V := by exact_mod_cast (by omega : T.card<Fintype.card V)
  have hkt : (k:ℝ)≤Fintype.card V-T.card := by
    have hh : (T.card:ℝ)+k≤Fintype.card V := by exact_mod_cast hk
    linarith
  have hnr : (Fintype.card Y:ℝ)=Fintype.card V-T.card := by
    rw [hY,Nat.cast_sub (by omega)]
  have hmean : |((A∩T).card:ℝ)+(B.card:ℝ)*k/Fintype.card Y-
      (A.card:ℝ)*(T.card+k:ℝ)/Fintype.card V|≤T.card := by
    have hh := rooted_subset_mean_error (a:=(A.card:ℝ)) (q:=((A∩T).card:ℝ)) hn
      (Nat.cast_nonneg _) htn (Nat.cast_nonneg k) hkt (Nat.cast_nonneg _)
      (by exact_mod_cast A.card_le_univ) (Nat.cast_nonneg _)
      (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁:=A) (s₂:=T)))
    rw [hnr]
    have hb : (B.card:ℝ)=(A.card:ℝ)-(A∩T).card := by linarith
    simpa only [hb] using hh
  rw [← finiteLaw_uniform_map_equiv (rootedSubsetEquiv T k).symm,finiteLaw_map_probability]
  apply le_trans (finiteLaw_probability_mono _ _ _ ?_)
    (fixedSubset_intersection_tail_at_size hky B s hs)
  intro S hS
  change s+T.card≤|((A∩(rootedSubsetUnion T S).val.val).card:ℝ)-
    (A.card:ℝ)*(T.card+k:ℝ)/Fintype.card V| at hS
  rw [rootedSubset_intersection_count T A S,Nat.cast_add] at hS
  have hb := abs_sub_le (((A∩T).card:ℝ)+((B∩S.val).card:ℝ))
    (((A∩T).card:ℝ)+(B.card:ℝ)*k/Fintype.card Y)
    ((A.card:ℝ)*(T.card+k:ℝ)/Fintype.card V)
  have he : ((A∩T).card:ℝ)+((B∩S.val).card:ℝ)-
      (((A∩T).card:ℝ)+(B.card:ℝ)*k/Fintype.card Y)=
      ((B∩S.val).card:ℝ)-(B.card:ℝ)*k/Fintype.card Y := by ring
  rw [he] at hb
  change s≤|((B∩S.val).card:ℝ)-(B.card:ℝ)*k/Fintype.card Y|
  change s+T.card≤|((A∩T).card:ℝ)+((B∩S.val).card:ℝ)-
    (A.card:ℝ)*(T.card+k:ℝ)/Fintype.card V| at hS
  linarith

end Oberwolfach
