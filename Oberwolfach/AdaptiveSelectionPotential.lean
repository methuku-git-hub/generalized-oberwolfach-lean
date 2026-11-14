module

public import Mathlib.Tactic

@[expose] public section

/-! A deterministic potential for sequential choices. The set of tests
and the steps that can affect each test are fixed in advance; candidates
at a step may depend on every preceding choice. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I A : Type*} [Fintype I] [Fintype A] {N : ℕ}

def selectionRemaining (active : Fin N→I→Prop) (k : ℕ) (x : I) : ℕ :=
  (Finset.univ.filter (fun i : Fin N=>k ≤ i.val ∧ active i x)).card

def selectionPotential (active : Fin N→I→Prop) (q : ℝ) (k : ℕ) (Z : I→ℕ) : ℝ :=
  ∑ x,(2:ℝ)^(Z x)*(1+q)^selectionRemaining active k x

theorem selectionRemaining_step (active : Fin N→I→Prop) (i : Fin N) (x : I) :
    selectionRemaining active i.val x=
      selectionRemaining active (i.val+1) x+(if active i x then 1 else 0) := by
  let S := Finset.univ.filter (fun j : Fin N=>i.val+1≤j.val ∧ active j x)
  have hi : i∉S := by simp [S]
  by_cases ha : active i x
  · have he : Finset.univ.filter (fun j : Fin N=>i.val≤j.val ∧ active j x)=insert i S := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,S]
      constructor
      · rintro ⟨hj,hja⟩
        by_cases hji : j=i
        · exact Or.inl hji
        · right
          have hne : j.val≠i.val := fun hh=>hji (Fin.ext hh)
          exact ⟨by omega,hja⟩
      · rintro (rfl|⟨hj,hja⟩)
        · exact ⟨le_rfl,ha⟩
        · exact ⟨by omega,hja⟩
    simp only [selectionRemaining,he,Finset.card_insert_of_notMem hi,if_pos ha]
    rfl
  · have he : Finset.univ.filter (fun j : Fin N=>i.val≤j.val ∧ active j x)=S := by
      ext j
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨hj,hja⟩
        have hne : j.val≠i.val := by intro he;exact ha (Fin.ext he ▸ hja)
        exact ⟨by omega,hja⟩
      · rintro ⟨hj,hja⟩;exact ⟨by omega,hja⟩
    simp only [selectionRemaining,he,if_neg ha,Nat.add_zero]
    rfl

theorem sum_two_pow_increment (z : ℕ) (hit : A→Prop) :
    (∑ a,(2:ℝ)^(z+(if hit a then 1 else 0)))=
      (2:ℝ)^z*((Fintype.card A:ℝ)+(Finset.univ.filter hit).card) := by
  have hp (a : A) : (2:ℝ)^(z+(if hit a then 1 else 0))=
      (2:ℝ)^z*(1+(if hit a then 1 else 0)) := by
    by_cases h : hit a <;> simp [h,pow_succ] <;> ring
  simp_rw [hp]
  rw [← Finset.mul_sum,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  rw [Finset.sum_boole]

theorem selectionPotential_step_average (active : Fin N→I→Prop) (i : Fin N)
    (q : ℝ) (hq : 0≤q) (Z : I→ℕ) (hit : A→I→Prop)
    (hinactive : ∀ x,¬active i x → ∀ a,¬hit a x)
    (hcount : ∀ x,((Finset.univ.filter (fun a=>hit a x)).card:ℝ)≤q*Fintype.card A) :
    (∑ a,selectionPotential active q (i.val+1) (fun x=>Z x+(if hit a x then 1 else 0)))≤
      (Fintype.card A:ℝ)*selectionPotential active q i.val Z := by
  unfold selectionPotential
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  rw [← Finset.sum_mul,sum_two_pow_increment]
  rw [selectionRemaining_step]
  by_cases ha : active i x
  · rw [if_pos ha,pow_succ]
    have hh := mul_le_mul_of_nonneg_left (add_le_add_left (hcount x) (Fintype.card A))
      (by positivity : (0:ℝ)≤2^(Z x)*(1+q)^selectionRemaining active (i.val+1) x)
    nlinarith only [hh]
  · simp only [if_neg ha,Nat.add_zero]
    have he : Finset.univ.filter (fun a=>hit a x)=∅ := by
      ext a
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
      exact hinactive x ha a
    rw [he,Finset.card_empty,Nat.cast_zero,add_zero]
    ring_nf
    exact le_rfl

theorem selectionPotential_step_choice [Nonempty A]
    (active : Fin N→I→Prop) (i : Fin N) (q : ℝ) (hq : 0≤q) (Z : I→ℕ)
    (hit : A→I→Prop) (hinactive : ∀ x,¬active i x → ∀ a,¬hit a x)
    (hcount : ∀ x,((Finset.univ.filter (fun a=>hit a x)).card:ℝ)≤q*Fintype.card A) :
    ∃ a,selectionPotential active q (i.val+1) (fun x=>Z x+(if hit a x then 1 else 0))≤
      selectionPotential active q i.val Z := by
  have hh := selectionPotential_step_average active i q hq Z hit hinactive hcount
  by_contra hn
  push_neg at hn
  have hstrict := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun a _=>hn a)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hstrict
  linarith

theorem selectionPotential_counter_le (active : Fin N→I→Prop) (q : ℝ) (hq : 0≤q)
    (k : ℕ) (Z : I→ℕ) (x : I) : (2:ℝ)^(Z x)≤selectionPotential active q k Z := by
  have hp : (1:ℝ)≤(1+q)^selectionRemaining active k x := one_le_pow₀ (by linarith)
  calc
    _ ≤ (2:ℝ)^(Z x)*(1+q)^selectionRemaining active k x := by nlinarith only [hp,pow_pos (by norm_num : (0:ℝ)<2) (Z x)]
    _ ≤ _ := Finset.single_le_sum
      (fun y _=>mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) (Z y))
        (pow_nonneg (by linarith : (0:ℝ)≤1+q) _)) (Finset.mem_univ x)

theorem selectionPotential_counter_lt (active : Fin N→I→Prop) (q : ℝ) (hq : 0≤q)
    (k B : ℕ) (Z : I→ℕ) (h : selectionPotential active q k Z<(2:ℝ)^B) :
    ∀ x,Z x<B := by
  intro x
  by_contra hn
  have hb : B≤Z x := by omega
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hb
  exact (not_lt_of_ge (hp.trans (selectionPotential_counter_le active q hq k Z x))) h

end Oberwolfach
