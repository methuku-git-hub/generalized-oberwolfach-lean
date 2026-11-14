module

public import Oberwolfach.MarkedWheels
public import Oberwolfach.OrdinaryCycleRootCounts

@[expose] public section

/-! Counts of canonical marked wheels containing specified auxiliary
vertices and with their hub in a fixed set. Coefficients are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_cycle_root_count {V E K : Type*} [Fintype V] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (S : Finset V) :
    (∑ C : MarkedCycleTuple tail head ktail khead m π b,
      if (∀ v∈S,v∈Set.range C.val) then (1:ℝ) else 0)≤
      ((m:ℝ)+1)^S.card*(Fintype.card V:ℝ)^(m+1-S.card) := by
  apply (finite_subtype_sum_le (IsMarkedCycleTuple tail head ktail khead m π b)
    (fun C=>if (∀ v∈S,v∈Set.range C) then (1:ℝ) else 0)
    (by intro C;split_ifs <;> norm_num)).trans
  simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
    functions_cover_roots_count (0 : Fin (m+1)) S

theorem marked_wheel_event_weight_bound {V U E K : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (H₀ Hₖ : V → U → Prop)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (M : ℝ) (hM : 0≤M) (hw : ∀ W,w W≤M) (S : Finset V) (T : Finset U)
    (P : MarkedWheel tail head ktail khead m π b H₀ Hₖ → Prop)
    (hP : ∀ W,P W → (∀ v∈S,v∈Set.range W.1.val) ∧ W.2.val∈T) :
    (∑ W,if P W then w W else 0)≤
      (T.card:ℝ)*((m:ℝ)+1)^S.card*(Fintype.card V:ℝ)^(m+1-S.card)*M := by
  let A := MarkedCycleTuple tail head ktail khead m π b
  let g (C : A) (u : U) : ℝ := if (∀ v∈S,v∈Set.range C.val) ∧ u∈T then M else 0
  have hg (C : A) (u : U) : 0≤g C u := by dsimp [g];split_ifs <;> positivity
  have hfirst : (∑ W,if P W then w W else 0)≤
      ∑ C : A,∑ u : {u // MarkedHubCompatible H₀ Hₖ C.val u},g C u.val := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro C _
    apply Finset.sum_le_sum
    intro u _
    by_cases hp : P ⟨C,u⟩
    · rw [if_pos hp]
      dsimp only [g]
      rw [if_pos (hP ⟨C,u⟩ hp)]
      exact hw ⟨C,u⟩
    · rw [if_neg hp];exact hg C u.val
  have hsecond : (∑ C : A,∑ u : {u // MarkedHubCompatible H₀ Hₖ C.val u},g C u.val)≤
      ∑ C : A,∑ u : U,g C u := by
    apply Finset.sum_le_sum
    intro C _
    exact finite_subtype_sum_le (MarkedHubCompatible H₀ Hₖ C.val) (g C) (hg C)
  have heq (C : A) : (∑ u : U,g C u)=
      (T.card:ℝ)*M*(if (∀ v∈S,v∈Set.range C.val) then (1:ℝ) else 0) := by
    by_cases hs : ∀ v∈S,v∈Set.range C.val
    · rw [if_pos hs,mul_one]
      have hg' (u : U) : g C u=(if u∈T then M else 0) := by
        dsimp only [g]
        by_cases hu : u∈T
        · rw [if_pos ⟨hs,hu⟩,if_pos hu]
        · rw [if_neg (fun h=>hu h.2),if_neg hu]
      simp_rw [hg']
      rw [← Finset.sum_filter]
      have ht : Finset.univ.filter (fun u=>u∈T)=T := by ext;simp
      rw [ht,Finset.sum_const,nsmul_eq_mul]
    · simp only [g,hs,false_and,ite_false,Finset.sum_const_zero,mul_zero]
  have hcount := marked_cycle_root_count tail head ktail khead m π b S
  calc
    _ ≤ ∑ C : A,∑ u : U,g C u := hfirst.trans hsecond
    _ = (T.card:ℝ)*M*(∑ C : A,if (∀ v∈S,v∈Set.range C.val) then (1:ℝ) else 0) := by
      simp_rw [heq]
      rw [Finset.mul_sum]
    _ ≤ (T.card:ℝ)*M*(((m:ℝ)+1)^S.card*(Fintype.card V:ℝ)^(m+1-S.card)) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by ring

end Oberwolfach
