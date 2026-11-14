module

public import Oberwolfach.BipartiteIntersectionEstimates

@[expose] public section

/-! Errors from pair and triple intersections, with repeated indices
kept separate from the hypotheses on distinct indices. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

theorem bipPairIntersection_absolute_error (H : A → B → Prop) (p : B → ℝ)
    (hp : ∀ u,0≤p u ∧ p u≤1) (u v : B) :
    |bipPairIntersection H v u-(Fintype.card A:ℝ)*p v*p u|≤2*Fintype.card A := by
  have hpu := (hp u).1
  have hpv := (hp v).1
  have hb := bipPairIntersection_bounds H v u
  have hc : 0≤(Fintype.card A:ℝ)*p v*p u := by positivity
  have hu : (Fintype.card A:ℝ)*p v*p u≤Fintype.card A := by
    calc
      _ ≤ (Fintype.card A:ℝ)*1*1 := by gcongr <;> exact (hp _).2
      _ = _ := by ring
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card A)]

theorem bipPairIntersection_error_sum (H : A → B → Prop) (p : B → ℝ)
    (hp : ∀ u,0≤p u ∧ p u≤1) (δ : ℝ) (hδ : 0≤δ)
    (herr : ∀ u v,u≠v → |bipPairIntersection H v u-(Fintype.card A:ℝ)*p v*p u|≤δ*Fintype.card A)
    (u : B) :
    (∑ v,|bipPairIntersection H v u-(Fintype.card A:ℝ)*p v*p u|)≤
      (Fintype.card B:ℝ)*δ*Fintype.card A+2*Fintype.card A := by
  have hh := exceptional_sum_abs_le
    (fun v=>bipPairIntersection H v u-(Fintype.card A:ℝ)*p v*p u) {u}
    (δ*Fintype.card A) (2*Fintype.card A) (by positivity) (by positivity)
    (fun v hv=>herr u v (Ne.symm (by simpa using hv)))
    (bipPairIntersection_absolute_error H p hp u)
  simpa only [Finset.card_singleton,Nat.cast_one,one_mul,mul_assoc] using hh

theorem bipTripleIntersection_absolute_error (H : A → B → Prop) (p : B → ℝ)
    (hp : ∀ u,0≤p u ∧ p u≤1) (u v t : B) :
    |bipTripleIntersection H u v t-(Fintype.card A:ℝ)*p u*p v*p t|≤2*Fintype.card A := by
  have hpu := (hp u).1
  have hpv := (hp v).1
  have hpt := (hp t).1
  have hb := bipTripleIntersection_bounds H u v t
  have hc : 0≤(Fintype.card A:ℝ)*p u*p v*p t := by positivity
  have hu : (Fintype.card A:ℝ)*p u*p v*p t≤Fintype.card A := by
    calc
      _ ≤ (Fintype.card A:ℝ)*1*1*1 := by gcongr <;> exact (hp _).2
      _ = _ := by ring
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card A)]

theorem bipTripleIntersection_error_sum (H : A → B → Prop) (p : B → ℝ)
    (hp : ∀ u,0≤p u ∧ p u≤1) (δ : ℝ) (hδ : 0≤δ)
    (herr : ∀ u v t,u≠v → u≠t → v≠t →
      |bipTripleIntersection H u v t-(Fintype.card A:ℝ)*p u*p v*p t|≤δ*Fintype.card A)
    (u t : B) (hut : u≠t) :
    (∑ v,|bipTripleIntersection H u v t-(Fintype.card A:ℝ)*p u*p v*p t|)≤
      (Fintype.card B:ℝ)*δ*Fintype.card A+4*Fintype.card A := by
  have hh := exceptional_sum_abs_le
    (fun v=>bipTripleIntersection H u v t-(Fintype.card A:ℝ)*p u*p v*p t) {u,t}
    (δ*Fintype.card A) (2*Fintype.card A) (by positivity) (by positivity)
    (by intro v hv;simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hv
        exact herr u v t (Ne.symm hv.1) hut hv.2)
    (fun v=>bipTripleIntersection_absolute_error H p hp u v t)
  have hc : ({u,t}:Finset B).card≤2 := by simp [hut]
  have hc' : (({u,t}:Finset B).card:ℝ)≤2 := by exact_mod_cast hc
  nlinarith [mul_le_mul_of_nonneg_right hc' (show (0:ℝ)≤2*Fintype.card A by positivity)]

end Oberwolfach
