module

public import Oberwolfach.TripleKernelBounds

@[expose] public section

/-! Summing the two exceptional sets in the opposite-operator square. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem bipTripleKernel_error_sum (H : A → B → Prop) (p q : B → ℝ)
    (L δ D : ℝ) (hL : 0≤L) (hδ : 0≤δ) (hD : 0≤D)
    (hp : ∀ u,0≤p u ∧ p u≤1) (hq : ∀ u,0≤q u ∧ q u≤L) (hpq : ∀ u,q u*p u=1)
    (herr : ∀ u v t,u≠v → u≠t → v≠t →
      |bipTripleIntersection H u v t-(Fintype.card A:ℝ)*p u*p v*p t|≤δ*Fintype.card A)
    (E : A → Finset A) (hE : ∀ x,(E x).card≤D)
    (hcodeg : ∀ x s,s∉E x → |bipWeightedCodegree H q x s-(Fintype.card B:ℝ)|≤δ*Fintype.card B)
    (x : A) (u : B) :
    (∑ s,∑ t,|bipTripleKernel H q x u s t-(Fintype.card A:ℝ)*(Fintype.card B:ℝ)*p u*p t|)≤
      (Fintype.card B:ℝ)*((Fintype.card A:ℝ)*
        (L^3*((Fintype.card B:ℝ)*δ*Fintype.card A+4*Fintype.card A)+
          (Fintype.card A:ℝ)*δ*Fintype.card B)+
        D*((L^3+1)*(Fintype.card A:ℝ)*Fintype.card B))+
      (Fintype.card A:ℝ)*((L^3+1)*(Fintype.card A:ℝ)*Fintype.card B) := by
  let a : ℝ := Fintype.card A
  let b : ℝ := Fintype.card B
  let e := L^3*(b*δ*a+4*a)+a*δ*b
  let M := (L^3+1)*a*b
  let f (t : B) := ∑ s,|bipTripleKernel H q x u s t-a*b*p u*p t|
  have he : 0≤e := by dsimp [e,a,b];positivity
  have hM : 0≤M := by dsimp [M,a,b];positivity
  have hf0 (t : B) : 0≤f t := Finset.sum_nonneg (fun _ _=>abs_nonneg _)
  have hall (t : B) : |f t|≤a*M := by
    rw [abs_of_nonneg (hf0 t)]
    calc
      _ ≤ ∑ _s : A,M := Finset.sum_le_sum (fun s _=>bipTripleKernel_absolute_error H p q L hL hp hq x s u t)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];rfl
  have hgood (t : B) (ht : t∉({u}:Finset B)) : |f t|≤a*e+D*M := by
    have hut : u≠t := Ne.symm (by simpa only [Finset.mem_singleton] using ht)
    rw [abs_of_nonneg (hf0 t)]
    have hh := exceptional_sum_abs_le
      (fun s=>bipTripleKernel H q x u s t-a*b*p u*p t) (E x) e M he hM
      (fun s hs=>bipTripleKernel_regular_error H p q L δ hL hδ hp hq hpq herr x s u t hut (hcodeg x s hs))
      (fun s=>bipTripleKernel_absolute_error H p q L hL hp hq x s u t)
    exact hh.trans (by dsimp only [a];gcongr;exact hE x)
  have hh := exceptional_sum_abs_le f {u} (a*e+D*M) (a*M)
    (by positivity) (by positivity) hgood hall
  simp only [Finset.card_singleton,Nat.cast_one,one_mul] at hh
  simp only [abs_of_nonneg (hf0 _)] at hh
  rw [Finset.sum_comm]
  exact hh

end Oberwolfach
