module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Counting finite sequences by actual extension counts. The predicates may
include injectivity, forbidden pairs, and required graph edges. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sequential_choices_count {V : Type*} [Fintype V]
    (Good : ∀ n : ℕ,(Fin n → V) → Prop) (K : ℕ) (a : ℝ) (ha : 0≤a)
    (hzero : ∀ f : Fin 0 → V,Good 0 f)
    (hstep : ∀ n<K,∀ f : Fin n → V,Good n f →
      a≤(Fintype.card {v : V // Good (n+1) (Fin.snoc f v)}:ℝ)) :
    a^K≤(Fintype.card {f : Fin K → V // Good K f}:ℝ) := by
  have hind : ∀ n≤K,a^n≤(Fintype.card {f : Fin n → V // Good n f}:ℝ) := by
    intro n
    induction n with
    | zero=>
      intro _
      simp only [pow_zero]
      have hnon : Nonempty {f : Fin 0 → V // Good 0 f} := ⟨⟨Fin.elim0,hzero _⟩⟩
      exact_mod_cast (Fintype.card_pos_iff.mpr hnon : 0<Fintype.card {f : Fin 0 → V // Good 0 f})
    | succ n ih=>
      intro hn
      let B := {f : Fin n → V // Good n f}
      let C (f : B) := {v : V // Good (n+1) (Fin.snoc f.val v)}
      let next : (Σ f : B,C f) → {g : Fin (n+1) → V // Good (n+1) g} :=
        fun z=>⟨Fin.snoc z.1.val z.2.val,z.2.property⟩
      have hinj : Function.Injective next := by
        intro x y he
        have hh := congrArg Subtype.val he
        have hf : x.1=y.1 := by
          apply Subtype.ext
          funext i
          have hi := congrFun hh i.castSucc
          simpa only [next,Fin.snoc_castSucc] using hi
        have hv : x.2.val=y.2.val := by
          have hi := congrFun hh (Fin.last n)
          simpa only [next,Fin.snoc_last] using hi
        cases x with
        | mk f v=>
          cases y with
          | mk g w=>
            dsimp only at hf
            subst g
            exact congrArg (Sigma.mk f) (Subtype.ext hv)
      have hc : (Fintype.card (Σ f : B,C f):ℝ)≤
          Fintype.card {g : Fin (n+1) → V // Good (n+1) g} := by
        exact_mod_cast Fintype.card_le_of_injective next hinj
      have hs : (Fintype.card B:ℝ)*a≤Fintype.card (Σ f : B,C f) := by
        rw [Fintype.card_sigma,Nat.cast_sum]
        calc
          _ = ∑ _f : B,a := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
          _ ≤ _ := Finset.sum_le_sum (fun f _=>hstep n (by omega) f.val f.property)
      calc
        a^(n+1)=a^n*a := pow_succ _ _
        _ ≤ (Fintype.card B:ℝ)*a := mul_le_mul_of_nonneg_right (ih (by omega)) ha
        _ ≤ _ := hs.trans hc
  exact hind K le_rfl

end Oberwolfach
