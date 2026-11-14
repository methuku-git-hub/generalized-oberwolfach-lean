module

public import Oberwolfach.PermutationEmbeddingWindows

@[expose] public section

/-! Restricting a permutation to a genuinely invariant vertex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

variable {V : Type}

def invariantSetPermutation (π : Equiv.Perm V) (A : Set V)
    (hA : ∀ v,π v∈A ↔ v∈A) : Equiv.Perm A where
  toFun x := ⟨π x,(hA x).mpr x.property⟩
  invFun x := ⟨π.symm x,(hA (π.symm x)).mp (by simpa using x.property)⟩
  left_inv x := by apply Subtype.ext;exact π.symm_apply_apply x
  right_inv x := by apply Subtype.ext;exact π.apply_symm_apply x

theorem invariantSetPermutation_apply (π : Equiv.Perm V) (A : Set V)
    (hA : ∀ v,π v∈A ↔ v∈A) (x : A) :
    ((invariantSetPermutation π A hA) x : V)=π x := rfl

theorem invariantSetPermutation_noshort [Fintype V] [DecidableEq V]
    (π : Equiv.Perm V) (A : Set V) [Fintype A] [DecidableEq A]
    (hA : ∀ v,π v∈A ↔ v∈A) (L : ℕ)
    (h : ∀ x l,0<l → l<L → (π^l) x≠x) :
    ∀ x : A,∀ l,0<l → l<L → ((invariantSetPermutation π A hA)^l) x≠x := by
  intro x l hl hL he
  have hh := congrArg (fun x : A=>(x:V)) he
  rw [permutation_embedding_power Subtype.val π (invariantSetPermutation π A hA)
    (fun _=>rfl) l] at hh
  exact h x l hl hL hh

end Oberwolfach
