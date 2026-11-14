module

public import Oberwolfach.RootFirstCommonPaths

@[expose] public section

/-! An injective map commuting with the two permutations preserves the
exact separation predicate and both orders of marked cycle tuples. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
variable {W V E K I:Type*}

theorem permutation_embedding_pow (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (n:ℕ) (x:W):f ((ρ^n) x)=(π^n) (f x):=by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [pow_succ',pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,h,ih]

theorem permutationClose_embedding_iff (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (b:ℕ) (x y:W):
    PermutationClose π b (f x) (f y)↔PermutationClose ρ b x y:=by
  simp only [PermutationClose,←permutation_embedding_pow f ρ π h,f.injective.eq_iff]

theorem permutationSeparated_embedding_iff (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (b:ℕ) (z:I→W):
    PermutationSeparated π b (f∘z)↔PermutationSeparated ρ b z:=by
  simp only [PermutationSeparated,Function.comp_apply,permutationClose_embedding_iff f ρ π h]

theorem markedCycle_embedding_iff (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (tail head:E→W) (ktail khead:K→W)
    (m b:ℕ) (z:Fin (m+1)→W):
    IsMarkedCycleTuple (f∘tail) (f∘head) (f∘ktail) (f∘khead) m π b (f∘z)↔
      IsMarkedCycleTuple tail head ktail khead m ρ b z:=by
  simp only [IsMarkedCycleTuple,permutationSeparated_embedding_iff f ρ π h,
    Function.comp_apply,f.injective.eq_iff]

theorem rootFirstMarkedCycle_embedding_iff (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (tail head:E→W) (ktail khead:K→W)
    (m b:ℕ) (s:Fin (m+1)) (z:Fin (m+1)→W):
    IsRootFirstMarkedCycle (f∘tail) (f∘head) (f∘ktail) (f∘khead) m π b s (f∘z)↔
      IsRootFirstMarkedCycle tail head ktail khead m ρ b s z:=by
  simp only [IsRootFirstMarkedCycle,permutationSeparated_embedding_iff f ρ π h,
    Function.comp_apply,f.injective.eq_iff]

end Oberwolfach
