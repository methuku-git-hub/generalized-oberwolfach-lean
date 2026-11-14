module

public import Oberwolfach.MarkedNeighbourhoodSpokeChanges

@[expose] public section

/-! Exact substitutions of finite typed tuples into the common index
estimate. The supplied marginal functions are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color I : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [Fintype I] [LinearOrder V] [DecidableEq U]

theorem marked_index_tuple_estimate
    (π : Equiv.Perm V) (d h : ℕ) (B : Finset U)
    (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color) (err : ℝ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hindices : MarkedIndicesWithSpokes π d h B q s g j err σ H)
    (w : Bool→ℝ) (hq : ∀ u∈B,q u g=w true) (hs : ∀ u∈B,s u j=w false)
    (x : I→V) (t : I→Bool) (hx : Function.Injective x) (hsize : Fintype.card I≤h)
    (hsep : ∀ i k,i≠k → ¬PermutationClose π (3*d) (x i) (x k)) :
    |((B.filter (fun u=>∀ i,H (t i) (x i) u)).card:ℝ)-
      (∏ i,w (t i))*B.card|<err := by
  let f : I→Bool×V := fun i=>(t i,x i)
  have hf : Function.Injective f := by
    intro i k he; exact hx (congrArg Prod.snd he)
  let J := Finset.univ.image f
  have hJ : J.card≤h := (Finset.card_image_le).trans (by simpa using hsize)
  have hse : ∀ a∈J,∀ b∈J,a≠b → ¬PermutationClose π (3*d) a.2 b.2 := by
    intro a ha b hb hne
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hb
    exact hsep i k (fun he=>hne (congrArg f he))
  have he := hindices J hJ hse
  have hcount : markedIndexCountWithSpokes H B J=
      ((B.filter (fun u=>∀ i,H (t i) (x i) u)).card:ℝ) := by
    simp only [markedIndexCountWithSpokes,J,Finset.forall_mem_image,Finset.mem_univ,
      forall_const,f,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have htarget : (∑ u∈B,∏ a∈J,if a.1 then q u g else s u j)=(∏ i,w (t i))*B.card := by
    calc
      _ = ∑ _u∈B,∏ i,w (t i) := by
        apply Finset.sum_congr rfl
        intro u hu
        dsimp only [J]
        rw [Finset.prod_image hf.injOn]
        apply Finset.prod_congr rfl
        intro i hi
        dsimp only [f]
        by_cases ht : t i=true
        · simp [ht,hq u hu]
        · have ht' : t i=false := Bool.eq_false_iff.mpr ht
          simp [ht',hs u hu]
      _ = _ := by simp [mul_comm]
  rwa [hcount,htarget] at he

end Oberwolfach
