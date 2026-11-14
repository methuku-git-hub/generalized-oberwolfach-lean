module

public import Mathlib.Tactic

@[expose] public section

/-! Exact degree identities after four typed matrix deletions. Natural
subtraction is converted only after proving the pointwise subgraph bound. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def TypedMatrixBalanced {V U : Type*} [Fintype V] [Fintype U]
    (q : ℕ) (R₀ Rₖ : V → V → ℕ) (H₀ Hₖ : V → U → ℕ) : Prop :=
  (∀ v,(∑ x,R₀ v x)+(∑ x,Rₖ v x)=(∑ u,H₀ v u)+(∑ u,Hₖ v u)) ∧
  (∀ v,(∑ x,R₀ x v)+(∑ x,Rₖ x v)=(∑ u,H₀ v u)+(∑ u,Hₖ v u)) ∧
  (∀ v,(∑ x,Rₖ x v)=(∑ u,Hₖ v u)) ∧
  (∀ u,(∑ v,H₀ v u)=q*(∑ v,Hₖ v u))

theorem int_sum_tsub {I : Type*} [Fintype I] (f g : I → ℕ)
    (h : ∀ i,g i≤f i) :
    (∑ i,((f i-g i : ℕ):ℤ))=(∑ i,(f i : ℤ))-(∑ i,(g i : ℤ)) := by
  simp only [Int.ofNat_sub (h _),Finset.sum_sub_distrib]

theorem typed_matrix_imbalance_totals {V U : Type*} [Fintype V] [Fintype U]
    (R₀ Rₖ : V → V → ℕ) (H₀ Hₖ : V → U → ℕ) :
    (∑ v,((∑ x,(R₀ v x : ℤ))+(∑ x,(Rₖ v x : ℤ))-
      (∑ u,(H₀ v u : ℤ))-(∑ u,(Hₖ v u : ℤ))))=
    (∑ v,((∑ x,(R₀ x v : ℤ))+(∑ x,(Rₖ x v : ℤ))-
      (∑ u,(H₀ v u : ℤ))-(∑ u,(Hₖ v u : ℤ)))) := by
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f:=fun v x=>(R₀ v x : ℤ)),
    Finset.sum_comm (f:=fun v x=>(Rₖ v x : ℤ))]

theorem typed_matrix_remainder_balanced {V U : Type*} [Fintype V] [Fintype U]
    (q : ℕ) (R₀ Rₖ J₀ Jₖ : V → V → ℕ) (H₀ Hₖ L₀ Lₖ : V → U → ℕ)
    (hJ0 : ∀ x y,J₀ x y≤R₀ x y) (hJK : ∀ x y,Jₖ x y≤Rₖ x y)
    (hL0 : ∀ v u,L₀ v u≤H₀ v u) (hLK : ∀ v u,Lₖ v u≤Hₖ v u)
    (hp : ∀ v,(∑ x,(J₀ v x : ℤ))+(∑ x,(Jₖ v x : ℤ))-
      (∑ u,(L₀ v u : ℤ))-(∑ u,(Lₖ v u : ℤ))=
      (∑ x,(R₀ v x : ℤ))+(∑ x,(Rₖ v x : ℤ))-
      (∑ u,(H₀ v u : ℤ))-(∑ u,(Hₖ v u : ℤ)))
    (hm : ∀ v,(∑ x,(J₀ x v : ℤ))+(∑ x,(Jₖ x v : ℤ))-
      (∑ u,(L₀ v u : ℤ))-(∑ u,(Lₖ v u : ℤ))=
      (∑ x,(R₀ x v : ℤ))+(∑ x,(Rₖ x v : ℤ))-
      (∑ u,(H₀ v u : ℤ))-(∑ u,(Hₖ v u : ℤ)))
    (hk : ∀ v,(∑ x,(Jₖ x v : ℤ))-(∑ u,(Lₖ v u : ℤ))=
      (∑ x,(Rₖ x v : ℤ))-(∑ u,(Hₖ v u : ℤ)))
    (hw : ∀ u,(∑ v,(L₀ v u : ℤ))-(q:ℤ)*(∑ v,(Lₖ v u : ℤ))=
      (∑ v,(H₀ v u : ℤ))-(q:ℤ)*(∑ v,(Hₖ v u : ℤ))) :
    TypedMatrixBalanced q (fun x y=>R₀ x y-J₀ x y) (fun x y=>Rₖ x y-Jₖ x y)
      (fun v u=>H₀ v u-L₀ v u) (fun v u=>Hₖ v u-Lₖ v u) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro v
    have hh : (∑ x,((R₀ v x-J₀ v x : ℕ):ℤ))+(∑ x,((Rₖ v x-Jₖ v x : ℕ):ℤ))=
        (∑ u,((H₀ v u-L₀ v u : ℕ):ℤ))+(∑ u,((Hₖ v u-Lₖ v u : ℕ):ℤ)) := by
      rw [int_sum_tsub _ _ (hJ0 v),int_sum_tsub _ _ (hJK v),
        int_sum_tsub _ _ (hL0 v),int_sum_tsub _ _ (hLK v)]
      linarith only [hp v]
    exact_mod_cast hh
  · intro v
    have hh : (∑ x,((R₀ x v-J₀ x v : ℕ):ℤ))+(∑ x,((Rₖ x v-Jₖ x v : ℕ):ℤ))=
        (∑ u,((H₀ v u-L₀ v u : ℕ):ℤ))+(∑ u,((Hₖ v u-Lₖ v u : ℕ):ℤ)) := by
      rw [int_sum_tsub _ _ (fun x=>hJ0 x v),int_sum_tsub _ _ (fun x=>hJK x v),
        int_sum_tsub _ _ (hL0 v),int_sum_tsub _ _ (hLK v)]
      linarith only [hm v]
    exact_mod_cast hh
  · intro v
    have hh : (∑ x,((Rₖ x v-Jₖ x v : ℕ):ℤ))=(∑ u,((Hₖ v u-Lₖ v u : ℕ):ℤ)) := by
      rw [int_sum_tsub _ _ (fun x=>hJK x v),int_sum_tsub _ _ (hLK v)]
      linarith only [hk v]
    exact_mod_cast hh
  · intro u
    have hh : (∑ v,((H₀ v u-L₀ v u : ℕ):ℤ))=(q:ℤ)*(∑ v,((Hₖ v u-Lₖ v u : ℕ):ℤ)) := by
      rw [int_sum_tsub _ _ (fun v=>hL0 v u),int_sum_tsub _ _ (fun v=>hLK v u)]
      nlinarith only [hw u]
    exact_mod_cast hh

end Oberwolfach
