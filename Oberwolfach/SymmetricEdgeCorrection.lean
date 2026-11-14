module

public import Oberwolfach.WheelLoadCombinations
public import Mathlib.Combinatorics.SimpleGraph.Operations

@[expose] public section

/-! An undirected edge occurs twice in the ordered endpoint sum, hence the
factor one half. This identity retains that multiplicity explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem symmetric_edge_isolator_sum {V : Type*} [Fintype V] [DecidableEq V]
    (z : V → V → ℝ) (hz : ∀ x y,z x y=z y x) (hdiag : ∀ x,z x x=0)
    (a b : V) :
    (1/2:ℝ)*(∑ p : V×V,z p.1 p.2*(if (SimpleGraph.edge p.1 p.2).Adj a b then 1 else 0))=z a b := by
  by_cases hab : a=b
  · subst b
    simp [hdiag]
  · have hterm (x y : V) :
        (if (SimpleGraph.edge x y).Adj a b then (1:ℝ) else 0)=
          (if a=x ∧ b=y then 1 else 0)+(if a=y ∧ b=x then 1 else 0) := by
      simp only [SimpleGraph.edge_adj]
      split_ifs <;> simp_all
    simp only [Fintype.sum_prod_type,hterm,mul_add,Finset.sum_add_distrib]
    have hfirst : (∑ x,∑ y,z x y*(if a=x ∧ b=y then (1:ℝ) else 0))=z a b := by
      simp [ite_and,eq_comm]
    have hsecond : (∑ x,∑ y,z x y*(if a=y ∧ b=x then (1:ℝ) else 0))=z b a := by
      simp [ite_and,eq_comm]
    rw [hfirst,hsecond,← hz a b]
    ring

theorem ordinaryRimLoad_symm {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ : OrdinaryWheel Q F H r → ℝ) (x y : V) :
    ordinaryRimLoad ψ x y=ordinaryRimLoad ψ y x := by
  unfold ordinaryRimLoad
  apply Finset.sum_congr rfl
  intro W _
  rw [(ordinaryWheelRim W).adj_comm]

def ordinaryRimResidual {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ : OrdinaryWheel Q F H r → ℝ) (x y : V) : ℝ :=
  (if Q.Adj x y then 1 else 0)-ordinaryRimLoad ψ x y

theorem ordinaryRimResidual_outside {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ : OrdinaryWheel Q F H r → ℝ) (x y : V) (hxy : ¬Q.Adj x y) :
    ordinaryRimResidual ψ x y=0 := by
  rw [ordinaryRimResidual,if_neg hxy,ordinaryRimLoad_eq_zero ψ x y hxy,sub_self]

theorem ordinaryRimResidual_symm {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ : OrdinaryWheel Q F H r → ℝ) (x y : V) :
    ordinaryRimResidual ψ x y=ordinaryRimResidual ψ y x := by
  unfold ordinaryRimResidual
  rw [Q.adj_comm,ordinaryRimLoad_symm]

theorem ordinary_rim_correction_loads {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ : OrdinaryWheel Q F H r → ℝ)
    (I : V → V → OrdinaryWheel Q F H r → ℝ)
    (hI : ∀ x y,Q.Adj x y → ∀ a b,ordinaryRimLoad (I x y) a b=
      if (SimpleGraph.edge x y).Adj a b then 1 else 0) (a b : V) :
    ordinaryRimLoad (fun D => ∑ p : V×V,
      (ordinaryRimResidual ψ p.1 p.2/2)*I p.1 p.2 D) a b=ordinaryRimResidual ψ a b := by
  rw [ordinaryRimLoad_combination]
  calc
    _ = (1/2:ℝ)*(∑ p : V×V,ordinaryRimResidual ψ p.1 p.2*
        (if (SimpleGraph.edge p.1 p.2).Adj a b then 1 else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : Q.Adj p.1 p.2
      · rw [hI p.1 p.2 hp a b];ring
      · rw [ordinaryRimResidual_outside ψ p.1 p.2 hp];ring
    _ = _ := symmetric_edge_isolator_sum (ordinaryRimResidual ψ)
      (ordinaryRimResidual_symm ψ)
      (fun x => ordinaryRimResidual_outside ψ x x Q.irrefl) a b

end Oberwolfach
