module

public import Oberwolfach.OrdinaryDecompositionEdges
public import Oberwolfach.ResourceDecompositionCounts

@[expose] public section

/-! Exact ordinary wheel partitions, union, and necessary divisibility.
The balance identity is derived from the actual edge partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_packing_exact_decomposition {P Q F : SimpleGraph V} {Hbase H : V → U → Prop} {r : ℕ}
    (M : Finset (OrdinaryWheel P F Hbase r))
    (hM : ∀ a∈M,∀ b∈M,a≠b → Disjoint (ordinaryWheelResources a) (ordinaryWheelResources b))
    (hcover : M.biUnion ordinaryWheelResources=ordinaryHostResources Q H) :
    HasOrdinaryWheelDecomposition Q H r := by
  exact resource_decomposition_map ordinaryWheelResources ordinaryWheelResources ordinaryWheelUniversal
    ordinaryWheelUniversal_resources _ ⟨M,hM,hcover⟩

theorem ordinaryHostResources_disjoint (Q P : SimpleGraph V) (H K : V → U → Prop)
    (hQP : Disjoint Q P) (hHK : ∀ v u,¬(H v u ∧ K v u)) :
    Disjoint (ordinaryHostResources Q H) (ordinaryHostResources P K) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  cases e with
  | inl e =>
    rw [ordinaryHostResources_rim] at he hf
    induction e using Sym2.ind with
    | _ v w => exact (disjoint_iff_inf_le.mp hQP) ⟨he,hf⟩
  | inr vu =>
    rcases vu with ⟨v,u⟩
    rw [ordinaryHostResources_spoke] at he hf
    exact hHK v u ⟨he,hf⟩

theorem ordinary_wheel_decomposition_union (Q P : SimpleGraph V) (H K : V → U → Prop) (r : ℕ)
    (hQ : HasOrdinaryWheelDecomposition Q H r) (hP : HasOrdinaryWheelDecomposition P K r)
    (hQP : Disjoint Q P) (hHK : ∀ v u,¬(H v u ∧ K v u)) :
    HasOrdinaryWheelDecomposition (Q⊔P) (fun v u => H v u ∨ K v u) r := by
  unfold HasOrdinaryWheelDecomposition at *
  rw [ordinaryHostResources_union]
  exact resource_decomposition_union _ _ _ hQ hP (ordinaryHostResources_disjoint Q P H K hQP hHK)

theorem finite_wheel_spoke_column {W : Type*} [Fintype W]
    (C : W → SimpleGraph V) (hub : W → U) (r : ℕ)
    (hC : ∀ w,IsEmbeddedCycle (C w) r) (ψ : W → ℝ) (u : U) :
    (∑ v,∑ w,if hub w=u ∧ v∈(C w).support then ψ w else 0)=
      (r:ℝ)*(∑ w,if hub w=u then ψ w else 0) := by
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hu : hub w=u
  · simp only [hu,true_and,ite_true]
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun v => v∈(C w).support)=(C w).support.toFinset := by
      ext v; simp
    have hc : (C w).support.toFinset.card=r := (hC w).support_card
    rw [he,Finset.sum_const,nsmul_eq_mul,hc]
  · simp only [hu,false_and,ite_false,Finset.sum_const_zero,mul_zero]

theorem ordinary_wheel_decomposition_exact_loads (Q : SimpleGraph V) (H : V → U → Prop) (r : ℕ)
    (h : HasOrdinaryWheelDecomposition Q H r) :
    ∃ M : Finset (UniversalOrdinaryWheel V U r),
      (∀ v w,(∑ W : M,if (ordinaryWheelRim W.val).Adj v w then (1:ℝ) else 0)=if Q.Adj v w then 1 else 0) ∧
      (∀ v u,(∑ W : M,if ordinaryWheelHub W.val=u ∧ v∈(ordinaryWheelRim W.val).support then (1:ℝ) else 0)=if H v u then 1 else 0) := by
  obtain ⟨M,hM,hcover⟩ := h
  refine ⟨M,?_,?_⟩
  · intro v w
    have he : (∑ W : M,if (ordinaryWheelRim W.val).Adj v w then (1:ℝ) else 0)=
        ∑ W∈M,if (ordinaryWheelRim W).Adj v w then (1:ℝ) else 0 := by
      convert (Finset.sum_coe_sort M (fun W : UniversalOrdinaryWheel V U r => if (ordinaryWheelRim W).Adj v w then (1:ℝ) else 0)) using 1 <;> congr!
    rw [he]
    have hh := resource_decomposition_indicator (ordinaryWheelResources (P:=(⊤ : SimpleGraph V)) (F:=⊥) (Hbase:=fun (_ : V) (_ : U) => True) (r:=r)) M (ordinaryHostResources Q H) hM hcover (Sum.inl s(v,w))
    simpa only [ordinaryWheelResources_rim,ordinaryHostResources_rim,SimpleGraph.mem_edgeSet] using hh
  · intro v u
    have he : (∑ W : M,if ordinaryWheelHub W.val=u ∧ v∈(ordinaryWheelRim W.val).support then (1:ℝ) else 0)=
        ∑ W∈M,if ordinaryWheelHub W=u ∧ v∈(ordinaryWheelRim W).support then (1:ℝ) else 0 := by
      convert (Finset.sum_coe_sort M (fun W : UniversalOrdinaryWheel V U r => if ordinaryWheelHub W=u ∧ v∈(ordinaryWheelRim W).support then (1:ℝ) else 0)) using 1 <;> congr!
    rw [he]
    have hh := resource_decomposition_indicator (ordinaryWheelResources (P:=(⊤ : SimpleGraph V)) (F:=⊥) (Hbase:=fun (_ : V) (_ : U) => True) (r:=r)) M (ordinaryHostResources Q H) hM hcover (Sum.inr (v,u))
    simpa only [ordinaryWheelResources_spoke,ordinaryHostResources_spoke] using hh

theorem ordinary_wheel_decomposition_balance (Q : SimpleGraph V) (H : V → U → Prop) (r : ℕ)
    (h : HasOrdinaryWheelDecomposition Q H r) :
    (∀ v,Q.degree v=2*(Finset.univ.filter (fun u => H v u)).card) ∧
    (∀ u,r∣(Finset.univ.filter (fun v => H v u)).card) := by
  obtain ⟨M,hrim,hspoke⟩ := ordinary_wheel_decomposition_exact_loads Q H r h
  let C : M → SimpleGraph V := fun w => ordinaryWheelRim w.val
  let hub : M → U := fun w => ordinaryWheelHub w.val
  have hC (w : M) : IsEmbeddedCycle (C w) r := w.val.val.1.val.property
  constructor
  · intro v
    have hh := finite_wheel_load_balance C hub r hC (fun _ => (1:ℝ)) v
    change 2*(∑ u,∑ W : M,if ordinaryWheelHub W.val=u ∧ v∈(ordinaryWheelRim W.val).support then (1:ℝ) else 0)=
      ∑ w,∑ W : M,if (ordinaryWheelRim W.val).Adj v w then (1:ℝ) else 0 at hh
    simp_rw [hspoke,hrim] at hh
    have hs : (∑ u,if H v u then (1:ℝ) else 0)=((Finset.univ.filter (fun u => H v u)).card:ℝ) := by
      rw [← Finset.sum_filter];simp
    rw [hs,graph_adjacency_row_sum] at hh
    exact_mod_cast hh.symm
  · intro u
    have hh := finite_wheel_spoke_column C hub r hC (fun _ => (1:ℝ)) u
    change (∑ v,∑ W : M,if ordinaryWheelHub W.val=u ∧ v∈(ordinaryWheelRim W.val).support then (1:ℝ) else 0)=
      (r:ℝ)*(∑ W : M,if ordinaryWheelHub W.val=u then (1:ℝ) else 0) at hh
    simp_rw [hspoke] at hh
    have hs : (∑ v,if H v u then (1:ℝ) else 0)=((Finset.univ.filter (fun v => H v u)).card:ℝ) := by
      rw [← Finset.sum_filter];simp
    have ht : (∑ W : M,if ordinaryWheelHub W.val=u then (1:ℝ) else 0)=
      ((M.filter (fun W => ordinaryWheelHub W=u)).card:ℝ) := by
      have he : (∑ W : M,if ordinaryWheelHub W.val=u then (1:ℝ) else 0)=
          ∑ W∈M,if ordinaryWheelHub W=u then (1:ℝ) else 0 := by
        convert (Finset.sum_coe_sort M (fun W : UniversalOrdinaryWheel V U r => if ordinaryWheelHub W=u then (1:ℝ) else 0)) using 1 <;> congr!
      rw [he,← Finset.sum_filter];simp
    rw [hs,ht] at hh
    exact ⟨(M.filter (fun W => ordinaryWheelHub W=u)).card,by exact_mod_cast hh⟩

end Oberwolfach
