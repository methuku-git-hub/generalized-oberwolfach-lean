module

public import Oberwolfach.RegularCycleIsomorphism
public import Oberwolfach.DecompositionCounts

@[expose] public section

/-! Decomposing an input two-factor into its actual cycle components, preserving
orders and the allowed-length condition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def componentVertexEquiv {V : Type*} (G : SimpleGraph V) :
    (Σ C : G.ConnectedComponent, C) ≃ V where
  toFun z := z.2.val
  invFun v := ⟨G.connectedComponentMk v, ⟨v, rfl⟩⟩
  left_inv := by
    rintro ⟨C, ⟨v, hv⟩⟩
    change G.connectedComponentMk v = C at hv
    subst C
    rfl
  right_inv := by intro v; rfl

theorem component_orders_sum {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    ∑ C : G.ConnectedComponent, Fintype.card C = Fintype.card V := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (componentVertexEquiv G)

theorem component_isCycleCopy {n : ℕ} (F : SimpleGraph (Fin n))
    (hF : F.IsRegularOfDegree 2) (C : F.ConnectedComponent) :
    IsCycleCopy C.toSimpleGraph.spanningCoe (Fintype.card C) := by
  obtain ⟨hthree, ⟨e⟩⟩ := component_regular_two_cycle_iso F hF C
  let f : Fin (Fintype.card C) ↪ Fin n := {
    toFun := fun i => (e i).val
    inj' := by intro i j hij; apply e.injective; exact Subtype.ext hij }
  apply (isCycleCopy_iff_map _).mpr
  refine ⟨hthree, f, ?_⟩
  ext u v
  rw [SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph, SimpleGraph.map_adj]
  constructor
  · rintro ⟨hu, huv⟩
    have hv : v ∈ C.supp := (C.mem_supp_congr_adj huv).mp hu
    refine ⟨e.symm ⟨u, hu⟩, e.symm ⟨v, hv⟩, e.symm.map_rel_iff.mpr huv, ?_, ?_⟩ <;>
      simp only [f, Function.Embedding.coeFn_mk, RelIso.apply_symm_apply]
  · rintro ⟨i, j, hij, rfl, rfl⟩
    exact ⟨(e i).property, e.map_rel_iff.mpr hij⟩

theorem reachable_order_eq_component_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    (C : G.ConnectedComponent) (v : V) (hv : v ∈ C.supp) :
    Nat.card {x : V // G.Reachable v x} = Fintype.card C := by
  have heq : ({x | G.Reachable v x} : Set V) = C.supp := by
    ext x
    change G.Reachable v x ↔ G.connectedComponentMk x = C
    change G.connectedComponentMk v = C at hv
    rw [← SimpleGraph.ConnectedComponent.eq, hv]
    exact eq_comm
  change ({x | G.Reachable v x} : Set V).ncard = _
  rw [heq]
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.refl _)

theorem AllowedCycleLengths_iff_component_orders {n : ℕ}
    (F : SimpleGraph (Fin n)) (S : Set ℕ) :
    AllowedCycleLengths F S ↔ ∀ C : F.ConnectedComponent, Fintype.card C ∈ S := by
  constructor
  · intro h C
    obtain ⟨v, hv⟩ := C.nonempty_supp
    rw [← reachable_order_eq_component_card F C v hv]
    exact h v
  · intro h v
    rw [reachable_order_eq_component_card F (F.connectedComponentMk v) v rfl]
    exact h _

theorem two_regular_cycle_partition {n : ℕ} (F : SimpleGraph (Fin n))
    (hF : F.IsRegularOfDegree 2) :
    ∃ q : ℕ, ∃ H : Fin q → SimpleGraph (Fin n), ∃ r : Fin q → ℕ,
      EdgePartition F H ∧ (∀ i, IsCycleCopy (H i) (r i)) ∧
      (∑ i, r i) = n ∧
      (∀ S : Set ℕ, AllowedCycleLengths F S ↔ ∀ i, r i ∈ S) := by
  let q := Fintype.card F.ConnectedComponent
  let e : Fin q ≃ F.ConnectedComponent := (Fintype.equivFin F.ConnectedComponent).symm
  let H (i : Fin q) := (e i).toSimpleGraph.spanningCoe
  let r (i : Fin q) := Fintype.card (e i)
  refine ⟨q, H, r, ?_, ?_, ?_, ?_⟩
  · intro u v
    have hi (i : Fin q) : (H i).Adj u v ↔ u ∈ (e i).supp ∧ F.Adj u v :=
      SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph (e i)
    constructor
    · constructor
      · intro huv
        refine ⟨e.symm (F.connectedComponentMk u), (hi _).mpr ⟨?_, huv⟩⟩
        simp only [Equiv.apply_symm_apply]
        rfl
      · rintro ⟨i, huv⟩
        exact ((hi i).mp huv).2
    · intro i j hui huj
      apply e.injective
      have hi' := ((hi i).mp hui).1
      have hj' := ((hi j).mp huj).1
      exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hi' hj'
  · intro i
    exact component_isCycleCopy F hF (e i)
  · change (∑ i, Fintype.card (e i)) = n
    calc
      (∑ i, Fintype.card (e i)) = ∑ C : F.ConnectedComponent, Fintype.card C :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = n := by simpa only [Fintype.card_fin] using component_orders_sum F
  · intro S
    rw [AllowedCycleLengths_iff_component_orders]
    exact ⟨fun h i => h (e i), fun h C => by
      obtain ⟨i, rfl⟩ := e.surjective C
      exact h i⟩

end Oberwolfach
