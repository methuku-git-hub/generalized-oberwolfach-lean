module

public import Oberwolfach.VortexApplications

@[expose] public section

/-! Appending the empty pair to a vortex without extending its size recurrence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def Vortex.extendedVertices {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (i : ℕ) : Finset V :=
  if i ≤ Q.length then Q.vertices i else ∅

def Vortex.extendedIndices {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (i : ℕ) : Finset U :=
  if i ≤ Q.length then Q.indices i else ∅

theorem Vortex.extendedVertices_eq {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    {i : ℕ} (hi : i ≤ Q.length) :
    Q.extendedVertices i = Q.vertices i := by simp [Vortex.extendedVertices, hi]

theorem Vortex.extendedIndices_eq {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    {i : ℕ} (hi : i ≤ Q.length) :
    Q.extendedIndices i = Q.indices i := by simp [Vortex.extendedIndices, hi]

theorem Vortex.extendedVertices_empty {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    {i : ℕ} (hi : Q.length < i) : Q.extendedVertices i = ∅ :=
  by simp [Vortex.extendedVertices, show ¬ i ≤ Q.length by omega]

theorem Vortex.extendedIndices_empty {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    {i : ℕ} (hi : Q.length < i) : Q.extendedIndices i = ∅ :=
  by simp [Vortex.extendedIndices, show ¬ i ≤ Q.length by omega]

theorem Vortex.extendedVertices_subset {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    {j k : ℕ} (hjk : j ≤ k) : Q.extendedVertices k ⊆ Q.extendedVertices j := by
  by_cases hk : k ≤ Q.length
  · rw [Q.extendedVertices_eq hk, Q.extendedVertices_eq (hjk.trans hk)]
    exact finset_chain_subset Q.vertices Q.length Q.nested hjk hk
  · rw [Q.extendedVertices_empty (by omega)]
    exact Finset.empty_subset _

theorem Vortex.extendedIndices_subset {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    {j k : ℕ} (hjk : j ≤ k) : Q.extendedIndices k ⊆ Q.extendedIndices j := by
  by_cases hk : k ≤ Q.length
  · rw [Q.extendedIndices_eq hk, Q.extendedIndices_eq (hjk.trans hk)]
    exact finset_chain_subset Q.indices k (fun i _ => Q.indices_nested i) hjk (le_refl k)
  · rw [Q.extendedIndices_empty (by omega)]
    exact Finset.empty_subset _

theorem Vortex.extended_later_size_le_quarter {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (he : 0 ≤ ε) (heq : ε ≤ 1 / 4) {j k : ℕ} (hjk : j < k) :
    ((Q.extendedVertices k).card : ℝ) ≤ (Q.extendedVertices j).card / 4 := by
  by_cases hk : k ≤ Q.length
  · rw [Q.extendedVertices_eq hk, Q.extendedVertices_eq (hjk.le.trans hk)]
    exact Q.later_size_le_quarter he heq hjk hk
  · rw [Q.extendedVertices_empty (by omega), Finset.card_empty, Nat.cast_zero]
    positivity

theorem Vortex.extended_estimates {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (hreg : G.IsRegularOfDegree D) (hn : 0 < Fintype.card V)
    (hρ : 0 < initialIndexDensity U D) (hb : 0 ≤ β) (i : ℕ) :
    |2 * ((Q.extendedIndices i).card : ℝ) / initialIndexDensity U D -
        ((D : ℝ) / Fintype.card V) * (Q.extendedVertices i).card| ≤
      β * (Q.extendedVertices i).card ∧
    ∀ x ∈ Q.extendedVertices (i - 2),
      |((G.neighborFinset x ∩ Q.extendedVertices i).card : ℝ) -
        2 * (Q.extendedIndices i).card / initialIndexDensity U D| ≤
      β * (Q.extendedVertices i).card := by
  by_cases hi : i ≤ Q.length
  · rw [Q.extendedVertices_eq hi, Q.extendedIndices_eq hi,
      Q.extendedVertices_eq (by omega : i - 2 ≤ Q.length)]
    exact Q.estimates_including_zero hreg hn hρ hb i hi
  · rw [Q.extendedVertices_empty (by omega : Q.length < i),
      Q.extendedIndices_empty (by omega : Q.length < i)]
    simp

theorem Vortex.extended_difference_degree_estimates {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (hreg : G.IsRegularOfDegree D) (hn : 0 < Fintype.card V)
    (hρ : 0 < initialIndexDensity U D) (hb : 0 ≤ β)
    (he : 0 ≤ ε) (heq : ε ≤ 1 / 4) {j k : ℕ} (hjk : j < k)
    (x : V) (hx : x ∈ Q.extendedVertices (k - 2)) :
    |2 * ((Q.extendedIndices j \ Q.extendedIndices k).card : ℝ) /
          initialIndexDensity U D -
        ((D : ℝ) / Fintype.card V) *
          (Q.extendedVertices j \ Q.extendedVertices k).card| ≤
      (5 / 3 : ℝ) * β * (Q.extendedVertices j \ Q.extendedVertices k).card ∧
    |((G.neighborFinset x ∩ (Q.extendedVertices j \ Q.extendedVertices k)).card : ℝ) -
        2 * (Q.extendedIndices j \ Q.extendedIndices k).card /
          initialIndexDensity U D| ≤
      (5 / 3 : ℝ) * β * (Q.extendedVertices j \ Q.extendedVertices k).card := by
  have hA := Q.extended_estimates hreg hn hρ hb j
  have hB := Q.extended_estimates hreg hn hρ hb k
  have hxj : x ∈ Q.extendedVertices (j - 2) :=
    Q.extendedVertices_subset (by omega : j - 2 ≤ k - 2) hx
  exact nested_domains_degree_subtraction G
    (Q.extendedVertices_subset hjk.le) (Q.extendedIndices_subset hjk.le)
    β (initialIndexDensity U D) ((D : ℝ) / Fintype.card V) hb
    (Q.extended_later_size_le_quarter he heq hjk) hA.1 hB.1 x (hA.2 x hxj) (hB.2 x hx)

end Oberwolfach
