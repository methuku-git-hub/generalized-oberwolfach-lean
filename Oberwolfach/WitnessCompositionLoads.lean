module

public import Oberwolfach.HypergraphLineGraph

@[expose] public section

/-! Counting the roots using a direct witness or one of its corroborating
witnesses. Every multiplicity is counted at the original coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_witness_image_load
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (T : Finset J) (A : Finset I) (D : J → Finset I) (f : I → I)
    {b d : ℕ} (hD : ∀ j∈T,D j⊆A)
    (hload : ∀ i,(T.filter (fun j=>i∈D j)).card≤d)
    (hpre : ∀ w,(A.filter (fun i=>f i=w)).card≤b) (w : I) :
    (T.filter (fun j=>w∈(D j).image f)).card≤b*d := by
  classical
  let F := A.filter (fun i=>f i=w)
  have hsub : T.filter (fun j=>w∈(D j).image f)⊆
      F.biUnion (fun i=>T.filter (fun j=>i∈D j)) := by
    intro j hj
    obtain ⟨hjT,hj⟩ := Finset.mem_filter.mp hj
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hj
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨hD j hjT hi,he⟩,
      Finset.mem_filter.mpr ⟨hjT,hi⟩⟩
  calc
    _ ≤ (F.biUnion (fun i=>T.filter (fun j=>i∈D j))).card := Finset.card_le_card hsub
    _ ≤ F.card*d := Finset.card_biUnion_le_card_mul _ _ _ (fun i _=>hload i)
    _ ≤ b*d := Nat.mul_le_mul_right _ (hpre w)

theorem hypergraph_outside_clique_incidence
    {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (R : E → Finset V) {k B : ℕ} (hsize : ∀ e,(R e).card≤k)
    (hcodeg : ∀ v w,v≠w →
      (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (a : V) (T : Finset E) (hT : ∀ e∈T,a∈R e) (w : E) :
    (T.filter (fun e=>∃ v∈R e,v≠a ∧ v∈R w)).card≤k*B := by
  let A : V → Finset E := fun v=>Finset.univ.filter (fun e=>a∈R e ∧ v∈R e)
  have hsub : T.filter (fun e=>∃ v∈R e,v≠a ∧ v∈R w)⊆
      ((R w).erase a).biUnion A := by
    intro e he
    obtain ⟨heT,v,hve,hva,hvw⟩ := Finset.mem_filter.mp he
    exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_erase.mpr ⟨hva,hvw⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hT e heT,hve⟩⟩
  calc
    _ ≤ (((R w).erase a).biUnion A).card := Finset.card_le_card hsub
    _ ≤ ((R w).erase a).card*B := Finset.card_biUnion_le_card_mul _ _ _
      (fun v hv=>hcodeg a v (Ne.symm (Finset.mem_erase.mp hv).1))
    _ ≤ (R w).card*B := Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.erase_subset _ _))
    _ ≤ k*B := Nat.mul_le_mul_right _ (hsize w)

end Oberwolfach
