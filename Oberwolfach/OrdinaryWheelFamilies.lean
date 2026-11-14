module

public import Oberwolfach.OrdinaryExactDecomposition
public import Oberwolfach.OrdinaryWheelDisjointness

@[expose] public section

/-! Turning an indexed family of actual wheels into its ordinary rim and
spoke graphs. Edge partitions and the avoidance of old root edges are
proved in that physical representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U] [Fintype I]
    {G F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}

def wheelFamilyRim (W : I → OrdinaryWheel G F H r) : SimpleGraph V := ⨆ i,ordinaryWheelRim (W i)
def wheelFamilySpokes (W : I → OrdinaryWheel G F H r) (v : V) (u : U) : Prop :=
  ∃ i,ordinaryWheelHub (W i)=u ∧ v∈(ordinaryWheelRim (W i)).support

theorem wheelFamily_resources (W : I → OrdinaryWheel G F H r) :
    ordinaryHostResources (wheelFamilyRim W) (wheelFamilySpokes W)=
      Finset.univ.biUnion (fun i => ordinaryWheelResources (W i)) := by
  ext e
  cases e with
  | inl e =>
    induction e using Sym2.ind with
    | _ v w =>
      simp only [ordinaryHostResources_rim,SimpleGraph.mem_edgeSet,wheelFamilyRim,SimpleGraph.iSup_adj,
        Finset.mem_biUnion,Finset.mem_univ,true_and,ordinaryWheelResources_rim]
  | inr vu =>
    rcases vu with ⟨v,u⟩
    simp only [ordinaryHostResources_spoke,wheelFamilySpokes,Finset.mem_biUnion,Finset.mem_univ,
      true_and,ordinaryWheelResources_spoke]

theorem wheelFamily_subhost (W : I → OrdinaryWheel G F H r) :
    wheelFamilyRim W ≤ G ∧ ∀ v u,wheelFamilySpokes W v u → H v u := by
  constructor
  · exact iSup_le (fun i => (W i).val.1.property)
  · intro v u h
    obtain ⟨i,hi,hv⟩ := h
    rw [← hi]
    exact (W i).property.1 v hv

theorem wheelFamily_decomposition (W : I → OrdinaryWheel G F H r)
    (hW : ∀ i j,i≠j → Disjoint (ordinaryWheelResources (W i)) (ordinaryWheelResources (W j))) :
    HasOrdinaryWheelDecomposition (wheelFamilyRim W) (wheelFamilySpokes W) r := by
  let M := Finset.univ.image W
  apply ordinary_packing_exact_decomposition M
  · intro A hA B hB hAB
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
    exact hW i j (fun h => hAB (congrArg W h))
  · rw [wheelFamily_resources]
    ext e
    simp only [M,Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨A,⟨i,rfl⟩,he⟩;exact ⟨i,he⟩
    · rintro ⟨i,hi⟩;exact ⟨W i,⟨i,rfl⟩,hi⟩

theorem wheel_avoids_old_edges (W : OrdinaryWheel G F H r) (R : Finset V) (B : Finset U) (x : V)
    (hroot : ∀ v∈(ordinaryWheelRim W).support,v∈R → v=x)
    (hhub : ordinaryWheelHub W∉B) (L : SimpleGraph V) (K : V → U → Prop)
    (hL : L.support ⊆ (R:Set V)) (hK : ∀ v u,K v u → u∈B) :
    Disjoint (ordinaryWheelResources W) (ordinaryHostResources L K) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  cases e with
  | inl e =>
    rw [ordinaryWheelResources_rim] at he
    rw [ordinaryHostResources_rim] at hf
    induction e using Sym2.ind with
    | _ v w =>
      have hv := hroot v he.mem_support_left (hL hf.mem_support_left)
      have hw := hroot w he.mem_support_right (hL hf.mem_support_right)
      exact he.ne (hv.trans hw.symm)
  | inr vu =>
    rcases vu with ⟨v,u⟩
    rw [ordinaryWheelResources_spoke] at he
    rw [ordinaryHostResources_spoke] at hf
    exact hhub (he.1.symm ▸ hK v u hf)

theorem wheelFamily_avoids_old_edges (W : I → OrdinaryWheel G F H r)
    (R : Finset V) (B : Finset U) (x : I → V)
    (hroot : ∀ i,∀ v∈(ordinaryWheelRim (W i)).support,v∈R → v=x i)
    (hhub : ∀ i,ordinaryWheelHub (W i)∉B) (L : SimpleGraph V) (K : V → U → Prop)
    (hL : L.support ⊆ (R:Set V)) (hK : ∀ v u,K v u → u∈B) :
    Disjoint (ordinaryHostResources (wheelFamilyRim W) (wheelFamilySpokes W)) (ordinaryHostResources L K) := by
  rw [wheelFamily_resources]
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
  exact (Finset.disjoint_left.mp (wheel_avoids_old_edges (W i) R B (x i) (hroot i) (hhub i) L K hL hK)) hi hf

theorem wheelFamily_vertex_bound (W : I → OrdinaryWheel G F H r) :
    (wheelFamilyRim W).support.toFinset.card ≤ r*Fintype.card I ∧
    (Finset.univ.image (fun i => ordinaryWheelHub (W i))).card ≤ Fintype.card I := by
  constructor
  · have he : (wheelFamilyRim W).support.toFinset=
        Finset.univ.biUnion (fun i => (ordinaryWheelRim (W i)).support.toFinset) := by
      ext v
      simp only [Set.mem_toFinset,Finset.mem_biUnion,Finset.mem_univ,true_and,SimpleGraph.mem_support,
        wheelFamilyRim,SimpleGraph.iSup_adj]
      constructor
      · rintro ⟨w,i,h⟩;exact ⟨i,w,h⟩
      · rintro ⟨i,w,h⟩;exact ⟨w,i,h⟩
    rw [he]
    calc
      _ ≤ ∑ i,(ordinaryWheelRim (W i)).support.toFinset.card := Finset.card_biUnion_le
      _ = _ := by
        have hc (i : I) : (ordinaryWheelRim (W i)).support.toFinset.card=r := (W i).val.1.val.property.support_card
        simp only [hc,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.mul_comm]
  · exact (Finset.card_image_le).trans_eq (Finset.card_univ)

end Oberwolfach
