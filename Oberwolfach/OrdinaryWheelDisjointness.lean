module

public import Oberwolfach.OrdinaryWheelResources

@[expose] public section

/-! Exact edge-disjointness tests for ordinary wheels, including wheels
that share one prescribed rim vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {P F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}

theorem ordinaryWheelResources_disjoint_iff (W Z : OrdinaryWheel P F H r) :
    Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z) ↔
      Disjoint (ordinaryWheelRim W) (ordinaryWheelRim Z) ∧
      (ordinaryWheelHub W=ordinaryWheelHub Z →
        Disjoint (ordinaryWheelRim W).support.toFinset (ordinaryWheelRim Z).support.toFinset) := by
  constructor
  · intro h
    constructor
    · apply disjoint_iff_inf_le.mpr
      intro v w hvw
      have he : Sum.inl s(v,w)∈ordinaryWheelResources W :=
        (ordinaryWheelResources_rim W _).mpr hvw.1
      have hf : Sum.inl s(v,w)∈ordinaryWheelResources Z :=
        (ordinaryWheelResources_rim Z _).mpr hvw.2
      exact ((Finset.disjoint_left.mp h) he hf).elim
    · intro hh
      apply Finset.disjoint_left.mpr
      intro v hv hz
      have he : Sum.inr (v,ordinaryWheelHub W)∈ordinaryWheelResources W :=
        (ordinaryWheelResources_spoke W _ _).mpr ⟨rfl,Set.mem_toFinset.mp hv⟩
      have hf : Sum.inr (v,ordinaryWheelHub W)∈ordinaryWheelResources Z :=
        (ordinaryWheelResources_spoke Z _ _).mpr ⟨hh.symm,Set.mem_toFinset.mp hz⟩
      exact (Finset.disjoint_left.mp h) he hf
  · rintro ⟨hrim,hspoke⟩
    apply Finset.disjoint_left.mpr
    intro e he hf
    cases e with
    | inl e =>
      rw [ordinaryWheelResources_rim] at he hf
      induction e using Sym2.ind with
      | _ v w => exact (disjoint_iff_inf_le.mp hrim) ⟨he,hf⟩
    | inr vu =>
      rcases vu with ⟨v,u⟩
      rw [ordinaryWheelResources_spoke] at he hf
      have hh := hspoke (he.1.trans hf.1.symm)
      exact (Finset.disjoint_left.mp hh) (Set.mem_toFinset.mpr he.2) (Set.mem_toFinset.mpr hf.2)

theorem graph_disjoint_of_single_common_support (Q P : SimpleGraph V) (x : V)
    (h : ∀ v,v∈Q.support → v∈P.support → v=x) : Disjoint Q P := by
  apply disjoint_iff_inf_le.mpr
  intro v w hvw
  have hv := h v hvw.1.mem_support_left hvw.2.mem_support_left
  have hw := h w hvw.1.mem_support_right hvw.2.mem_support_right
  exact (hvw.1.ne (hv.trans hw.symm)).elim

theorem ordinaryWheels_disjoint_at_one_root (W Z : OrdinaryWheel P F H r) (x : V)
    (hcommon : ∀ v,v∈(ordinaryWheelRim W).support → v∈(ordinaryWheelRim Z).support → v=x)
    (hhub : ordinaryWheelHub W≠ordinaryWheelHub Z) :
    Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z) := by
  exact (ordinaryWheelResources_disjoint_iff W Z).mpr
    ⟨graph_disjoint_of_single_common_support _ _ x hcommon,fun hh => (hhub hh).elim⟩

def optionWheelRimSupport (W : Option (OrdinaryWheel P F H r)) : Finset V :=
  W.elim ∅ (fun w => (ordinaryWheelRim w).support.toFinset)

def optionWheelHubSet (W : Option (OrdinaryWheel P F H r)) : Finset U :=
  W.elim ∅ (fun w => {ordinaryWheelHub w})

theorem optionWheelRimSupport_card (W : Option (OrdinaryWheel P F H r)) :
    (optionWheelRimSupport W).card ≤ r := by
  cases W with
  | none => simp [optionWheelRimSupport]
  | some W => exact le_of_eq W.val.1.val.property.support_card

theorem optionWheelHubSet_card (W : Option (OrdinaryWheel P F H r)) :
    (optionWheelHubSet W).card ≤ 1 := by cases W <;> simp [optionWheelHubSet]

end Oberwolfach
