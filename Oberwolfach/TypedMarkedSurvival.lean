module

public import Oberwolfach.TypedMarkedPotentialResources
public import Oberwolfach.MarkedWheelRestriction

@[expose] public section

/-! Restriction of typed potential candidates uses endpoint injections in
each rim type, not global physical injectivity or disjoint parent spoke types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
  {H₀ Hₖ H₀' Hₖ' : V → U → Prop}

theorem canonicalMarkedCycle_restrict_iff (PE : E → Prop) (PK : K → Prop)
    (hE : Function.Injective (fun e=>(tail e,head e)))
    (hK : Function.Injective (fun e=>(ktail e,khead e)))
    (C : MarkedCycleTuple tail head ktail khead m π b) :
    IsMarkedCycleTuple (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b C.val ↔
        ∀ i,Sum.elim PE PK (markedCycleTypedEdge tail head ktail khead m π b C i) := by
  constructor
  · intro h i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · obtain ⟨e,he⟩ := h.2.2
      have hh := Classical.choose_spec C.property.2.2
      have heq : Classical.choose C.property.2.2=e.val := hK (Prod.ext (hh.1.trans he.1.symm) (hh.2.trans he.2.symm))
      simpa only [markedCycleTypedEdge,Fin.snoc_last,Sum.elim_inr,heq] using e.property
    · obtain ⟨e,he⟩ := h.2.1 j
      have hh := Classical.choose_spec (C.property.2.1 j)
      have heq : Classical.choose (C.property.2.1 j)=e.val := hE (Prod.ext (hh.1.trans he.1.symm) (hh.2.trans he.2.symm))
      simpa only [markedCycleTypedEdge,Fin.snoc_castSucc,Sum.elim_inl,heq] using e.property
  · intro h
    refine ⟨C.property.1,?_,?_⟩
    · intro j
      have hj := h j.castSucc
      simp only [markedCycleTypedEdge,Fin.snoc_castSucc,Sum.elim_inl] at hj
      exact ⟨⟨Classical.choose (C.property.2.1 j),hj⟩,Classical.choose_spec (C.property.2.1 j)⟩
    · have hj := h (Fin.last m)
      simp only [markedCycleTypedEdge,Fin.snoc_last,Sum.elim_inr] at hj
      exact ⟨⟨Classical.choose C.property.2.2,hj⟩,Classical.choose_spec C.property.2.2⟩

theorem markedWheelSurvives_iff_typed_occurrences (PE : E → Prop) (PK : K → Prop)
    (hE : Function.Injective (fun e=>(tail e,head e)))
    (hK : Function.Injective (fun e=>(ktail e,khead e)))
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :
    MarkedWheelSurvives PE PK H₀' Hₖ' W ↔
      ∀ e∈typedMarkedOccurrenceResources W,
        Sum.elim (Sum.elim PE PK) (fun s=>if s.1 then Hₖ' s.2.1 s.2.2 else H₀' s.2.1 s.2.2) e := by
  rw [MarkedWheelSurvives,canonicalMarkedCycle_restrict_iff PE PK hE hK]
  constructor
  · rintro ⟨hc,hh⟩ e he
    cases e with
    | inl e =>
      obtain ⟨i,rfl⟩ := (typedMarkedOccurrenceResources_rim W e).mp he
      exact hc i
    | inr s =>
      obtain ⟨i,rfl⟩ := (typedMarkedOccurrenceResources_spoke W s).mp he
      dsimp only [Sum.elim_inr]
      refine Fin.cases ?_ (fun j=>?_) i
      · simpa only [decide_true,ite_true] using hh.1
      · simpa only [Fin.succ_ne_zero,decide_false,Bool.false_eq_true,ite_false] using hh.2 j
  · intro h
    constructor
    · intro i
      apply h (Sum.inl (markedCycleTypedEdge tail head ktail khead m π b W.1 i))
      rw [typedMarkedOccurrenceResources_rim]
      exact ⟨i,rfl⟩
    · have hh (i : Fin (m+1)) := h (Sum.inr (decide (i=0),W.1.val i,W.2.val))
        ((typedMarkedOccurrenceResources_spoke W _).mpr ⟨i,rfl⟩)
      constructor
      · simpa only [Sum.elim_inr,decide_true,ite_true] using hh 0
      · intro j
        simpa only [Sum.elim_inr,Fin.succ_ne_zero,decide_false,Bool.false_eq_true,ite_false] using hh j.succ

end Oberwolfach
