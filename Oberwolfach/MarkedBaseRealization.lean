module

public import Oberwolfach.MarkedBaseSurvival
public import Oberwolfach.MarkedPhysicalCuts

@[expose] public section

/-! The pattern product counts actual ordinary arcs and the unique marked
closing arc, after the prescribed auxiliary-distance deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (b m : ℕ) (T₀ TK : Finset V)

def MarkedBaseRims (σ : Sym2 V→Option (Bool×Bool)) (f : Fin (m+1)→V) : Prop :=
  (∀ i : Fin m,markedPhysicalRim P π b σ false (f i.castSucc) (f i.succ)=1) ∧
  markedPhysicalRim P π b σ true (f (Fin.last m)) (f 0)=1

theorem markedBase_states_iff_rims (hb : 1≤b) (hm : 2≤m)
    (C : DenseMarkedBaseFamily P π b m T₀ TK) (σ : Sym2 V→Option (Bool×Bool)) :
    (∀ e∈markedBaseRequiredEdges P π b m T₀ TK C,
      σ e=markedBaseRequiredState P π b m T₀ TK C e) ↔ MarkedBaseRims P π b m σ C.val := by
  have hO (i : Fin m) : ¬PermutationClose π b (C.val i.castSucc) (C.val i.succ) :=
    C.property.1 i.castSucc i.succ (by intro h;have hh:=congrArg Fin.val h;simp at hh)
  have hK : ¬PermutationClose π b (C.val (Fin.last m)) (C.val 0) :=
    C.property.1 (Fin.last m) 0 (by intro h;have hh:=congrArg Fin.val h;simp at hh;omega)
  have hstates : (∀ e∈markedBaseRequiredEdges P π b m T₀ TK C,
      σ e=markedBaseRequiredState P π b m T₀ TK C e) ↔
      ∀ i : Fin m⊕Unit,σ (twistedTupleEdge C.val (π (C.val 0)) i)=markedBasePositionState P π b m T₀ TK C i := by
    constructor
    · intro h i
      have hh := h _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      simpa only [markedBaseRequiredState_apply P π b m T₀ TK hb hm] using hh
    · intro h e he
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      rw [markedBaseRequiredState_apply P π b m T₀ TK hb hm]
      exact h i
  rw [hstates]
  have hOrd (i : Fin m) :
      markedPhysicalRim P π b σ false (C.val i.castSucc) (C.val i.succ)=1 ↔
        σ s(C.val i.castSucc,C.val i.succ)=some (false,orientationBit (C.val i.castSucc) (C.val i.succ)) := by
    simp [markedPhysicalRim,permutationSeparatedMatrix,markedPhysicalOrientation,hO i,C.property.2.2.2.1 i]
  have hLast : markedPhysicalRim P π b σ true (C.val (Fin.last m)) (C.val 0)=1 ↔
      σ s(C.val (Fin.last m),π (C.val 0))=some (true,orientationBit (C.val (Fin.last m)) (π (C.val 0))) := by
    simp [markedPhysicalRim,permutationSeparatedMatrix,markedPhysicalOrientation,hK,C.property.2.2.2.2]
  constructor
  · intro h
    exact ⟨fun i=>(hOrd i).mpr (h (Sum.inl i)),hLast.mpr (h (Sum.inr ()))⟩
  · intro h i
    cases i with
    | inl i=>exact (hOrd i).mp (h.1 i)
    | inr i=>exact hLast.mp h.2

theorem markedBaseSurvivalSum_count (hb : 1≤b) (hm : 2≤m)
    (σ : Sym2 V→Option (Bool×Bool)) :
    markedBaseSurvivalSum P π b m T₀ TK σ=
      (Fintype.card {C : DenseMarkedBaseFamily P π b m T₀ TK // MarkedBaseRims P π b m σ C.val}:ℝ)/
        (Fintype.card V:ℝ)^(m+1) := by
  unfold markedBaseSurvivalSum
  simp_rw [patternValue_indicator,markedBase_states_iff_rims P π b m T₀ TK hb hm]
  rw [← Finset.mul_sum]
  have hcard : (∑ C : DenseMarkedBaseFamily P π b m T₀ TK,
      if MarkedBaseRims P π b m σ C.val then (1:ℝ) else 0)=
      Fintype.card {C : DenseMarkedBaseFamily P π b m T₀ TK // MarkedBaseRims P π b m σ C.val} := by
    simp only [Fintype.card_subtype,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [hcard]
  ring

end Oberwolfach
