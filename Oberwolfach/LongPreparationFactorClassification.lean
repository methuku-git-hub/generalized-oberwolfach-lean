module

public import Oberwolfach.FactorCyclePartition
public import Oberwolfach.LongPreparationVertexFractions

@[expose] public section
/-! Classification of vertices by the lengths of their actual cycle components. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def longPreparationCycleClass {n:ℕ} (F:SimpleGraph (Fin n))
    (hF:F.IsRegularOfDegree 2) (K:ℕ) (v:Fin n):Option (Fin K):=by
  let c:=Fintype.card (F.connectedComponentMk v)
  have hc:3≤c:=(component_regular_two_cycle_iso F hF (F.connectedComponentMk v)).1
  exact if h:c≤K then some ⟨c-1,by omega⟩ else none

theorem long_preparation_cycle_class {n:ℕ} (F:SimpleGraph (Fin n))
    (hF:F.IsRegularOfDegree 2) (K:ℕ) (v:Fin n):
    (longPreparationCycleClass F hF K v=none ↔
      K<Fintype.card (F.connectedComponentMk v)) ∧
    (∀ i:Fin K, longPreparationCycleClass F hF K v=some i ↔
      Fintype.card (F.connectedComponentMk v)=i.val+1):=by
  let c:=Fintype.card (F.connectedComponentMk v)
  have hc:3≤c:=(component_regular_two_cycle_iso F hF (F.connectedComponentMk v)).1
  unfold longPreparationCycleClass
  dsimp only
  by_cases h:c≤K
  · change Fintype.card (F.connectedComponentMk v)≤K at h
    rw [dif_pos h]
    constructor
    · simp only [Option.some_ne_none, false_iff, not_lt]
      exact h
    · intro i
      constructor
      · intro heq
        have hv: c-1=i.val:=congrArg Fin.val (Option.some.inj heq)
        omega
      · intro heq
        apply congrArg some
        apply Fin.ext
        simp only
        omega
  · have hk:K<c:=by omega
    change ¬Fintype.card (F.connectedComponentMk v)≤K at h
    rw [dif_neg h]
    constructor
    · exact ⟨fun _=>hk,fun _=>rfl⟩
    · intro i
      constructor
      · intro heq
        cases heq
      · intro heq
        have hi:=i.isLt
        omega
end Oberwolfach
