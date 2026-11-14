module

public import Oberwolfach.OrdinaryProtectedReserveEdit
public import Oberwolfach.OrdinaryProtectedRequiredDegree

@[expose] public section
/-! Protect the reference inside the inner set and the rim resources of the
reservoir. Both pieces remain in the reference and have explicit degree cost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryMatchingProtect (Reference : SimpleGraph V) (Inner : Finset V)
    (K : Finset (Sym2 V ⊕ (V × U))) : SimpleGraph V :=
  spanningRestriction Reference Inner ⊔ ordinaryResourceRim Reference K

theorem ordinary_matching_protect_choice
    (Reference : SimpleGraph V) (Inner : Finset V) (K : Finset (Sym2 V ⊕ (V × U))) :
    let Protect := ordinaryMatchingProtect Reference Inner K;
    Protect ≤ Reference ∧ spanningRestriction Reference Inner ≤ Protect ∧
    ordinaryResourceRim Reference K ≤ Protect ∧
    (∀ v, Protect.degree v ≤ Inner.card + (ordinaryResourceRows K).card) := by
  intro Protect
  refine ⟨?_, le_sup_left, le_sup_right, ?_⟩
  · intro v w h
    rcases h with h | h
    · exact ((spanningRestriction_adj Reference Inner v w).mp h).1
    · exact h.1
  · intro v
    have hh := graph_degree_sup_le (spanningRestriction Reference Inner) (ordinaryResourceRim Reference K) v
    have hh' : Protect.degree v ≤ (spanningRestriction Reference Inner).degree v + (ordinaryResourceRim Reference K).degree v := by
      convert hh using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
    have hi := ordinary_spanning_restriction_degree_card Reference Inner v
    have hr := ordinary_reservoir_rim_degree_le_rows Reference K v
    omega
end Oberwolfach
