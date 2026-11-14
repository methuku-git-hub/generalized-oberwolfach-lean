module

public import Oberwolfach.SuccessorSequenceWeights
public import Oberwolfach.OrdinaryCycleWeightRestriction
public import Oberwolfach.MarkedCycleIncidence

@[expose] public section
/-! Restriction of a supported successor weighting to the marked tuple
index set preserves its positional sums. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem successor_weight_marked_cycle_any_position
    (P:SimpleGraph V) (π:Equiv.Perm V) (m b:ℕ) (D τ A B:ℝ)
    (w:(Fin (m+1)→V)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π b D τ A B w) (i:Fin (m+1)) (x:V):
    (1-τ)*D≤(∑ C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b,
      if C.val i=x then w C.val else 0) ∧
    (∑ C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b,
      if C.val i=x then w C.val else 0)≤D:=by
  let Q:=fun C:Fin (m+1)→V=>IsMarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b C
  let f:=fun C:Fin (m+1)→V=>if C i=x then w C else 0
  have hz:∀ C,¬Q C→f C=0:=by
    intro C hC
    by_cases h:w C=0
    · simp [f,h]
    · have hp:0<w C:=lt_of_le_of_ne (hw.nonneg C) (Ne.symm h)
      have hsep:PermutationSeparated π b C:=(hw.support C hp).2
      have hq:Q C:=by
        refine ⟨hsep,?_,?_⟩
        · intro i;exact ⟨(C i.castSucc,C i.succ),rfl,rfl⟩
        · exact ⟨(C (Fin.last m),C 0),rfl,rfl⟩
      exact (hC hq).elim
  have he:=finite_sum_restrict_of_zero Q f hz
  have he':(∑ C:Fin (m+1)→V,if C i=x then w C else 0)=
      ∑ C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b,
        if C.val i=x then w C.val else 0:=by
    calc
      _ = ∑ C,f C := by
        apply Finset.sum_congr rfl
        intro C _
        rfl
      _ = _ := by
        simpa only [Q,f] using he
  have he'':(∑ C:Fin (m+1)→V,@ite ℝ (C i=x) (Classical.propDecidable _) (w C) 0)=
      ∑ C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b,
        if C.val i=x then w C.val else 0:=by
    calc
      _ = (∑ C:Fin (m+1)→V,if C i=x then w C else 0) := by
        apply Finset.sum_congr rfl
        intro C _
        split_ifs <;> rfl
      _ = _ := he'
  have hh:=hw.positions i x
  constructor
  · exact hh.1.trans_eq he''
  · exact he''.symm.le.trans hh.2
end Oberwolfach
