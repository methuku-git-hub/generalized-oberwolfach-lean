module

public import Oberwolfach.MarkedOutsideBalance

@[expose] public section

/-! The marked-spoke predicate may be replaced by its physically deleted
version on the exact surviving spoke set. Its truth value on every retained
pair is unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
  {tail head:E→V} {ktail khead:K→V} {HK HK':V→U→Prop} {m:ℕ}

theorem MarkedOutsideBalance.congr_spoke_types
    (A:Finset (E⊕K)) (S:Finset (V×U)) (X:Finset V) (Z:Finset U)
    (ht:∀ s∈S,HK s.1 s.2↔HK' s.1 s.2)
    (h:MarkedOutsideBalance tail head ktail khead HK A S m X Z):
    MarkedOutsideBalance tail head ktail khead HK' A S m X Z:=by
  have he (p:V×U→Prop) (b:Bool):
      S.filter (fun s=>p s∧(if b then HK s.1 s.2 else ¬HK s.1 s.2))=
      S.filter (fun s=>p s∧(if b then HK' s.1 s.2 else ¬HK' s.1 s.2)):=by
    ext s
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro hs
    rw [ht s hs]
  refine ⟨h.directed,h.row,?_,?_⟩
  · intro v hv
    have hh:=h.marked v hv
    have hp:=congrArg Finset.card (he (fun s=>s.1=v) true)
    simp only [ite_true,←Set.ncard_coe_finset,Finset.coe_filter] at hp hh ⊢
    exact hh.trans hp
  · intro u hu
    have hh:=h.hub u hu
    have hp:=congrArg Finset.card (he (fun s=>s.2=u) false)
    have hq:=congrArg (fun T:Finset (V×U)=>m*T.card) (he (fun s=>s.2=u) true)
    simp only [ite_true,Bool.false_eq_true,ite_false,←Set.ncard_coe_finset,Finset.coe_filter] at hp hq hh ⊢
    exact hp.symm.trans (hh.trans hq)

end Oberwolfach
