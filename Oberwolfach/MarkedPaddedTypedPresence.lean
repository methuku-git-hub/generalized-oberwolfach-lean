module

public import Oberwolfach.MarkedPaddedMapCompatibility

@[expose] public section

/-! Typed presence of the augmented occurrences follows directly from
the actual wheels. No new arc or spoke existence is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S I:Type} [Fintype A] [Fintype S] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq I]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_cycle_canonical_typed_presence
    (C:MarkedCycleTuple tail head ktail khead m π b) (k:Fin (m+1)):
    if k=Fin.last m then ∃ e,ktail e=C.val k∧khead e=C.val (finRotate (m+1) k)
    else ∃ e,tail e=C.val k∧head e=C.val (finRotate (m+1) k):=by
  refine Fin.lastCases ?_ (fun q=>?_) k
  · simpa only [ite_true,finRotate_last] using C.property.2.2
  · simpa only [Fin.castSucc_ne_last,ite_false,finRotate_castSucc_eq_succ] using C.property.2.1 q

theorem marked_wheel_canonical_spoke_presence
    (C:MarkedWheel tail head ktail khead m π b H₀ HK) (k:Fin (m+1)):
    if k=0 then HK (C.1.val k) C.2.val else H₀ (C.1.val k) C.2.val:=by
  refine Fin.cases ?_ (fun q=>?_) k
  · exact C.2.property.1
  · simpa only [Fin.succ_ne_zero,ite_false] using C.2.property.2 q

theorem padded_typed_presence (src dst:A→V) (row:S→V) (jr:A→Bool) (js:S→Bool) (u:S→U)
    (C:I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (hr:∀ a,if jr a then ∃ e,ktail e=src a∧khead e=dst a else ∃ e,tail e=src a∧head e=dst a)
    (hs:∀ s,if js s then HK (row s) (u s) else H₀ (row s) (u s)):
    (∀ a,if paddingRimType jr m a then
      ∃ e,ktail e=paddingRimTail src (fun i=>(C i).1.val) a∧khead e=paddingRimHead dst (fun i=>(C i).1.val) a
      else ∃ e,tail e=paddingRimTail src (fun i=>(C i).1.val) a∧head e=paddingRimHead dst (fun i=>(C i).1.val) a)∧
    ∀ s,if paddingSpokeType js m s then
      HK (paddingSpokeRow row (fun i=>(C i).1.val) s) (actualPaddingSpokeHub u (fun i=>(C i).2.val) s)
      else H₀ (paddingSpokeRow row (fun i=>(C i).1.val) s) (actualPaddingSpokeHub u (fun i=>(C i).2.val) s):=by
  constructor
  · rintro (a|⟨i,k⟩)
    · exact hr a
    · simpa only [paddingRimType,paddingRimTail,paddingRimHead,Sum.elim_inr,decide_eq_true_eq] using
        marked_cycle_canonical_typed_presence (C i).1 k
  · rintro (s|⟨i,k⟩)
    · exact hs s
    · simpa only [paddingSpokeType,paddingSpokeRow,actualPaddingSpokeHub,Sum.elim_inr,decide_eq_true_eq] using
        marked_wheel_canonical_spoke_presence (C i) k

end Oberwolfach
