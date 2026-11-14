module

public import Oberwolfach.MarkedPaddedTypedPresence

@[expose] public section

/-! Adjacent positions in a canonical padding cycle are distinct and
separated in the host permutation metric. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E K A I:Type} [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ}

theorem finRotate_ne_self_of_pos (hm:0<m) (k:Fin (m+1)):k≠finRotate (m+1) k:=by
  refine Fin.lastCases ?_ (fun q=>?_) k
  · rw [finRotate_last]
    intro he
    have hv:=congrArg Fin.val he
    simp only [Fin.val_last,Fin.val_zero] at hv
    omega
  · rw [finRotate_castSucc_eq_succ]
    intro he
    have hv:=congrArg Fin.val he
    simp only [Fin.val_castSucc,Fin.val_succ] at hv
    omega

theorem marked_cycle_adjacent_separated (hm:0<m)
    (C:MarkedCycleTuple tail head ktail khead m π b) (k:Fin (m+1)):
    ¬PermutationClose π b (C.val k) (C.val (finRotate (m+1) k)):=
  C.property.1 k (finRotate (m+1) k) (finRotate_ne_self_of_pos hm k)

theorem padded_arcs_separated (src dst:A→V) (hm:0<m)
    (C:I→MarkedCycleTuple tail head ktail khead m π b)
    (hsep:∀ a,¬PermutationClose π b (src a) (dst a)):
    ∀ a,¬PermutationClose π b (paddingRimTail src (fun i=>(C i).val) a)
      (paddingRimHead dst (fun i=>(C i).val) a):=by
  rintro (a|⟨i,k⟩)
  · exact hsep a
  · exact marked_cycle_adjacent_separated hm (C i) k

end Oberwolfach
