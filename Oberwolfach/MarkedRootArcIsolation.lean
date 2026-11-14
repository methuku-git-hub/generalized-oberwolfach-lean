module

public import Oberwolfach.MarkedWheelRawCoordinates
public import Oberwolfach.MarkedRootOrder

@[expose] public section

/-! A rim-wheel cycle has exactly one possible arc with two old row
endpoints; a spoke-wheel cycle has none. These are statements about the
auxiliary endpoints, followed by the original physical representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ} {H₀ HK:V→U→Prop}

 theorem two_root_raw_old_arc {n:ℕ} (p:Fin (n+1)→V) (v w:V) (R:Finset V)
    (hp:∀ i,p i∉R) (i:Fin (n+3))
    (ht:Fin.cons (α:=fun _=>V) v (Fin.cons w p) i∈R)
    (hh:Fin.cons (α:=fun _=>V) v (Fin.cons w p) (finRotate (n+3) i)∈R):i=0:=by
  revert ht hh
  refine Fin.cases ?_ (fun i=>?_) i
  · intros; rfl
  · refine Fin.cases ?_ (fun i=>?_) i
    · intro ht hh
      have hr:finRotate (n+3) (0:Fin (n+2)).succ=(0:Fin (n+1)).succ.succ:=by
        change finRotate (n+3) ((0:Fin (n+1)).succ.castSucc)=(0:Fin (n+1)).succ.succ
        exact finRotate_castSucc_eq_succ (n+2) _
      rw [hr] at hh
      exact (hp 0 hh).elim
    · intro ht hh
      exact (hp i ht).elim

 theorem one_root_raw_no_old_arc {n:ℕ} (p:Fin (n+1)→V) (v:V) (R:Finset V)
    (hp:∀ i,p i∉R) (i:Fin (n+2)):
    ¬(Fin.cons (α:=fun _=>V) v p i∈R∧Fin.cons (α:=fun _=>V) v p (finRotate (n+2) i)∈R):=by
  refine Fin.cases ?_ (fun i=>?_) i
  · intro hh
    have hr:finRotate (n+2) (0:Fin (n+2))=(0:Fin (n+1)).succ:=finRotate_castSucc_eq_succ (n+1) 0
    exact hp 0 (by simpa only [hr,Fin.cons_succ] using hh.2)
  · intro hh
    exact hp i hh.1

 theorem marked_two_root_wheel_old_arc (n:ℕ) (hn:2≤n) (p:Fin (n+1)→V)
    (v w:V) (j:Bool) (R:Finset V) (hp:∀ i,p i∉R)
    (W:MarkedWheel tail head ktail khead (n+2) π b H₀ HK)
    (hW:∀ a,W.1.val a=Fin.cons (α:=fun _=>V) v (Fin.cons w p)
      (canonicalMarkedRotation (if j then 0 else 3) a))
    (a:Fin (n+3)) (ht:W.1.val a∈R) (hh:W.1.val (finRotate (n+3) a)∈R):
    markedPhysicalEdge tail head ktail khead π (markedCycleTypedEdge tail head ktail khead (n+2) π b W.1 a)=
      (if j then {v,π w} else {v,w}):=by
  let k:Fin (n+3):=if j then 0 else 3
  let ρ:=canonicalMarkedRotation k
  have hpos:ρ a=0:=by
    apply two_root_raw_old_arc p v w R hp (ρ a)
    · simpa only [hW] using ht
    · simpa only [hW,canonicalMarkedRotation_rotate] using hh
  have ha:a=ρ.symm 0:=by rw [← hpos,Equiv.symm_apply_apply]
  have hr:=marked_wheel_raw_rim_position W (Fin.cons v (Fin.cons w p)) k hW 0
  have hr0:finRotate (n+3) (0:Fin (n+3))=(0:Fin (n+2)).succ:=finRotate_castSucc_eq_succ (n+2) 0
  have h03:(0:Fin (n+3))≠3:=by
    intro he
    have hh:=congrArg Fin.val he
    change 0=3%(n+3) at hh
    rw [Nat.mod_eq_of_lt (by omega)] at hh
    omega
  apply Sum.inl_injective (β:=V×U)
  change markedWheelPositionResource W (Sum.inl a)=Sum.inl _
  rw [ha,hr]
  simp only [markedRawRimResource,k,hr0,Fin.cons_succ,Fin.cons_zero]
  cases j <;> simp only [Bool.false_eq_true,ite_false,ite_true,h03]

 theorem marked_one_root_wheel_no_old_arc {n:ℕ} (p:Fin (n+1)→V) (v:V) (R:Finset V)
    (hp:∀ i,p i∉R) (σ:Equiv.Perm (Fin (n+2)))
    (hσ:∀ i,σ (finRotate (n+2) i)=finRotate (n+2) (σ i))
    (W:MarkedWheel tail head ktail khead (n+1) π b H₀ HK)
    (hW:∀ a,W.1.val a=rootedCycleOrder σ v p a):
    ∀ a,¬(W.1.val a∈R∧W.1.val (finRotate (n+2) a)∈R):=by
  intro a h
  apply one_root_raw_no_old_arc p v R hp (σ a)
  simpa only [hW,rootedCycleOrder,hσ,Fin.cons] using h

end Oberwolfach
