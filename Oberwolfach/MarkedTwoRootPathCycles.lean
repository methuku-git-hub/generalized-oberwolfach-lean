module

public import Oberwolfach.MarkedCycleRotation
public import Oberwolfach.RootFirstMarkedCycles

@[expose] public section

/-! Close a shared directed path using the actual old rim arc. If that arc
is ordinary, the unique marked arc lies inside the path; if it is marked,
all path and attachment arcs are ordinary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem root_first_marked_two_root_cycle {V E K:Type*}
    (tail head:E→V) (ktail khead:K→V) (n:ℕ) (hn:2≤n)
    (π:Equiv.Perm V) (b:ℕ) (j:Bool) (v w:V) (p:Fin (n+1)→V)
    (hsep:PermutationSeparated π b (Fin.cons v (Fin.cons w p)))
    (hroot:if j then ∃ e,ktail e=v∧khead e=w else ∃ e,tail e=v∧head e=w)
    (hopen:∃ e,tail e=w∧head e=p 0)
    (hclose:∃ e,tail e=p (Fin.last n)∧head e=v)
    (hpath:∀ i:Fin n,if j=false∧i.val=1 then
      ∃ e,ktail e=p i.castSucc∧khead e=p i.succ
      else ∃ e,tail e=p i.castSucc∧head e=p i.succ):
    IsRootFirstMarkedCycle tail head ktail khead (n+2) π b
      (if j then 0 else 3) (Fin.cons v (Fin.cons w p)):=by
  have h3:((3:Fin (n+3)):ℕ)=3:=by change 3%(n+3)=3;exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hsep,?_⟩
  intro t
  refine Fin.cases ?_ (fun i=>?_) t
  · have hrot:finRotate (n+3) (0:Fin (n+3))=(0:Fin (n+2)).succ:=finRotate_castSucc_eq_succ (n+2) 0
    rw [hrot]
    have hne:(0:Fin (n+3))≠3:=by intro h;have hh:=congrArg Fin.val h;simp only [Fin.val_zero,h3] at hh;omega
    cases j
    · simpa only [Bool.false_eq_true,ite_false,hne,Fin.cons_zero,Fin.cons_succ] using hroot
    · simpa only [ite_true,Fin.cons_zero,Fin.cons_succ] using hroot
  · refine Fin.cases ?_ (fun i=>?_) i
    · have hrot:finRotate (n+3) (0:Fin (n+2)).succ=(0:Fin (n+1)).succ.succ:=by
        change finRotate (n+3) ((0:Fin (n+1)).succ.castSucc)=(0:Fin (n+1)).succ.succ
        exact finRotate_castSucc_eq_succ _ _
      rw [hrot]
      have hne:(0:Fin (n+2)).succ≠(if j then (0:Fin (n+3)) else 3):=by
        cases j
        · intro h;have hh:=congrArg Fin.val h;simp only [Bool.false_eq_true,ite_false,Fin.val_succ,Fin.val_zero,h3] at hh;omega
        · exact Fin.succ_ne_zero _
      rw [ite_eq_right hne]
      exact hopen
    · refine Fin.lastCases ?_ (fun k=>?_) i
      · have he:(Fin.last n).succ.succ=Fin.last (n+2):=rfl
        rw [he,finRotate_last]
        have hne:(Fin.last (n+2):Fin (n+3))≠(if j then 0 else 3):=by
          cases j
          · intro h;have hh:=congrArg Fin.val h;simp only [Bool.false_eq_true,ite_false,Fin.val_last,h3] at hh;omega
          · intro h;have hh:=congrArg Fin.val h;simp only [ite_true,Fin.val_last,Fin.val_zero] at hh;omega
        rw [ite_eq_right hne]
        exact hclose
      · have hcast:k.castSucc.succ.succ=k.succ.succ.castSucc:=rfl
        rw [hcast,finRotate_castSucc_eq_succ]
        have hval:Fin.cons (α:=fun _=>V) v (Fin.cons w p) k.succ.succ.castSucc=p k.castSucc:=by
          rw [← hcast,Fin.cons_succ,Fin.cons_succ]
        have heq:k.succ.succ.castSucc=(3:Fin (n+3))↔k.val=1:=by
          simp only [Fin.ext_iff,Fin.val_castSucc,Fin.val_succ,h3]
          omega
        have hne:k.succ.succ.castSucc≠(0:Fin (n+3)):=by
          intro h;have hh:=congrArg Fin.val h;simp only [Fin.val_castSucc,Fin.val_succ,Fin.val_zero] at hh;omega
        cases j
        · simpa only [Bool.false_eq_true,ite_false,heq,true_and,hval,Fin.cons_succ] using hpath k
        · simpa only [ite_true,ite_eq_right hne,Bool.true_eq_false,false_and,ite_false,hval,Fin.cons_succ] using hpath k

 theorem marked_cycle_from_two_root_path {V E K:Type*}
    (tail head:E→V) (ktail khead:K→V) (n:ℕ) (hn:2≤n)
    (π:Equiv.Perm V) (b:ℕ) (j:Bool) (v w:V) (p:Fin (n+1)→V)
    (hsep:PermutationSeparated π b (Fin.cons v (Fin.cons w p)))
    (hroot:if j then ∃ e,ktail e=v∧khead e=w else ∃ e,tail e=v∧head e=w)
    (hopen:∃ e,tail e=w∧head e=p 0)
    (hclose:∃ e,tail e=p (Fin.last n)∧head e=v)
    (hpath:∀ i:Fin n,if j=false∧i.val=1 then
      ∃ e,ktail e=p i.castSucc∧khead e=p i.succ
      else ∃ e,tail e=p i.castSucc∧head e=p i.succ):
    ∃ C:MarkedCycleTuple tail head ktail khead (n+2) π b,
      ∀ i,C.val i=Fin.cons (α:=fun _=>V) v (Fin.cons w p) (canonicalMarkedRotation (if j then 0 else 3) i):=by
  have hc:=root_first_marked_two_root_cycle tail head ktail khead n hn π b j v w p hsep hroot hopen hclose hpath
  let k:Fin (n+3):=if j then 0 else 3
  have hcan: IsMarkedCycleTuple tail head ktail khead (n+2) π b
      (fun i=>Fin.cons (α:=fun _=>V) v (Fin.cons w p) (canonicalMarkedRotation k i)):=by
    apply (markedCycle_reindex_iff (canonicalMarkedRotation k) (canonicalMarkedRotation_rotate k) _).mpr
    simpa only [canonicalMarkedRotation_last,k] using hc
  exact ⟨⟨_,hcan⟩,fun _=>rfl⟩

end Oberwolfach
