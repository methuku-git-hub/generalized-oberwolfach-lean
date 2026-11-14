module

public import Oberwolfach.MarkedTwoRootPathCycles

@[expose] public section

/-! A fixed hub is attached to a cycle containing a prescribed rim arc.
The marked root arc has its marked spoke at its head; otherwise the unique
marked head is the specified internal path vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_wheel_from_two_root_path {V U E K:Type*}
    (tail head:E→V) (ktail khead:K→V) (n:ℕ) (hn:2≤n)
    (π:Equiv.Perm V) (b:ℕ) (H₀ HK:V→U→Prop) (j:Bool) (v w:V) (u:U) (p:Fin (n+1)→V)
    (hsep:PermutationSeparated π b (Fin.cons v (Fin.cons w p)))
    (hroot:if j then ∃ e,ktail e=v∧khead e=w else ∃ e,tail e=v∧head e=w)
    (hopen:∃ e,tail e=w∧head e=p 0)
    (hclose:∃ e,tail e=p (Fin.last n)∧head e=v)
    (hpath:∀ i:Fin n,if j=false∧i.val=1 then
      ∃ e,ktail e=p i.castSucc∧khead e=p i.succ else ∃ e,tail e=p i.castSucc∧head e=p i.succ)
    (hv:H₀ v u) (hw:if j then HK w u else H₀ w u)
    (hfree:∀ i,if j=false∧i.val=2 then HK (p i) u else H₀ (p i) u):
    ∃ C:MarkedWheel tail head ktail khead (n+2) π b H₀ HK,
      C.2.val=u∧∀ i,C.1.val i=Fin.cons (α:=fun _=>V) v (Fin.cons w p) (canonicalMarkedRotation (if j then 0 else 3) i):=by
  let z:Fin (n+3)↪V:=⟨Fin.cons v (Fin.cons w p),permutationSeparated_injective π b _ hsep⟩
  let k:Fin (n+3):=if j then 0 else 3
  have hcyc:=root_first_marked_two_root_cycle tail head ktail khead n hn π b j v w p hsep hroot hopen hclose hpath
  have hhead:finRotate (n+3) k=(if j then (1:Fin (n+3)) else 4):=by
    cases j
    · change finRotate (n+3) (3:Fin (n+3))=4
      have h3:((3:Fin (n+3)):ℕ)=3:=by change 3%(n+3)=3;exact Nat.mod_eq_of_lt (by omega)
      apply Fin.ext
      simp only [finRotate_apply,Fin.val_add,Fin.val_one,h3]
      change 4%(n+3)=4%(n+3)
      rfl
    · change finRotate (n+3) (0:Fin (n+3))=1
      simp [finRotate_apply]
  have hsp (i:Fin (n+3)):if i=finRotate (n+3) k then HK (z i) u else H₀ (z i) u:=by
    rw [hhead]
    have h1:((1:Fin (n+3)):ℕ)=1:=by change 1%(n+3)=1;exact Nat.mod_eq_of_lt (by omega)
    have h4:((4:Fin (n+3)):ℕ)=4:=by change 4%(n+3)=4;exact Nat.mod_eq_of_lt (by omega)
    refine Fin.cases ?_ (fun i=>?_) i
    · have hne:(0:Fin (n+3))≠(if j then 1 else 4):=by
        cases j <;> intro h <;> have hh:=congrArg Fin.val h <;> simp only [Bool.false_eq_true,ite_false,ite_true,Fin.val_zero,h1,h4] at hh <;> omega
      rw [if_neg hne];exact hv
    · refine Fin.cases ?_ (fun i=>?_) i
      · have he:(0:Fin (n+2)).succ=(1:Fin (n+3)):=rfl
        have hz1:z (1:Fin (n+3))=w:=he ▸ (show z (0:Fin (n+2)).succ=w from rfl)
        have hne:(1:Fin (n+3))≠4:=by intro h;have hh:=congrArg Fin.val h;rw [h1,h4] at hh;omega
        cases j
        · simpa only [Bool.false_eq_true,ite_false,he,if_neg hne,hz1,z,Function.Embedding.coeFn_mk,Fin.cons_succ,Fin.cons_zero] using hw
        · simpa only [ite_true,he,ite_true,hz1,z,Function.Embedding.coeFn_mk,Fin.cons_succ,Fin.cons_zero] using hw
      · have he:i.succ.succ=(4:Fin (n+3))↔i.val=2:=by
          simp only [Fin.ext_iff,Fin.val_succ,h4];omega
        have hne:i.succ.succ≠(1:Fin (n+3)):=by
          intro h;have hh:=congrArg Fin.val h;simp only [Fin.val_succ,h1] at hh;omega
        cases j
        · simpa only [Bool.false_eq_true,ite_false,true_and,he,z,Function.Embedding.coeFn_mk,Fin.cons_succ] using hfree i
        · simpa only [ite_true,if_neg hne,Bool.true_eq_false,false_and,ite_false,z,Function.Embedding.coeFn_mk,Fin.cons_succ] using hfree i
  obtain ⟨C,hCu,hC⟩:=marked_wheel_from_cyclic_embedding tail head ktail khead (n+2) π b H₀ HK z k u hsep
    (fun i hi=>by have h:=hcyc.2 i;rw [if_neg hi] at h;exact h)
    (by have h:=hcyc.2 k;rw [if_pos rfl] at h;exact h)
    (by have h:=hsp (finRotate (n+3) k);rw [if_pos rfl] at h;exact h)
    (fun i hi=>by have h:=hsp i;rw [if_neg hi] at h;exact h)
  exact ⟨C,hCu,hC⟩
end Oberwolfach
