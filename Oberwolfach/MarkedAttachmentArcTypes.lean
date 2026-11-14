module

public import Oberwolfach.MarkedActualAttachments
public import Oberwolfach.MarkedTwoRootPathCycles
public import Oberwolfach.MarkedRootedPathCycles

@[expose] public section

/-! Read the attachment arcs from the already constructed cycles. The
incoming vertex attachment has the type assigned by the spoke bijection;
the outgoing incidence closes by an ordinary arc. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E K:Type} {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ}

theorem marked_rim_path_attachment_arcs (n:ℕ) (hn:2≤n)
    (C:MarkedCycleTuple tail head ktail khead (n+2) π b)
    (v w:V) (p:Fin (n+1)→V) (j:Bool)
    (hC:∀ i,C.val i=Fin.cons (α:=fun _=>V) v (Fin.cons w p) (canonicalMarkedRotation (if j then 0 else 3) i)):
    (∃ e,tail e=w∧head e=p 0)∧(∃ e,tail e=p (Fin.last n)∧head e=v):=by
  have hc:IsMarkedCycleTuple tail head ktail khead (n+2) π b
      (fun i=>Fin.cons (α:=fun _=>V) v (Fin.cons w p) (canonicalMarkedRotation (if j then 0 else 3) i)):=by
    simpa only [←funext hC] using C.property
  have hr:=(markedCycle_reindex_iff (canonicalMarkedRotation (if j then (0:Fin (n+3)) else 3))
    (canonicalMarkedRotation_rotate _) (Fin.cons (α:=fun _=>V) v (Fin.cons w p))).mp hc
  rw [canonicalMarkedRotation_last] at hr
  have h3:((3:Fin (n+3)):ℕ)=3:=by change 3%(n+3)=3;exact Nat.mod_eq_of_lt (by omega)
  have h1:(0:Fin (n+2)).succ≠(if j then (0:Fin (n+3)) else 3):=by
    cases j <;> intro he <;> have he':=congrArg Fin.val he
    · simp only [Bool.false_eq_true,ite_false,Fin.val_succ,Fin.val_zero,h3] at he';omega
    · simp only [ite_true,Fin.val_succ,Fin.val_zero] at he';omega
  have hl:(Fin.last (n+2):Fin (n+3))≠(if j then 0 else 3):=by
    cases j <;> intro he <;> have he':=congrArg Fin.val he
    · simp only [Bool.false_eq_true,ite_false,Fin.val_last,h3] at he';omega
    · simp only [ite_true,Fin.val_last,Fin.val_zero] at he';omega
  have ho:=hr.2 (0:Fin (n+2)).succ
  have he:finRotate (n+3) (0:Fin (n+2)).succ=(0:Fin (n+1)).succ.succ:=by
    exact finRotate_castSucc_eq_succ _ (0:Fin (n+1)).succ
  rw [if_neg h1,he] at ho
  have hh:=hr.2 (Fin.last (n+2))
  rw [if_neg hl,finRotate_last] at hh
  exact ⟨ho,hh⟩

theorem marked_spoke_path_attachment_arcs (n:ℕ) (hn:2≤n)
    (C:MarkedCycleTuple tail head ktail khead (n+2) π b)
    (v:V) (p:Fin (n+2)→V) (j:Bool)
    (hC:∀ i,C.val i=rootedCycleOrder (markedRootOrder (n+2) j) v p i):
    (∃ e,tail e=v∧head e=p 0)∧
      (if j then ∃ e,ktail e=p (Fin.last (n+1))∧khead e=v
        else ∃ e,tail e=p (Fin.last (n+1))∧head e=v):=by
  have hc:IsMarkedCycleTuple tail head ktail khead (n+2) π b
      (rootedCycleOrder (markedRootOrder (n+2) j) v p):=by
    simpa only [←funext hC] using C.property
  have hr:=(rootedCycleOrder_marked_iff j v p).mp hc
  have h2:((2:Fin (n+3)):ℕ)=2:=by change 2%(n+3)=2;exact Nat.mod_eq_of_lt (by omega)
  have hz:(0:Fin (n+3))≠(if j then Fin.last (n+2) else 2):=by
    cases j <;> intro he <;> have he':=congrArg Fin.val he
    · simp only [Bool.false_eq_true,ite_false,Fin.val_zero,h2] at he';omega
    · simp only [ite_true,Fin.val_last,Fin.val_zero] at he';omega
  have ho:=hr.2 0
  have hrot:finRotate (n+3) (0:Fin (n+3))=(0:Fin (n+2)).succ:=finRotate_castSucc_eq_succ (n+2) 0
  rw [if_neg hz,hrot] at ho
  have hh:=hr.2 (Fin.last (n+2))
  rw [finRotate_last] at hh
  have hl:(Fin.last (n+2):Fin (n+3))≠2:=by
    intro he;have he':=congrArg Fin.val he
    simp only [Fin.val_last,h2] at he';omega
  have hlast:(Fin.last (n+2):Fin (n+3))=(Fin.last (n+1)).succ:=rfl
  refine ⟨ho,?_⟩
  cases j
  · simp only [Bool.false_eq_true,ite_false] at hh
    rw [if_neg hl] at hh
    simpa only [Bool.false_eq_true,ite_false,hlast,Fin.cases_succ,Fin.cases_zero] using hh
  · simpa only [ite_true,if_pos rfl,hlast,Fin.cases_succ,Fin.cases_zero] using hh

variable {A S:Type} [Fintype A] [Fintype S] [DecidableEq V] [DecidableEq A] [DecidableEq S]

theorem marked_actual_attachment_arcs (n:ℕ) (hn:2≤n) (src dst:A→V) (row:S→V)
    (a:∀ v,{e:A // dst e=v}≃{s:S // row s=v})
    (d:∀ v,{e:A // src e=v}≃{s:S // row s=v})
    (f:V→V) (jr:A→Bool) (js:S→Bool) (pr:A→Fin (n+1)→V) (ps:S→Fin (n+2)→V)
    (C:A→MarkedCycleTuple tail head ktail khead (n+2) π b)
    (D:S→MarkedCycleTuple tail head ktail khead (n+2) π b)
    (hC:∀ e i,(C e).val i=Fin.cons (α:=fun _=>V) (f (src e)) (Fin.cons (f (dst e)) (pr e))
      (canonicalMarkedRotation (if jr e then 0 else 3) i))
    (hD:∀ e i,(D e).val i=rootedCycleOrder (markedRootOrder (n+2) (js e)) (f (row e)) (ps e) i)
    (jv:(Σ v,DirectedIncidence src dst v)→Bool)
    (hjin:∀ v e,jv ⟨v,Sum.inl e⟩=js (a v e).val)
    (hjout:∀ v e,jv ⟨v,Sum.inr e⟩=false):
    ∀ z:Σ v,DirectedIncidence src dst v,
      (∃ e,tail e=f z.1∧head e=markedAttachmentFirst n a d pr ps z)∧
      (if jv z then ∃ e,ktail e=markedAttachmentLast n a d pr ps z∧khead e=f z.1
        else ∃ e,tail e=markedAttachmentLast n a d pr ps z∧head e=f z.1):=by
  rintro ⟨v,z⟩
  cases z with
  | inl z=>
    have hr:=marked_rim_path_attachment_arcs n hn (C z.val) _ _ _ _ (hC z.val)
    have hs:=marked_spoke_path_attachment_arcs n hn (D (a v z).val) _ _ _ (hD (a v z).val)
    constructor
    · simpa only [markedAttachmentFirst,z.property] using hr.1
    · simpa only [hjin,markedAttachmentLast,(a v z).property] using hs.2
  | inr z=>
    have hr:=marked_rim_path_attachment_arcs n hn (C z.val) _ _ _ _ (hC z.val)
    have hs:=marked_spoke_path_attachment_arcs n hn (D (d v z).val) _ _ _ (hD (d v z).val)
    constructor
    · simpa only [markedAttachmentFirst,(d v z).property] using hs.1
    · simpa only [hjout,markedAttachmentLast,z.property,Bool.false_eq_true,ite_false] using hr.2

end Oberwolfach
