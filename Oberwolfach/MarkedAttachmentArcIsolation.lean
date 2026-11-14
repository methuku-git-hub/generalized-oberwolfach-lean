module

public import Oberwolfach.MarkedRootArcIsolation

@[expose] public section

/-! A vertex wheel through two prescribed attachment vertices has no arc
joining two attachment vertices. The internal path vertices are fresh. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ} {H₀ HK:V→U→Prop}

 theorem one_root_raw_no_attachment_arc (n:ℕ) (p:Fin (n+3)→V)
    (v:V) (A:Finset V) (hv:v∉A)
    (hp:∀ i,p i∈A→i=0∨i=Fin.last (n+2)):
    ∀ i:Fin (n+4),¬(Fin.cons (α:=fun _=>V) v p i∈A∧
      Fin.cons (α:=fun _=>V) v p (finRotate (n+4) i)∈A):=by
  intro i hh
  revert hh
  refine Fin.cases ?_ (fun i=>?_) i
  · intro hh
    exact hv hh.1
  · intro hh
    have hpi:p i∈A:=hh.1
    rcases hp i hpi with hi|hi
    · subst i
      have hr:finRotate (n+4) (0:Fin (n+3)).succ=(0:Fin (n+2)).succ.succ:=by
        change finRotate (n+4) ((0:Fin (n+2)).succ.castSucc)=(0:Fin (n+2)).succ.succ
        exact finRotate_castSucc_eq_succ (n+3) _
      rw [hr] at hh
      have hh':p (0:Fin (n+2)).succ∈A:=hh.2
      rcases hp _ hh' with he|he
      · exact Fin.succ_ne_zero _ he
      · have he':=congrArg Fin.val he
        simp only [Fin.val_succ,Fin.val_zero,Fin.val_last] at he'
        omega
    · subst i
      have he:(Fin.last (n+2)).succ=Fin.last (n+3):=rfl
      rw [he,finRotate_last] at hh
      exact hv hh.2

 theorem marked_fixed_attachment_no_attachment_arc (n:ℕ) (p:Fin (n+3)↪V)
    (v:V) (j:Bool) (A:Finset V) (hv:v∉A)
    (hp:∀ i,p i∈A→p i∈({p 0,p (Fin.last (n+2))}:Finset V))
    (W:MarkedWheel tail head ktail khead (n+3) π b H₀ HK)
    (hW:∀ i,W.1.val i=rootedCycleOrder (markedRootOrder (n+3) j) v p i):
    ∀ i,¬(W.1.val i∈A∧W.1.val (finRotate (n+4) i)∈A):=by
  have hpi:∀ i,p i∈A→i=0∨i=Fin.last (n+2):=by
    intro i hi
    rcases Finset.mem_insert.mp (hp i hi) with he|he
    · exact Or.inl (p.injective he)
    · exact Or.inr (p.injective (Finset.mem_singleton.mp he))
  intro i hh
  apply one_root_raw_no_attachment_arc n p v A hv hpi (markedRootOrder (n+3) j i)
  simpa only [hW,rootedCycleOrder,markedRootOrder_successor,Fin.cons] using hh

end Oberwolfach
