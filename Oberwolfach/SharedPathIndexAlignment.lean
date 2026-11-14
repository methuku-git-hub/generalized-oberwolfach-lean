module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Two paths with the same free labels and disjoint old roots can share
a vertex only at the same position. This is the exact condition needed to
prevent contradictory spoke types in the paired marked wheels. -/
set_option autoImplicit false
namespace Oberwolfach

 theorem shared_two_root_path_index_alignment {V:Type} {n:ℕ}
    (p:Fin n→V) (hp:Function.Injective p) (v w v' w':V)
    (hcross:v≠v'∧v≠w'∧w≠v'∧w≠w')
    (hfree:∀ i,p i≠v∧p i≠w∧p i≠v'∧p i≠w'):
    ∀ i j:Fin (n+2),
      Fin.cons (α:=fun _=>V) v (Fin.cons w p) i=
        Fin.cons (α:=fun _=>V) v' (Fin.cons w' p) j→i=j:=by
  intro i
  refine Fin.cases ?_ (fun i=>?_) i
  · intro j
    refine Fin.cases ?_ (fun j=>?_) j
    · intro h;exact (hcross.1 h).elim
    · refine Fin.cases ?_ (fun j=>?_) j
      · intro h;exact (hcross.2.1 h).elim
      · intro h;exact ((hfree j).1 h.symm).elim
  · refine Fin.cases ?_ (fun i=>?_) i
    · intro j
      refine Fin.cases ?_ (fun j=>?_) j
      · intro h;exact (hcross.2.2.1 h).elim
      · refine Fin.cases ?_ (fun j=>?_) j
        · intro h;exact (hcross.2.2.2 h).elim
        · intro h;exact ((hfree j).2.1 h.symm).elim
    · intro j
      refine Fin.cases ?_ (fun j=>?_) j
      · intro h;exact ((hfree i).2.2.1 h).elim
      · refine Fin.cases ?_ (fun j=>?_) j
        · intro h;exact ((hfree i).2.2.2 h).elim
        · intro h;exact congrArg (fun k:Fin n=>k.succ.succ) (hp h)

end Oberwolfach
