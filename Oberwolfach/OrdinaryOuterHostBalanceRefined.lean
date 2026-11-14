module

public import Oberwolfach.OrdinaryDeletedHostBalanceRefined
public import Oberwolfach.OrdinaryOuterHostBalance

@[expose] public section
/-! Control the outer host using actual inner-pair balance, rather than its
size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_outer_host_balance_refined (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U)
    (b c:ℝ) (hfull:∀v,|(Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card|≤b)
    (hinner:∀v,|((spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤c):
    ∀v,|((Q\spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧¬(v∈I∧u∈J))).card|≤b+c:=by
  let K:=fun v u=>H v u∧v∈I∧u∈J
  have hRQ:spanningRestriction Q I≤Q:=by intro x y h;exact (spanningRestriction_adj Q I x y).mp h |>.1
  have hKH:∀v u,K v u→H v u:=by intro v u h;exact h.1
  have hinner':∀v,|((spanningRestriction Q I).degree v:ℝ)-2*(Finset.univ.filter (K v)).card|≤c:=hinner
  have ht:=ordinary_deleted_host_balance_refined Q (spanningRestriction Q I) H K b c hRQ hKH hfull (by intro v;convert hinner' v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  intro v
  have he:(Finset.univ.filter (fun u=>H v u∧¬K v u))=
      Finset.univ.filter (fun u=>H v u∧¬(v∈I∧u∈J)):=by
    ext u;simp only [Finset.mem_filter,Finset.mem_univ,true_and,K];tauto
  have hh:|((Q\spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧¬K v u)).card|≤b+c:=by
    convert ht v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  rw [he] at hh
  exact hh
end Oberwolfach
