module

public import Oberwolfach.BipartiteDeletionEstimates
public import Oberwolfach.CommonMarkedCycleConstraintCounts

@[expose] public section

/-! A two-edge directed walk loses an intermediate vertex only through
its first outgoing edge or its second incoming edge. The endpoints and
intermediate-vertex domain are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V]

theorem directed_two_step_deletion (R R' : V → V → Prop)
    (hsub : ∀ x y,R' x y → R x y) (x y : V) (d : ℝ)
    (hout : (∑ z,bipAdj (fun x z=>R x z ∧ ¬R' x z) x z)≤d)
    (hin : (∑ z,bipAdj (fun z y=>R z y ∧ ¬R' z y) z y)≤d) :
    |((Finset.univ.filter (fun z=>R' x z ∧ R' z y)).card:ℝ)-
      (Finset.univ.filter (fun z=>R x z ∧ R z y)).card|≤2*d := by
  have he (T : V → V → Prop) : ((Finset.univ.filter (fun z=>T x z ∧ T z y)).card:ℝ)=
      ∑ z,bipAdj T x z*bipAdj T z y := by
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro z _
    by_cases h1 : T x z <;> by_cases h2 : T z y <;> simp [bipAdj,h1,h2]
  rw [he R,he R']
  have hp (z : V) := unit_product_deletion
    (bipAdj_nonneg R' x z) (bipAdj_subrelation R R' hsub x z) (bipAdj_le_one R x z)
    (bipAdj_nonneg R' z y) (bipAdj_subrelation R R' hsub z y) (bipAdj_le_one R z y)
  have hn : 0≤(∑ z,bipAdj R x z*bipAdj R z y)-(∑ z,bipAdj R' x z*bipAdj R' z y) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg (fun z _=>(hp z).1)
  rw [abs_sub_comm,abs_of_nonneg hn,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ z,((bipAdj R x z-bipAdj R' x z)+(bipAdj R z y-bipAdj R' z y)) :=
      Finset.sum_le_sum (fun z _=>(hp z).2)
    _ ≤ 2*d := by
      simp only [bipAdj_deletion R R' hsub,Finset.sum_add_distrib]
      linarith only [hout,hin]

theorem represented_two_step_deletion [Fintype E] (tail head : E → V) (keep : E → Prop)
    (x y : V) (d : ℝ)
    (hout : (∑ e,if ¬keep e ∧ tail e=x then (1:ℝ) else 0)≤d)
    (hin : (∑ e,if ¬keep e ∧ head e=y then (1:ℝ) else 0)≤d) :
    |((Finset.univ.filter (fun z=>
        (∃ e : {e // keep e},tail e.val=x ∧ head e.val=z) ∧
        (∃ e : {e // keep e},tail e.val=z ∧ head e.val=y))).card:ℝ)-
      (Finset.univ.filter (fun z=>(∃ e,tail e=x ∧ head e=z) ∧ (∃ e,tail e=z ∧ head e=y))).card|≤2*d := by
  have hrow : (∑ z,bipAdj (fun x z=>(∃ e,tail e=x ∧ head e=z) ∧
      ¬(∃ e : {e // keep e},tail e.val=x ∧ head e.val=z)) x z)≤d := by
    convert (represented_relation_lost_outdegree tail head keep x).trans
      (by convert hout using 1 <;> congr!) using 1 <;> congr!
  have hcol : (∑ z,bipAdj (fun z y=>(∃ e,tail e=z ∧ head e=y) ∧
      ¬(∃ e : {e // keep e},tail e.val=z ∧ head e.val=y)) z y)≤d := by
    convert (represented_relation_lost_indegree tail head keep y).trans
      (by convert hin using 1 <;> congr!) using 1 <;> congr!
  have hh := directed_two_step_deletion
    (fun x y=>∃ e,tail e=x ∧ head e=y)
    (fun x y=>∃ e : {e // keep e},tail e.val=x ∧ head e.val=y)
    (by rintro a b ⟨e,he⟩;exact ⟨e.val,he⟩) x y d hrow hcol
  convert hh using 1 <;> congr!

end Oberwolfach
