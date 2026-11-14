module

public import Oberwolfach.MarkedEndpointColumnEstimates
public import Oberwolfach.HubNeighbourClasses

@[expose] public section

/-! Hub class cardinalities are the empty-rim, one-spoke instances of the
original row profiles. They are measured on the fixed vertex domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_single_hub_class_estimate
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (hh:1≤h) (A:Finset V)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (err:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A p k q s g j err σ H)
    (b:Bool) (u:U):
    |((A.filter (H b · u)).card:ℝ)-(if b then q u g else s u j)*A.card|<err:=by
  have he:=hr ∅ ∅ {(b,u)} (by simp) (by simp) (by simpa using hh)
    (by intro a ha c hc he;simpa using (Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hc).symm)
  simpa [markedRowCountWithSpokes,markedRowDomain,Finset.card_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,-Finset.sum_boole] using he

theorem marked_sample_hub_class_lower
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (hh:1≤h)
    (p k t eps:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (hq:∀ u,q u g=t) (heps:eps≤t/2)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h Finset.univ p k q s g j (eps*Fintype.card V) σ H):
    ∀ u,(t/2)*Fintype.card V≤Fintype.card (hubNeighbourClass (H false) (H true) u true):=by
  intro u
  have he:=marked_single_hub_class_estimate P π d h hh Finset.univ p k q s g j _ σ H hr true u
  simp only [ite_true,hq,Finset.card_univ] at he
  have hcard:Fintype.card (hubNeighbourClass (H false) (H true) u true)=
      (Finset.univ.filter (H true · u)).card:=by
    simp only [hubNeighbourClass,ite_true,Fintype.card_subtype]
  rw [hcard]
  have hsmall:=mul_le_mul_of_nonneg_right heps (Nat.cast_nonneg (Fintype.card V): (0:ℝ)≤_)
  have hb:=(abs_lt.mp he).1
  linarith only [hsmall,hb]

end Oberwolfach
