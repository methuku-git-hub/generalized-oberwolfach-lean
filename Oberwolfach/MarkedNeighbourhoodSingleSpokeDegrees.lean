module

public import Oberwolfach.MarkedSpokeIntersectionsFromNeighbourhoods

@[expose] public section
/-! Singleton neighbourhood tests give the retained spoke degrees used by
the global near-balance estimates. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_neighbourhood_single_spoke_degrees
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (hh:1≤h) (p k:ℝ)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (errR errI density:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (mark:Bool)
    (hden:∀u,(if mark then q u g else s u j)=density)
    (hr:MarkedRowsWithSpokes P π d h Finset.univ p k q s g j errR σ H)
    (hi:MarkedIndicesWithSpokes π d h Finset.univ q s g j errI σ H):
    (∀u,|(∑v,if H mark v u then (1:ℝ) else 0)-density*Fintype.card V|<errR) ∧
    (∀v,|(∑u,if H mark v u then (1:ℝ) else 0)-density*Fintype.card U|<errI):=by
  constructor
  · intro u
    have hc:=markedRows_spoke_intersections P π d h p k q s g j errR density σ H mark hden hr {u} (by simpa using hh)
    simpa only [commonSpokeNeighbours,Finset.mem_singleton,forall_eq,Finset.card_filter,
      Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.card_singleton,pow_one] using hc
  · intro v
    have hsep:∀a∈({(mark,v)}:Finset (Bool×V)),∀b∈({(mark,v)}:Finset (Bool×V)),
        a≠b→¬PermutationClose π (3*d) a.2 b.2:=by
      intro a ha b hb hab
      simp only [Finset.mem_singleton] at ha hb
      subst a;subst b;exact (hab rfl).elim
    have hc:=hi {(mark,v)} (by simpa using hh) hsep
    simp only [markedIndexCountWithSpokes,Finset.mem_singleton,forall_eq,Finset.prod_singleton] at hc
    simp only [hden,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hc
    simpa only [mul_comm] using hc
end Oberwolfach
