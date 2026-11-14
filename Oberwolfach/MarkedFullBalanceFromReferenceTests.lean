module

public import Oberwolfach.MarkedReferenceSingletonSpokeCounts
public import Oberwolfach.MarkedFullBalanceFromCenters
public import Oberwolfach.MarkedReferenceStatistics

@[expose] public section
/-! The existing common reference tests imply full-domain balance for the
retained spokes, using the original probability centers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_full_balance_from_reference_tests
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m h:ℕ) (hh:1≤h)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (D p k t εR δ γ εrow εcol ε:ℝ)
    (hεR:0≤εR) (hεrow:0≤εrow) (hεcol:0≤εcol)
    (hq:∀u,q u g=t) (hs:∀u,s u j=(m:ℝ)*t)
    (hp:p*D=(m:ℝ)*(t*Fintype.card U)) (hk:k*D=t*Fintype.card U)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hstats:MarkedReferenceStatistics P π d g j D εR δ γ p k ((m:ℝ)*t) t σ)
    (hrows:MarkedRowsWithSpokes P π d h Finset.univ p k q s g j εcol σ H)
    (hindices:MarkedIndicesWithSpokes π d h Finset.univ q s g j εrow σ H)
    (hrowBudget:2*(εR*Fintype.card V+εrow)≤ε)
    (hcolBudget:((m:ℝ)+1)*εcol≤ε):
    MarkedRestrictedBalanceWithSpokes P π d m Finset.univ Finset.univ ε σ H:=by
  have hcounts:=marked_reference_singleton_spoke_counts P π d h hh p k q s g j εrow εcol σ H hrows hindices
  have hR:∀mark incoming v,|(markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming v Finset.univ:ℝ)-
      (if mark then t*Fintype.card U else (m:ℝ)*(t*Fintype.card U))|≤εR*Fintype.card V:=by
    intro mark incoming v
    have ht:=hstats.1.1 mark v
    cases incoming with
    | false => cases mark <;> simpa only [markedRestrictedDegree,Bool.false_eq_true,↓reduceIte,Nat.cast_sum,hp,hk] using ht.1
    | true => cases mark <;> simpa only [markedRestrictedDegree,Bool.false_eq_true,↓reduceIte,Nat.cast_sum,hp,hk] using ht.2
  have hS:∀mark v,|(∑u,bipAdj (H mark) v u)-
      (if mark then t*Fintype.card U else (m:ℝ)*(t*Fintype.card U))|≤εrow:=by
    intro mark v
    have ht:=hcounts.1 mark v
    have hsum:(∑u,bipAdj (H mark) v u)=((Finset.univ.filter (fun u=>H mark v u)).card:ℝ):=by simp [bipAdj,Finset.sum_boole]
    rw [hsum]
    cases mark <;> simp only [Bool.false_eq_true,↓reduceIte,hq,hs,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at ht ⊢ <;>
      (convert le_of_lt ht using 1 <;> congr 2 <;> ring)
  have hC:∀mark u,|(∑v,bipAdj (H mark) v u)-
      (if mark then t*Fintype.card V else (m:ℝ)*(t*Fintype.card V))|≤εcol:=by
    intro mark u
    have ht:=hcounts.2 mark u
    have hsum:(∑v,bipAdj (H mark) v u)=((Finset.univ.filter (fun v=>H mark v u)).card:ℝ):=by simp [bipAdj,Finset.sum_boole]
    rw [hsum]
    cases mark <;> simp only [Bool.false_eq_true,↓reduceIte,hq,hs] at ht ⊢ <;>
      (convert le_of_lt ht using 1 <;> congr 2 <;> ring)
  exact marked_full_balance_from_centers P π d m σ H (t*Fintype.card U) (t*Fintype.card V)
    (εR*Fintype.card V) εrow εcol ε (mul_nonneg hεR (Nat.cast_nonneg _)) hεrow hεcol hR hS hC hrowBudget hcolBudget
end Oberwolfach
