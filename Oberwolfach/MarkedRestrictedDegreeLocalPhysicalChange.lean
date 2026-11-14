module

public import Oberwolfach.MarkedRestrictedBalancePhysicalChanges

@[expose] public section
/-! Restricted rim degrees are controlled by the change graph's edges into
an invariant protected set, rather than by its whole ambient degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_restricted_degree_after_local_physical_changes
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A:Finset V)
    (hA:∀x,π x∈A↔x∈A)
    (σ τ:RawMarkedOutcome V U Γ Color) (D:SimpleGraph V) (δ:ℝ)
    (hchange:∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈D.edgeFinset)
    (hD:∀v,((A.filter (fun x=>D.Adj v x)).card:ℝ)≤δ)
    (mark incoming:Bool) (v:V):
    |(markedRestrictedDegree P π (3*d) (fun e=>τ (Sum.inl e)) mark incoming v A:ℝ)-
      (markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming v A:ℝ)|≤δ :=by
  let R:=fun x=>rawMarkedPairRims P π d σ (markedRowRim (mark,incoming,v) x)
  let R':=fun x=>rawMarkedPairRims P π d τ (markedRowRim (mark,incoming,v) x)
  have himage:A.image π=A:=by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
      exact (hA y).mpr hy
    · intro hx
      apply Finset.mem_image.mpr
      exact ⟨π.symm x,(hA (π.symm x)).mp (by simpa using hx),by simp⟩
  have hsum (z:V):(∑x∈A,if D.Adj z x then (1:ℝ) else 0)=((A.filter (fun x=>D.Adj z x)).card:ℝ):=by
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have hsumπ (z:V):(∑x∈A,if D.Adj z (π x) then (1:ℝ) else 0)=((A.filter (fun x=>D.Adj z x)).card:ℝ):=by
    calc
      _ = ∑x∈A.image π,if D.Adj z x then (1:ℝ) else 0 := by
        symm
        rw [Finset.sum_image (fun _ _ _ _ he=>π.injective he)]
      _ = _ := by rw [himage];exact hsum z
  have hphysical:(∑x∈A,if markedPairPhysical π (markedRowRim (mark,incoming,v) x)∈D.edgeFinset then (1:ℝ) else 0)≤δ:=by
    cases mark <;> cases incoming <;>
      simp only [markedRowRim,markedPairPhysical,Bool.false_eq_true,ite_false,ite_true,
        Sum.elim_inl,Sum.elim_inr,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] <;>
      first | simpa only [D.adj_comm] using ((hsum v).trans_le (hD v))
            | simpa only [D.adj_comm] using ((hsumπ v).trans_le (hD v))
            | simpa only [D.adj_comm] using ((hsum (π v)).trans_le (hD (π v)))
  have hinc:(∑x∈A,if ¬(R x↔R' x) then (1:ℝ) else 0)≤δ:=by
    apply le_trans _ hphysical
    apply Finset.sum_le_sum
    intro x _
    by_cases h:¬(R x↔R' x)
    · simp [h,hchange _ h]
    · simp [h];positivity
  have hh:=(indicator_sum_change A R R').trans hinc
  convert hh using 1
  apply congrArg abs
  apply congrArg₂ (fun a b:ℝ=>a-b) <;> unfold markedRestrictedDegree <;> simp only [Nat.cast_sum] <;>
    apply Finset.sum_congr rfl <;> intro x hx <;> dsimp [R,R',markedRowRim,rawMarkedPairRims] <;>
    cases mark <;> cases incoming <;> simp only [Bool.false_eq_true,ite_false,ite_true,Sum.elim_inl,Sum.elim_inr] <;>
    norm_cast <;> symm <;> exact markedPhysicalRim_indicator _ _ _ _ _ _ _
end Oberwolfach
