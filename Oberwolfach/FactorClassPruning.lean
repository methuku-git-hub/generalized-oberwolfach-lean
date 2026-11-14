module

public import Oberwolfach.FactorClassAssignment

@[expose] public section
/-! Removing small classes deletes at most the sum of their stated size
thresholds. The class assignment and the thresholds are fixed first. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_class_pruning_bound {W:Type} [Fintype W] (K:ℕ)
    (classify:W→Option (Fin K)) (n κL κS:ℝ)
    (hn:0≤n) (hL:0≤κL) (hS:0≤κS):
    let fibres:=fun j:Option (Fin K)=>Finset.univ.filter (fun w=>classify w=j)
    let small:=fun j:Option (Fin K)=>
      ((fibres j).card:ℝ)<(if j=none then κL*n else κS*n)
    let removed:=Finset.univ.filter (fun w=>small (classify w));
    (removed.card:ℝ)≤(κL+(K:ℝ)*κS)*n ∧
    (∀ j,¬small j→(fibres j∩removed).card=0):=by
  intro fibres small removed
  have hcount (j:Option (Fin K)):
      (((removed.filter (fun w=>classify w=j)).card:ℝ))≤
        (if j=none then κL*n else κS*n):=by
    by_cases hj:small j
    · have hsub:removed.filter (fun w=>classify w=j)⊆fibres j:=by
        intro w hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,(Finset.mem_filter.mp hw).2⟩
      have hle:(((removed.filter (fun w=>classify w=j)).card:ℝ))≤(fibres j).card:=by
        exact_mod_cast Finset.card_le_card hsub
      exact hle.trans (le_of_lt hj)
    · have he:removed.filter (fun w=>classify w=j)=∅:=by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        have hw':=Finset.mem_filter.mp hw
        have hs:small (classify w):=(Finset.mem_filter.mp hw'.1).2
        rw [hw'.2] at hs
        exact hj hs
      rw [he,Finset.card_empty,Nat.cast_zero]
      split <;> positivity
  have hpartition:(∑ j:Option (Fin K),((removed.filter (fun w=>classify w=j)).card:ℝ))=removed.card:=by
    have h:=Finset.sum_card_fiberwise_eq_card_filter removed (Finset.univ:Finset (Option (Fin K))) classify
    have hnat:(∑ j:Option (Fin K),(removed.filter (fun w=>classify w=j)).card)=removed.card:=by simpa using h
    exact_mod_cast hnat
  have hbound:(∑ j:Option (Fin K),((removed.filter (fun w=>classify w=j)).card:ℝ))≤
      (∑ j:Option (Fin K),if j=none then κL*n else κS*n):=
    Finset.sum_le_sum (fun j _=>hcount j)
  have hright:(∑ j:Option (Fin K),if j=none then κL*n else κS*n)=
      (κL+(K:ℝ)*κS)*n:=by simp only [Fintype.sum_option,Option.some_ne_none,ite_false,ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id];ring
  constructor
  · linarith
  · intro j hj
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hmem:=Finset.mem_inter.mp hw
    have hc:classify w=j:=(Finset.mem_filter.mp hmem.1).2
    have hs:small (classify w):=(Finset.mem_filter.mp hmem.2).2
    rw [hc] at hs
    exact hj hs

/-- A class not removed by its size cutoff has the density required by its
preparation proposition, since the remaining host degree is at most its order. -/
theorem factor_retained_class_density {W:Type} [Fintype W] (K:ℕ)
    (classify:W→Option (Fin K)) (n D κL κS:ℝ)
    (hn:0≤n) (hD:0<D) (hDn:D≤n) (hL:0≤κL) (hS:0≤κS):
    let fibres:=fun j:Option (Fin K)=>Finset.univ.filter (fun w=>classify w=j)
    let cutoff:=fun j:Option (Fin K)=>if j=none then κL else κS;
    ∀ j, cutoff j*n≤(fibres j).card →
      2*cutoff j≤2*(fibres j).card/D:=by
  intro fibres cutoff j hj
  have hk:0≤cutoff j:=by dsimp [cutoff];split <;> assumption
  have hh:=mul_nonneg hk (sub_nonneg.mpr hDn)
  apply (le_div_iff₀ hD).2
  nlinarith
end Oberwolfach
