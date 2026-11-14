module

public import Oberwolfach.FactorClassPruning

@[expose] public section
/-! The concrete long- and short-class cutoffs imply the deletion budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_small_class_budget {W:Type} [Fintype W] (K:ℕ) (hK:0<K)
    (classify:W→Option (Fin K)) (n α κL κS:ℝ)
    (hn:0≤n) (hα:0<α) (hL0:0≤κL) (hS0:0≤κS)
    (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ))):
    let fibres:=fun j:Option (Fin K)=>Finset.univ.filter (fun w=>classify w=j)
    let small:=fun j:Option (Fin K)=>
      ((fibres j).card:ℝ)<(if j=none then κL*n else κS*n)
    let removed:=Finset.univ.filter (fun w=>small (classify w));
    (removed.card:ℝ)≤α*n/500:=by
  intro fibres small removed
  have hK':(0:ℝ)<K:=by exact_mod_cast hK
  have hKS:(K:ℝ)*κS≤α/1000:=by
    have h:κS*(K:ℝ)≤α/1000:=by
      apply (le_div_iff₀ hK').mp
      have hh:=hS
      convert hh using 1 <;> ring
    nlinarith
  have hco:κL+(K:ℝ)*κS≤α/500:=by linarith
  have hsum:=factor_class_pruning_bound K classify n κL κS hn hL0 hS0
  have hraw:(removed.card:ℝ)≤(κL+(K:ℝ)*κS)*n:=by simpa [fibres,small,removed] using hsum.1
  calc
    _ ≤ (κL+(K:ℝ)*κS)*n:=hraw
    _ ≤ (α/500)*n:=mul_le_mul_of_nonneg_right hco hn
    _ = α*n/500:=by ring
end Oberwolfach
