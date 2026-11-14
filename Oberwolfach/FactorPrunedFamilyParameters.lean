module

public import Oberwolfach.FactorClassDensitySum
public import Oberwolfach.FactorRemainingClasses
public import Oberwolfach.FactorRemovalPositiveDegree

@[expose] public section
/-! The sizes and density profile passed to the class-partition theorem are
those of the actual remaining family after the small classes are deleted. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_pruned_family_parameters {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
    (K:ℕ) (hK:0<K) (classify:W→Option (Fin K))
    (D:ℕ) (hEven:Even D) (hsize:Fintype.card W=D/2) (hDn:D≤n)
    (δ α κL κS:ℝ) (hδ:0≤δ) (hα:0<α)
    (hL0:0≤κL) (hS0:0≤κS) (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ)))
    (hdegree:(δ+α)*(n:ℝ)≤D):
    let fibres:=fun j:Option (Fin K)=>Finset.univ.filter (fun w=>classify w=j)
    let cutoff:=fun j:Option (Fin K)=>if j=none then κL else κS
    let small:=fun j:Option (Fin K)=>((fibres j).card:ℝ)<cutoff j*n
    let removed:=Finset.univ.filter (fun w=>small (classify w))
    let remaining:={w:W // w∉removed}
    let classifyRemaining:=fun w:remaining=>classify w.val
    let D0:=D-2*removed.card;
    0<D0 ∧ Fintype.card remaining=D0/2 ∧ Even D0 ∧
    (∑ j:Option (Fin K),2*((Finset.univ.filter (fun w=>classifyRemaining w=j)).card:ℝ)/D0)=1 ∧
    (∀ j,(∃ w:remaining,classifyRemaining w=j)→2*cutoff j≤
      2*((Finset.univ.filter (fun w:remaining=>classifyRemaining w=j)).card:ℝ)/D0):=by
  intro fibres cutoff small removed remaining classifyRemaining D0
  have hb:=factor_small_class_budget K hK classify (n:ℝ) α κL κS (by positivity) hα hL0 hS0 hL hS
  have hsmall:(removed.card:ℝ)≤α*n/500:=by simpa [fibres,cutoff,small,removed,ite_mul] using hb
  have hpositive:2*removed.card<D:=factor_small_removal_positive_degree D removed.card n hn δ α hδ hα hdegree hsmall
  have hD0:0<D0:=by dsimp [D0];omega
  have hsize0:=factor_remaining_family_size D hEven hsize removed hpositive.le
  have hsum:=factor_remaining_class_density_sum D hEven hsize removed hpositive K classifyRemaining
  have hD0R:(0:ℝ)<D0:=by exact_mod_cast hD0
  have hD0n:(D0:ℝ)≤n:=by
    have hd:D0≤n:=by dsimp [D0];omega
    exact_mod_cast hd
  refine ⟨hD0,hsize0.1,hsize0.2,hsum,?_⟩
  intro j hj
  have hnot:=factor_remaining_class_not_small K classify (n:ℝ) κL κS j hj
  have hh:=factor_retained_class_actual_density K classify (n:ℝ) (D0:ℝ) κL κS
    (by positivity) hD0R hD0n hL0 hS0 j hnot
  simpa [cutoff,classifyRemaining,mul_ite] using hh
end Oberwolfach
