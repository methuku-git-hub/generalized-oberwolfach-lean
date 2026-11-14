module

public import Oberwolfach.FixedLengthPadding

@[expose] public section
/-! The fixed-index padding reproduces the original coefficient at every
hub, including zero coefficients of unretained lengths. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_coefficient_padding {I U:Type} [Fintype I] [DecidableEq I] [Fintype U]
    (fraction:U→I→ℝ) (threshold θ:ℝ) (b:U→ℝ):
    let S:=Finset.univ.filter (fun i=>∃ u,threshold≤fraction u i)
    let f:=fun i u=>if threshold≤fraction u i then fraction u i else 0
    let ηS:=fun (i:↥S) u=>(1-θ)*f i.val u/b u;
    ∀ i u,padIndexedFunctions S (fun _=>U) ηS i u=(1-θ)*f i u/b u:=by
  intro S f ηS i u
  by_cases hi:i∈S
  · simpa [ηS] using pad_indexed_functions_on S (fun _=>U) ηS ⟨i,hi⟩ u
  · have hf:¬threshold≤fraction u i:=by
      intro hh
      apply hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,u,hh⟩
    rw [pad_indexed_functions_off S (fun _=>U) ηS i hi u]
    simp [f,hf]
end Oberwolfach
