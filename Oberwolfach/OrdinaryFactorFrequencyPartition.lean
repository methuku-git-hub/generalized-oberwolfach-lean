module

public import Oberwolfach.LongPreparationFactorFractions

@[expose] public section
/-! Remove the reserved short-cycle fraction from the actual component
frequencies of a prescribed 2-factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem ordinary_factor_frequency_partition {n:ℕ} (hn:0<n)
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (s:ℝ) (hs:0≤s)
    (hreserve:s≤((Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=some i₀)).card:ℝ)/n):
    let fraction:Option (Fin K)→ℝ:=fun j=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=j)).card:ℝ)/n
    let f:Fin K→ℝ:=fun i=>fraction (some i)-(if i=i₀ then s else 0);
    (∀ i,0≤f i) ∧ 0≤fraction none ∧ (∑ i,f i)+fraction none=1-s := by
  intro fraction f
  have hfr:=long_preparation_vertex_fractions (V:=Fin n) (by simpa using hn) K (longPreparationCycleClass F hF K)
  have hn0:(0:ℝ)≤n:=by positivity
  have hf0:∀ i,0≤fraction (some i):=fun i=>by dsimp [fraction];positivity
  have hlong0:0≤fraction none:=by dsimp [fraction];positivity
  have hsum:fraction none+(∑ i,fraction (some i))=1:=by simpa [fraction] using hfr.2
  have hreserve':s≤fraction (some i₀):=by simpa [fraction] using hreserve
  refine ⟨?_,hlong0,?_⟩
  · intro i
    dsimp [f]
    by_cases hi:i=i₀
    · subst i;simp [hreserve']
    · simp [hi,hf0]
  · dsimp [f]
    rw [Finset.sum_sub_distrib]
    have hind:(∑ i:Fin K,(if i=i₀ then s else 0))=s:=by simp
    rw [hind]
    linarith
end Oberwolfach
