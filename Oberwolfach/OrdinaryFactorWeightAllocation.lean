module

public import Oberwolfach.OrdinaryFactorActualMarginals
public import Oberwolfach.OrdinaryFrequencyWeightAllocation

@[expose] public section
/-! Instantiate the frequency weights using the actual component frequencies
of a factor and its fixed reserved short-cycle fraction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem ordinary_factor_frequency_weight_allocation {n:ℕ} (hn:0<n)
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2) (K:ℕ) (hK:0<K)
    (i₀:Fin K) (s θ c:ℝ) (hs0:0≤s) (hs1:s≤1/100)
    (hθ0:0≤θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hreserve:s≤((Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=some i₀)).card:ℝ)/n):
    let fraction:Option (Fin K)→ℝ:=fun j=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=j)).card:ℝ)/n
    let f:Fin K→ℝ:=fun i=>fraction (some i)-(if i=i₀ then s else 0)
    let long:=fraction none
    let cutoff:=θ/(100*(K:ℝ))
    let longKept:=if long<θ/100 then 0 else long
    let kept:=fun i:Fin K=>if f i<cutoff then 0 else f i
    let a:=(1-θ)*longKept/c
    let b:=(c-1)*a+(1-θ)*∑ i,kept i
    let η:=fun i:Fin K=>(1-θ)*kept i/b;
    0<b ∧ (∀ i,0≤η i ∧ η i≤1/b) ∧ (∑ i,η i)*b+(c-1)*a=b := by
  intro fraction f long cutoff longKept kept a b η
  have hpart:=ordinary_factor_frequency_partition hn F hF K hK i₀ s hs0 hreserve
  have hsum:(∑ i,f i)≤1:=by linarith [hpart.2.1,hpart.2.2]
  have hf1:∀ i,f i≤1:=by
    intro i
    have hh:=Finset.single_le_sum (fun j _=>hpart.1 j) (Finset.mem_univ i)
    exact hh.trans hsum
  have hk0:∀ i,0≤kept i:=by
    intro i
    dsimp [kept]
    split_ifs
    · norm_num
    · exact hpart.1 i
  have hk1:∀ i,kept i≤1:=by
    intro i
    dsimp [kept]
    split_ifs
    · norm_num
    · exact hf1 i
  have hmain:=ordinary_factor_actual_marginals hn F hF K hK i₀ s θ c hs0 hs1 hθ0 hθ1 hc hreserve
  have hb:0<b:=by have hh:=hmain.2.2.2.2.2.2.2.1;linarith
  have hw:=ordinary_frequency_weight_allocation K θ c a b kept hθ0 (by linarith) hk0 hk1 hb rfl
  exact ⟨hb,hw⟩
end Oberwolfach
