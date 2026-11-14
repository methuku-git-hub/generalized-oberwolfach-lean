module

public import Oberwolfach.OrdinaryActualFrequencyMarginals
public import Oberwolfach.OrdinaryFactorFrequencyPartition

@[expose] public section
/-! The retained ordinary-class marginals come from the actual prescribed
2-factor after reserving its short cycles. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem ordinary_factor_actual_marginals {n:ℕ} (hn:0<n)
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
    let shortKept:=∑ i:Fin K,(if f i<cutoff then 0 else f i)
    let omitted:=(∑ i:Fin K,(if f i<cutoff then f i else 0))+
      (if long<θ/100 then long else 0)
    let a:=(1-θ)*longKept/c
    let b:=(c-1)*a+(1-θ)*shortKept
    let u:=1-s-a-b;
    0≤omitted ∧ omitted≤θ/50 ∧
    u=θ*(1-s)+(1-θ)*omitted ∧ θ/2≤u ∧ u≤2*θ ∧
    0≤a ∧ a≤1/c ∧ 1/2≤b ∧ s+a+b+u=1 := by
  intro fraction f long cutoff longKept shortKept omitted a b u
  have hpart:=ordinary_factor_frequency_partition hn F hF K hK i₀ s hs0 hreserve
  have hh:=ordinary_actual_frequency_marginals K hK s θ c long f hs0 hs1 hθ0 hθ1 hc hpart.2.1 hpart.1 hpart.2.2
  exact hh
end Oberwolfach
