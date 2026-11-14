module

public import Oberwolfach.LongPreparationFactorClassification
public import Oberwolfach.LongPreparationRetainedFractions

@[expose] public section
/-! The actual vertex fractions of a prescribed factor, including the total
weight of short lengths discarded by the manuscript's threshold rule. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_factor_fractions {n:ℕ} (hn:0<n)
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (θ:ℝ) (hθ:0≤θ):
    let fraction:Option (Fin K)→ℝ:=fun j=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=j)).card:ℝ)/n
    let S:Finset (Fin K):=Finset.univ.filter (fun i=>θ/(100*(K:ℝ))≤fraction (some i))
    let rare:=∑ i∈Finset.univ\S,fraction (some i);
    (∀ v, longPreparationCycleClass F hF K v=none ↔ K<Fintype.card (F.connectedComponentMk v)) ∧
    (∀ v i, longPreparationCycleClass F hF K v=some i ↔ Fintype.card (F.connectedComponentMk v)=i.val+1) ∧
    (∀ j,0≤fraction j) ∧ (∀ i∈S,θ/(100*(K:ℝ))≤fraction (some i)) ∧
    0≤rare ∧ rare≤θ/100 ∧ fraction none+(∑ i∈S,fraction (some i))+rare=1:=by
  intro fraction S rare
  have hn':0<Fintype.card (Fin n):=by simpa using hn
  have hfreq:=long_preparation_vertex_fractions hn' K (longPreparationCycleClass F hF K)
  have hfreq':(∀ j,0≤fraction j) ∧ fraction none+(∑ i,fraction (some i))=1:=by
    simpa [fraction] using hfreq
  have hret:=long_preparation_retained_fractions K hK θ (fraction none) hθ
    (fun i=>fraction (some i)) (fun i=>hfreq'.1 _) hfreq'.2
  have hret':(∀ i∈S,θ/(100*(K:ℝ))≤fraction (some i)) ∧
      0≤rare ∧ rare≤θ/100 ∧ fraction none+(∑ i∈S,fraction (some i))+rare=1:=by
    simpa [S,rare] using hret
  exact ⟨fun v=>(long_preparation_cycle_class F hF K v).1,
    fun v=>(long_preparation_cycle_class F hF K v).2,hfreq'.1,hret'⟩
end Oberwolfach
