module

public import Oberwolfach.LongPreparationFamilyFractions
public import Oberwolfach.RetainedComplementTargetBounds
public import Oberwolfach.LongAssignedSeedTargets

@[expose] public section
/-! Identify the target left for long and discarded factor components. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U]

theorem long_ordinary_complement_target (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (θ:ℝ) (hθ:0≤θ)
    (hlong:∀u,(1/2:ℝ)≤
      ((Finset.univ.filter (fun v=>K<Fintype.card ((F u).connectedComponentMk v))).card:ℝ)/n):
    ∀u,
      ordinaryAssignedFraction F hF K u none ≤
        1-(1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u) ∧
      1-(1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u) ≤
        ordinaryAssignedFraction F hF K u none+(101/100:ℝ)*θ :=by
  let fraction:=fun (u:U) (j:Option (Fin K))=>ordinaryAssignedFraction F hF K u j
  let retained:=fun (u:U)=>Finset.univ.filter (fun i=>θ/(100*(K:ℝ))≤fraction u (some i))
  let rare:=fun u=>∑ i∈Finset.univ\retained u,fraction u (some i)
  let f:=fun (i:Fin K) u=>if i∈retained u then fraction u (some i) else 0
  have hdata:=long_preparation_family_fractions hn F hF K hK θ hθ hlong
  change (∀u,(1/2:ℝ)≤fraction u none ∧ fraction u none≤1) ∧
    (∀u,0≤rare u ∧ rare u≤θ/100) ∧ (∀i u,0≤f i u) ∧
    (∀u,fraction u none+(∑i,f i u)+rare u=1) ∧
    (∀u i,i∈retained u→θ/(100*(K:ℝ))≤f i u) at hdata
  have heq:∀i u,f i u=longAssignedKeptFraction F hF K θ i u:=by
    intro i u
    simp [f,retained,fraction,longAssignedKeptFraction]
  intro u
  have h:=retained_complement_target_bounds (fraction u none) (rare u) θ (fun i=>f i u)
    hθ (by have hh:=(hdata.1 u).1;linarith) (hdata.2.1 u) (fun i=>hdata.2.2.1 i u) (hdata.2.2.2.1 u)
  simpa only [fraction,heq] using h

end Oberwolfach
