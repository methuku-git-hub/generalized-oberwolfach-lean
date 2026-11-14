module

public import Oberwolfach.LongAssignedSamplingRecipe

@[expose] public section
/-! The formulas used by the reference-weight construction are the original
long-class sampling recipe, including the fixed frequency cutoffs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_reference_recipe_identity {n K m:ℕ} {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (θ D:ℝ):
    let fraction:=fun (u:U) (i:Fin K)=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i)).card:ℝ)/n
    let retained:=Finset.univ.filter (fun i=>∃ u,θ/(100*(K:ℝ))≤fraction u i)
    let f:=fun (i:Fin K) u=>if θ/(100*(K:ℝ))≤fraction u i then fraction u i else 0
    let c:ℝ:=(m:ℝ)+1
    let t:ℝ:=(1/100)/(m:ℝ)
    let a:=fun u=>(1-θ)*(((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=none)).card:ℝ)/n)/c-t
    let b:=fun u=>(m:ℝ)*a u+(1-θ)*∑ i,f i u
    let q:=fun (u:U) (j:Bool)=>if j then a u else t
    let sco:=fun (u:U) (j:Bool)=>if j then b u else (1/100:ℝ);
    (∀u,a u=longAssignedApproxMarkedWeight F hF K m θ u) ∧
    (∀u,b u=longAssignedApproxOrdinaryWeight F hF K m θ u) ∧
    q=longAssignedIntervalProbability F hF K m θ ∧
    sco=longAssignedSpokeProbability F hF K m θ ∧
    (∑u,a u)/D=(∑u,longAssignedApproxMarkedWeight F hF K m θ u)/D ∧
    (∑u,b u)/D=(∑u,longAssignedApproxOrdinaryWeight F hF K m θ u)/D ∧
    2*(∑u,(1-(1/100:ℝ)-t-a u-b u))/D=
      2*(∑u,(1-(1/100:ℝ)-(1/100)/(m:ℝ)-longAssignedApproxMarkedWeight F hF K m θ u-
        longAssignedApproxOrdinaryWeight F hF K m θ u))/D :=by
  intro fraction retained f c t a b q sco
  have ha:∀u,a u=longAssignedApproxMarkedWeight F hF K m θ u:=by intro u;rfl
  have hb:∀u,b u=longAssignedApproxOrdinaryWeight F hF K m θ u:=by intro u;rfl
  refine ⟨ha,hb,?_,?_,?_,?_,?_⟩
  · funext u j;cases j <;> rfl
  · funext u j;cases j <;> rfl
  · rfl
  · rfl
  · rfl
end Oberwolfach
