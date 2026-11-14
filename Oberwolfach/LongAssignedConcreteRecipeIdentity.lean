module

public import Oberwolfach.LongAssignedSamplingRecipe

@[expose] public section
/-! The retained-frequency formulation and the named long-class sampling
recipe agree pointwise, including the two approximate densities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_concrete_recipe_identity {n K m:ℕ} {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (θ D:ℝ):
    let fraction:=fun (u:U) (j:Option (Fin K))=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=j)).card:ℝ)/n
    let retained:=fun (u:U)=>Finset.univ.filter (fun i=>θ/(100*(K:ℝ))≤fraction u (some i))
    let f:=fun (i:Fin K) u=>if i∈retained u then fraction u (some i) else 0
    let c:ℝ:=(m:ℝ)+1
    let t:ℝ:=(1/100)/(m:ℝ)
    let a:=fun u=>(1-θ)*fraction u none/c-t
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
  have hf:∀i u,f i u=(if θ/(100*(K:ℝ))≤ordinaryAssignedFraction F hF K u (some i)
      then ordinaryAssignedFraction F hF K u (some i) else 0):=by
    intro i u
    simp only [f,retained,Finset.mem_filter,Finset.mem_univ,true_and,fraction,ordinaryAssignedFraction]
  have hb:∀u,b u=longAssignedApproxOrdinaryWeight F hF K m θ u:=by
    intro u
    dsimp only [b,longAssignedApproxOrdinaryWeight]
    rw [ha u]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact hf i u
  refine ⟨ha,hb,?_,?_,?_,?_,?_⟩
  · funext u j;cases j <;> simp only [q,t,longAssignedIntervalProbability,Bool.false_eq_true,↓reduceIte,ha]
  · funext u j;cases j <;> simp only [sco,longAssignedSpokeProbability,Bool.false_eq_true,↓reduceIte,hb]
  · rfl
  · congr 1;exact Finset.sum_congr rfl (fun u _=>hb u)
  · congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    rw [ha u,hb u]
end Oberwolfach
