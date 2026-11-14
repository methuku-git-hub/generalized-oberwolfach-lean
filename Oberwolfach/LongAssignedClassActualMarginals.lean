module

public import Oberwolfach.LongPreparationActualFamily
public import Oberwolfach.LongPreparationActualMarginals
public import Oberwolfach.LongPreparationFamilyFractions
public import Oberwolfach.LongAssignedClassReservation

@[expose] public section
/-! The manuscript's two-colour sampling bounds follow from the actual
components of the prescribed long-factor family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_factor_family_actual_marginals {U:Type} [Fintype U] {n:ℕ} (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀ u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none):
    let fraction:=fun (u:U) (j:Option (Fin K))=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=j)).card:ℝ)/n
    let retained:=fun (u:U)=>Finset.univ.filter (fun i=>θ/(100*(K:ℝ))≤fraction u (some i))
    let ℓ:=fun u=>fraction u none
    let rare:=fun u=>∑ i∈Finset.univ\retained u,fraction u (some i)
    let f:=fun (i:Fin K) u=>if i∈retained u then fraction u (some i) else 0;
    let c:ℝ:=(m:ℝ)+1
    let s₀:ℝ:=1/100
    let t:ℝ:=s₀/(m:ℝ)
    let a:=fun u=>(1-θ)*ℓ u/c-t
    let b:=fun u=>(m:ℝ)*a u+(1-θ)*∑ i,f i u
    let residual:=fun u=>1-s₀-t-a u-b u
    let q:=fun (u:U) (j:Bool)=>if j then a u else t
    let s:=fun (u:U) (j:Bool)=>if j then b u else s₀
    let p:=ρ*s₀/2
    let k:=ρ*t/2
    let p₂:=(∑ u,b u)/D
    let k₂:=(∑ u,a u)/D
    let udens:=2*(∑ u,residual u)/D;
    (∀ u,1/(3*c)≤a u ∧ 1/4≤b u ∧ b u≤1 ∧ 0≤residual u ∧ residual u≤2*θ ∧ (t+a u)/(d:ℝ)≤residual u) ∧
    (∀ u,q u false=t ∧ q u true=a u ∧ s u false=s₀ ∧ s u true=b u) ∧
    (∀ u j,0≤q u j) ∧ (∀ u,∑ j,q u j≤1/8) ∧
    (∀ u j,0≤s u j) ∧ (∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ j,q u j)) ∧
    0≤p ∧ 0≤k ∧ ρ/8≤p₂ ∧ ρ/(6*c)≤k₂ ∧ 0≤udens ∧
    2*p+2*k+2*p₂+2*k₂+udens=ρ ∧ 2*p+2*k+2*p₂+2*k₂+udens≤1 ∧ k=p/(m:ℝ):=by
  have hlong:=long_class_assigned_frequency hn F hF Allowed hAllowed K hK hclass
  exact long_preparation_factor_family_actual_marginals hn F hF K hK m d hm hd θ ρ D hθ0 hθ hρ hρ1 hD hsize hcut hlong
end Oberwolfach
