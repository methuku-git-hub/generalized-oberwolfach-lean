module

public import Oberwolfach.LongPreparationUniformFamilySeeds
public import Oberwolfach.LongPreparationFamilySeeds
public import Oberwolfach.LongPreparationUniformSeedDensity
public import Oberwolfach.LongPreparationRetainedSum
public import Oberwolfach.LongAssignedClassReservation

@[expose] public section
/-! The fixed lower density and balanced hub coefficients required by the
seeded theorem, with the genuinely retained index set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_uniform_family_seed_coefficients {U:Type} [Fintype U] {n:ℕ} (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀ u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none):
    let fraction:=fun (u:U) (i:Fin K)=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i)).card:ℝ)/n
    let S:=Finset.univ.filter (fun i=>∃ u,θ/(100*(K:ℝ))≤fraction u i)
    let f:=fun (i:Fin K) u=>if θ/(100*(K:ℝ))≤fraction u i then fraction u i else 0
    let c:ℝ:=(m:ℝ)+1
    let t:ℝ:=(1/100)/(m:ℝ)
    let a:=fun u=>(1-θ)*
      (((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=none)).card:ℝ)/n)/c-t
    let b:=fun u=>(m:ℝ)*a u+(1-θ)*∑ i,f i u
    let η:=fun (i:{i:Fin K // i∈S}) u=>(1-θ)*f i.val u/b u
    let p:=(∑ u,b u)/D
    let k:=(∑ u,a u)/D
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*c)));
    0<pstar ∧ pstar≤p ∧ pstar≤k ∧ (∀ u,pstar≤b u) ∧
    (∀ i u,0≤η i u ∧ η i u≤1/b u) ∧
    (∀ u,(m:ℝ)*a u+(∑ i,η i u)*b u=b u) ∧
    (∑ u,a u)=D*k ∧ (∑ u,b u)=D*p:=by
  have hlong:=long_class_assigned_frequency hn F hF Allowed hAllowed K hK hclass
  exact long_preparation_uniform_family_seed_coefficients hn F hF K hK m d hm hd θ ρ₀ ρ D hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hlong
end Oberwolfach
