module

public import Oberwolfach.LongPreparationFamilySeeds
public import Oberwolfach.LongPreparationUniformSeedDensity
public import Oberwolfach.LongPreparationRetainedSum

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

theorem long_preparation_uniform_family_seed_coefficients {U:Type} [Fintype U] {n:ℕ} (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀ u,(F u).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hlong:∀ u,(1/2:ℝ)≤
      ((Finset.univ.filter (fun v=>K<Fintype.card ((F u).connectedComponentMk v))).card:ℝ)/n):
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
  intro fraction S f c t a b η p k pstar
  have hρ:0<ρ:=hρ₀.trans_le hρlo
  have hfixed:=long_preparation_uniform_seed_density m ρ₀ ρ hρ₀ hρlo
  have ha:=long_preparation_factor_family_seed_coefficients hn F hF K hK m d hm hd θ ρ D
    hθ0 hθ hρ hρ1 hD hsize hcut hlong
  dsimp only at hfixed ha
  have hp_le:pstar≤min (1/4:ℝ) (min (ρ/8) (ρ/(6*c))):=by
    exact le_min hfixed.2.1 (le_min hfixed.2.2.1 hfixed.2.2.2)
  have hsums (u:U):(∑ i:{i:Fin K // i∈S},η i u)=
      ∑ i:Fin K,(1-θ)*f i u/b u:=by
    have h:=long_preparation_retained_coefficient_sum F hF K θ b u
    simpa [fraction,S,f,η] using h
  have hA:(∀ u,(m:ℝ)*a u+(∑ i:Fin K,(1-θ)*f i u/b u)*b u=b u):=by
    simpa [fraction,f,c,t,a,b] using ha.2.2.2.2.2.1
  refine ⟨hfixed.1,?_,?_,?_,?_,?_,?_,?_⟩
  · apply hp_le.trans
    simpa [fraction,S,f,c,t,a,b,p] using ha.2.1
  · apply hp_le.trans
    simpa [fraction,S,f,c,t,a,b,k] using ha.2.2.1
  · intro u
    apply hp_le.trans
    simpa [fraction,S,f,c,t,a,b] using ha.2.2.2.1 u
  · intro i u
    have hh:=ha.2.2.2.2.1 i.val u
    simpa [fraction,S,f,c,t,a,b,η] using hh
  · intro u
    rw [hsums]
    exact hA u
  · simpa [fraction,f,c,t,a,b,k] using ha.2.2.2.2.2.2.1
  · simpa [fraction,f,c,t,a,b,p] using ha.2.2.2.2.2.2.2
end Oberwolfach
