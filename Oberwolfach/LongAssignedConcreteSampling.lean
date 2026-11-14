module

public import Oberwolfach.LongAssignedClassActualMarginals
public import Oberwolfach.LongAssignedSelectedDensity

@[expose] public section
/-! The actual long-factor class supplies the fixed selected probabilities,
its two interval colours, and the full physical categorical probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_factor_concrete_sampling {U:Type} [Fintype U] {n:ℕ} (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρhi:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none):
    let fraction:=fun (u:U) (j:Option (Fin K))=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=j)).card:ℝ)/n
    let retained:=fun (u:U)=>Finset.univ.filter (fun i=>θ/(100*(K:ℝ))≤fraction u (some i))
    let f:=fun (i:Fin K) u=>if i∈retained u then fraction u (some i) else 0
    let c:ℝ:=(m:ℝ)+1
    let s₀:ℝ:=1/100
    let t:ℝ:=s₀/(m:ℝ)
    let a:=fun u=>(1-θ)*fraction u none/c-t
    let b:=fun u=>(m:ℝ)*a u+(1-θ)*∑ i,f i u
    let residual:=fun u=>1-s₀-t-a u-b u
    let q:=fun (u:U) (j:Bool)=>if j then a u else t
    let sco:=fun (u:U) (j:Bool)=>if j then b u else s₀
    let p₁:=ρ*s₀/2
    let k₁:=ρ*t/2
    let p₂:=(∑ u,b u)/D
    let k₂:=(∑ u,a u)/D
    let udens:=2*(∑ u,residual u)/D
    let kstar:=ρ₀*t/2
    let pstarRef:=ρ₀*t/8;
    (∀u,q u false=t ∧ sco u false=s₀) ∧
    (∀u j,0≤q u j) ∧ (∀u,∑j,q u j≤1/8) ∧
    (∀u j,0≤sco u j) ∧ (∀u,∑j,sco u j≤ intervalUncoveredProbability d (∑j,q u j)) ∧
    0<pstarRef ∧ pstarRef≤ρ₀*t/4 ∧ 0<t ∧ t≤s₀ ∧ t≤1 ∧
    0<kstar ∧ kstar≤p₁ ∧ kstar≤k₁ ∧ k₁=p₁/(m:ℝ) ∧
    0≤p₁ ∧ 0≤k₁ ∧ ρ₀/8≤p₂ ∧ ρ₀/(6*c)≤k₂ ∧ 0≤udens ∧
    2*p₁+2*k₁+2*p₂+2*k₂+udens=ρ ∧ 2*p₁+2*k₁+2*p₂+2*k₂+udens≤1 :=by
  intro fraction retained f c s₀ t a b residual q sco p₁ k₁ p₂ k₂ udens kstar pstarRef
  have hρ:0<ρ:=hρ₀.trans_le hρlo
  have hh:=long_assigned_factor_family_actual_marginals hn F hF Allowed hAllowed K hK m d hm hd θ ρ D
    hθ0 hθ hρ hρhi hD hsize hcut hclass
  have hden:=long_assigned_selected_density_uniform m hm ρ₀ ρ hρ₀ hρlo hρhi
  dsimp only at hh hden
  rcases hh with ⟨hw,hcol,hq,hQ,hs,hS,hp,hk,hp₂,hk₂,hu,hsum,hle,hkeq⟩
  rcases hden with ⟨hs₀,hss,ht,hts,htone,hkstar,hkp,hkk,hpstar,hpstarU,heq,_,_,_⟩
  refine ⟨fun u=>⟨(hcol u).1,(hcol u).2.2.1⟩,hq,hQ,hs,hS,?_,?_,?_,?_,?_,?_,?_,?_,?_,hp,hk,?_,?_,hu,hsum,hle⟩
  all_goals dsimp only [fraction,retained,f,c,s₀,t,a,b,residual,q,sco,p₁,k₁,p₂,k₂,udens,kstar,pstarRef]
  · exact hpstar
  · exact hpstarU
  · exact ht
  · exact hts
  · exact htone
  · exact hkstar
  · exact hkp
  · exact hkk
  · exact heq
  · exact (div_le_div_of_nonneg_right hρlo (by norm_num)).trans hp₂
  · exact (div_le_div_of_nonneg_right hρlo (by positivity)).trans hk₂
end Oberwolfach
