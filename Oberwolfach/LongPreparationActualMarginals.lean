module

public import Oberwolfach.LongPreparationTwoColourMarginals
public import Oberwolfach.LongPreparationMarginalBounds
public import Oberwolfach.LongPreparationResidualIdentity
public import Oberwolfach.LongPreparationPhysicalFeasible
public import Oberwolfach.LongPreparationDensityBounds
public import Oberwolfach.LongPreparationSelectedDensities

@[expose] public section
/-! The long preparation's two interval colours and five physical states,
derived directly from the component fractions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_actual_marginals {U I:Type} [Fintype U] [Fintype I]
    (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U)
    (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (ℓ rare:U→ℝ) (f:I→U→ℝ)
    (hℓ:∀ u,1/2≤ℓ u ∧ ℓ u≤1) (hrare:∀ u,0≤rare u ∧ rare u≤θ/100)
    (hf:∀ i u,0≤f i u) (hfractions:∀ u,ℓ u+(∑ i,f i u)+rare u=1):
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
  intro c s₀ t a b residual q s p k p₂ k₂ udens
  have hmR:(7:ℝ)≤m:=by exact_mod_cast hm
  have hc:8≤c:=by dsimp [c];linarith
  have hc0:0<c:=by linarith
  have hm0:(0:ℝ)<m:=by linarith
  have ht0:0≤t:=by dsimp [t,s₀];positivity
  have hf0:∀ u,0≤∑ i,f i u:=fun u=>Finset.sum_nonneg (fun i _=>hf i u)
  have hbound (v:U):1/(3*c)≤a v ∧ 1/4≤b v ∧ t+a v≤1/c:=by
    have hh:=long_preparation_marginal_bounds c θ (ℓ v) (∑ i,f i v) (by linarith) hθ0 hθ (hℓ v).1 (hℓ v).2 (hf0 v)
    dsimp only at hh
    have hcm:c-1=(m:ℝ):=by dsimp [c];ring
    rw [hcm] at hh
    exact hh
  have ha0:∀ v,0≤a v:=by
    intro v
    have hh:0≤1/(3*c):=by positivity
    exact hh.trans (hbound v).1
  have hb0:∀ v,0≤b v:=by intro v;have hh:=(hbound v).2.1;linarith
  have hident (v:U):residual v=θ+(1-θ)*rare v:=by
    have hh:=long_preparation_residual_identity c θ (ℓ v) (∑ i,f i v) (rare v) s₀ (by linarith) (hfractions v)
    dsimp only at hh
    have hcm:c-1=(m:ℝ):=by dsimp [c];ring
    rw [hcm] at hh
    exact hh
  have hres (v:U):0≤residual v ∧ residual v≤2*θ ∧ (t+a v)/(d:ℝ)≤residual v:=by
    have hq0:0≤t+a v:=add_nonneg ht0 (ha0 v)
    have hh:=long_preparation_residual_bounds θ (rare v) (t+a v) c d hθ0 (by linarith) (hrare v).1 (hrare v).2 hq0 (hbound v).2.2 (by positivity) hcut
    dsimp only at hh
    rw [hident]
    exact ⟨le_trans hθ0 hh.1,hh.2.1,hh.2.2⟩
  have hb1 (v:U):b v≤1:=by
    have hh:=(hres v).1
    have hs0:0≤s₀:=by dsimp [s₀];norm_num
    dsimp [residual] at hh
    linarith [ha0 v]
  have hinterval:∀ v,t+a v≤1/8:=by
    intro v
    have hc8:1/c≤(1/8:ℝ):=one_div_le_one_div_of_le (by norm_num) hc
    exact (hbound v).2.2.trans hc8
  have hrest:∀ v,(t+a v)/(d:ℝ)≤1-s₀-t-a v-b v:=fun v=>(hres v).2.2
  have hinter:=long_preparation_two_colour_marginals d m hd (by omega) s₀ (by dsimp [s₀];norm_num) a b ha0 hb0 hinterval hrest
  dsimp only at hinter
  have hphys:=long_preparation_physical_feasible D ρ s₀ t hD hρ.le hρ1 (by dsimp [s₀];norm_num) ht0 a b ha0 hb0 (fun v=>(hres v).1) hsize
  dsimp only at hphys
  have hsize':ρ*D/2≤(Fintype.card U:ℝ):=by nlinarith [hsize]
  have hden:=long_preparation_density_bounds D ρ c hD hρ hc0 a b (fun v=>(hbound v).1) (fun v=>(hbound v).2.1) hsize'
  refine ⟨?_,hinter.1,hinter.2.1,hinter.2.2.1,hinter.2.2.2.1,hinter.2.2.2.2,
    hphys.1,hphys.2.1,hden.1,hden.2,hphys.2.2.2.2.1,hphys.2.2.2.2.2.1,hphys.2.2.2.2.2.2,?_⟩
  · intro v
    exact ⟨(hbound v).1,(hbound v).2.1,hb1 v,(hres v).1,(hres v).2.1,(hres v).2.2⟩
  · dsimp [p,k,t]
    exact long_preparation_selected_density_identity ρ s₀ m (by omega)
end Oberwolfach
