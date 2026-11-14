module

public import Oberwolfach.LongPreparationActualFamily
public import Oberwolfach.LongPreparationConcreteMarginals

@[expose] public section
/-! Concrete fixed hub coefficients for the short ordinary wheels, with
normalisation and the densities required by the seeded-root estimates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_factor_family_seed_coefficients {U:Type} [Fintype U] {n:ℕ} (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀ u,(F u).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hlong:∀ u,(1/2:ℝ)≤
      ((Finset.univ.filter (fun v=>K<Fintype.card ((F u).connectedComponentMk v))).card:ℝ)/n):
    let fraction:=fun (u:U) (j:Option (Fin K))=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=j)).card:ℝ)/n
    let retained:=fun (u:U)=>Finset.univ.filter (fun i=>θ/(100*(K:ℝ))≤fraction u (some i))
    let f:=fun (i:Fin K) u=>if i∈retained u then fraction u (some i) else 0
    let c:ℝ:=(m:ℝ)+1
    let t:ℝ:=(1/100)/(m:ℝ)
    let a:=fun u=>(1-θ)*fraction u none/c-t
    let b:=fun u=>(m:ℝ)*a u+(1-θ)*∑ i,f i u
    let η:=fun i u=>(1-θ)*f i u/b u
    let p:=(∑ u,b u)/D
    let k:=(∑ u,a u)/D
    let pstar:=min (1/4:ℝ) (min (ρ/8) (ρ/(6*c)));
    0<pstar ∧ pstar≤p ∧ pstar≤k ∧ (∀ u,pstar≤b u) ∧
    (∀ i u,0≤η i u ∧ η i u≤1/b u) ∧
    (∀ u,(m:ℝ)*a u+(∑ i,η i u)*b u=b u) ∧
    (∑ u,a u)=D*k ∧ (∑ u,b u)=D*p:=by
  intro fraction retained f c t a b η p k pstar
  have hc:0<c:=by dsimp [c];positivity
  have hm0:(0:ℝ)≤m:=by positivity
  have hpstar0:0<pstar:=by dsimp [pstar];positivity
  have hpstarb:pstar≤1/4:=min_le_left _ _
  have hpstarp:pstar≤ρ/8:=le_trans (min_le_right _ _) (min_le_left _ _)
  have hpstark:pstar≤ρ/(6*c):=le_trans (min_le_right _ _) (min_le_right _ _)
  have hsize':ρ*D/2≤(Fintype.card U:ℝ):=by nlinarith [hsize]
  have hfamily:=long_preparation_family_fractions hn F hF K hK θ hθ0 hlong
  have hf:∀ i u,0≤f i u:=by simpa [fraction,retained,f] using hfamily.2.2.1
  have hmarg:=long_preparation_factor_family_actual_marginals hn F hF K hK m d hm hd θ ρ D hθ0 hθ hρ hρ1 hD hsize hcut hlong
  have hbounds:∀ u,1/(3*c)≤a u ∧ 1/4≤b u ∧ b u≤1:=by
    intro u
    have hh:=hmarg.1 u
    exact ⟨hh.1,hh.2.1,hh.2.2.1⟩
  have ha:∀ u,1/(3*c)≤a u:=fun u=>(hbounds u).1
  have hb:∀ u,1/4≤b u ∧ b u≤1:=fun u=>(hbounds u).2
  have hdef:∀ u,b u=(m:ℝ)*a u+(1-θ)*∑ i,f i u:=by intro u;rfl
  have hh:=long_preparation_concrete_marginals D ρ c (m:ℝ) θ pstar hD hρ hc hm0 (by linarith)
    hpstar0 hpstarb hpstarp hpstark a b f ha hb hf hsize' hdef
  exact ⟨hpstar0,by simpa [η,p,k] using hh⟩
end Oberwolfach
