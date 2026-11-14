module

public import Oberwolfach.LongAssignedConcreteSampling
public import Oberwolfach.PrunedClassDensityIdentities

@[expose] public section
/-! The actual nonempty retained long class supplies the exact two-colour
sampling law and density-uniform selected probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem pruned_long_class_concrete_sampling {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
    (K:ℕ) (hK:0<K) (F:W→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (D:ℕ) (hEven:Even D) (hsize:Fintype.card W=D/2) (hDn:D≤n)
    (δ α κL κS:ℝ) (hδ:0≤δ) (hα:0<α)
    (hL0:0<κL) (hS0:0<κS) (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ)))
    (hdegree:(δ+α)*(n:ℝ)≤D)
    (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ:ℝ) (hθ0:0≤θ) (hθ:θ≤1/100)
    (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ):
    let classify:=fun w=>factorPreparationClass (F w) K
    let fibres:=fun j:Option (Fin K)=>Finset.univ.filter (fun w=>classify w=j)
    let cutoff:=fun j:Option (Fin K)=>if j=none then κL else κS
    let small:=fun j:Option (Fin K)=>((fibres j).card:ℝ)<cutoff j*n
    let removed:=Finset.univ.filter (fun w=>small (classify w))
    let remaining:={w:W // w∉removed}
    let cf:=fun w:remaining=>classify w.val
    let D0:=D-2*removed.card
    let fibres0:=fun j:Option (Fin K)=>Finset.univ.filter (fun w:remaining=>cf w=j)
    let C:=Finset.univ.filter (fun j=>(fibres0 j).Nonempty)
    let k:=C.card
    let e:Fin k≃↥C:=(Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm;
    ∀ j:Fin k,(e j).val=none→
    let U:Type:={w:remaining // cf w=(e j).val}
    let Fclass:=fun u:U=>F u.1.1
    let hFclass:=fun u:U=>hF u.1.1
    let ρ₀:ℝ:=2*min κL κS
    let ρ:=initialIndexDensity U D0
    let Dclass:ℝ:=D0;
    let fraction:=fun (u:U) (j:Option (Fin K))=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass (Fclass u) (hFclass u) K v=j)).card:ℝ)/n
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
    let p₂:=(∑ u,b u)/Dclass
    let k₂:=(∑ u,a u)/Dclass
    let udens:=2*(∑ u,residual u)/Dclass
    let kstar:=ρ₀*t/2
    let pstarRef:=ρ₀*t/8;
    (∀u,q u false=t ∧ sco u false=s₀) ∧
    (∀u j,0≤q u j) ∧ (∀u,∑j,q u j≤1/8) ∧
    (∀u j,0≤sco u j) ∧ (∀u,∑j,sco u j≤ intervalUncoveredProbability d (∑j,q u j)) ∧
    0<pstarRef ∧ pstarRef≤ρ₀*t/4 ∧ 0<t ∧ t≤s₀ ∧ t≤1 ∧
    0<kstar ∧ kstar≤p₁ ∧ kstar≤k₁ ∧ k₁=p₁/(m:ℝ) ∧
    0≤p₁ ∧ 0≤k₁ ∧ ρ₀/8≤p₂ ∧ ρ₀/(6*c)≤k₂ ∧ 0≤udens ∧
    2*p₁+2*k₁+2*p₂+2*k₂+udens=ρ ∧ 2*p₁+2*k₁+2*p₂+2*k₂+udens≤1 :=by
  intro classify fibres cutoff small removed remaining cf D0 fibres0 C k e j hj U Fclass hFclass ρ₀ ρ Dclass
  have hdens:=factor_pruned_initial_index_densities hn K hK classify D hEven hsize hDn δ α κL κS
    hδ hα hL0 hS0 hL hS hdegree
  have hid:=factor_pruned_actual_density_identities hn K hK classify D hEven hsize hDn δ α κL κS
    hδ hα hL0 hS0 hL hS hdegree
  have hρ₀:0<ρ₀:=by dsimp [ρ₀];positivity
  have hρlo:ρ₀≤ρ:=(hdens.2.2.2.2 j).1
  have hρhi:ρ≤1:=(hdens.2.2.2.2 j).2
  have hD:0<Dclass:=by dsimp [Dclass];exact_mod_cast hdens.1
  have hmass:ρ*Dclass=2*Fintype.card U:=by
    have heq:ρ=2*((fibres0 (e j).val).card:ℝ)/D0:=(hid j).1.symm
    rw [heq]
    exact (hid j).2
  have hallow:∀u:U,AllowedCycleLengths (Fclass u) Allowed:=fun u=>hAllowed u.1.1
  have hclass:∀u:U,factorPreparationClass (Fclass u) K=none:=by
    intro u
    change classify u.1.1=none
    exact u.2.trans hj
  exact long_assigned_factor_concrete_sampling hn Fclass hFclass Allowed hallow K hK m d hm hd θ ρ₀ ρ Dclass
    hθ0 hθ hρ₀ hρlo hρhi hD hmass hcut hclass
end Oberwolfach
