module

public import Oberwolfach.PreparationPaddedWeightsFromAllowed
public import Oberwolfach.LongPreparationUniformFamilySeeds
public import Oberwolfach.RetainedCoefficientPadding
public import Oberwolfach.TwoColourUniformSeedFloor

@[expose] public section
/-! The actual factor family supplies its retained lengths, fixed hub
coefficients and cycle weights on a fixed ambient index set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem preparation_actual_padded_family_with_marginals
    (L:ℕ) (hL:7≤L) (α:ℝ) (hα:0<α):
    ∃ m:ℕ,7≤m ∧ L≤m ∧ Even (m+1) ∧
    ∃ A BK:ℝ,0<A ∧ 0<BK ∧
    ∀ (K d:ℕ),0<K→2≤d→
    let nO:=fun i:Fin K=>max 1 (i.val-1);
    ∃ B:Fin K→ℝ,(∀ i,0<B i) ∧
    ∀ τ:ℝ,0<τ→∃ ε:ℝ,0<ε ∧ ε≤τ/4 ∧ ∃ N:ℕ,0<N ∧
    ∀ n:ℕ,N≤n→∀ (U:Type) [Fintype U]
      (F:U→SimpleGraph (Fin n)) (hF:∀ u,(F u).IsRegularOfDegree 2)
      (Allowed:Set ℕ) (hAllowed:Allowed.Nonempty) (hvalid:∀ r∈Allowed,3≤r)
      (hS:∀ u,AllowedCycleLengths (F u) Allowed)
      (θ ρ₀ ρ D:ℝ) (hθ:0<θ) (hθmax:θ≤1/100) (hρ₀:0<ρ₀)
      (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*Fintype.card U)
      (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
      (hlong:∀ u,(1/2:ℝ)≤((Finset.univ.filter (fun v=>K<Fintype.card ((F u).connectedComponentMk v))).card:ℝ)/n)
      (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
      (hDlo:(Fintype.card (Fin n):ℝ)/2≤D) (hDhi:D≤2*Fintype.card (Fin n))
      (hreg:∀ v,|(G.degree v:ℝ)-D|≤ε*Fintype.card (Fin n))
      (hdeg:∀ v,(allowedThreshold Allowed+α)*Fintype.card (Fin n)≤(G.degree v:ℝ)),
    let fraction:=fun (u:U) (i:Fin K)=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i)).card:ℝ)/n
    let S:=Finset.univ.filter (fun i=>∃ u,θ/(100*(K:ℝ))≤fraction u i)
    let f:=fun (i:Fin K) u=>if θ/(100*(K:ℝ))≤fraction u i then fraction u i else 0
    let c:ℝ:=(m:ℝ)+1
    let t:ℝ:=(1/100)/(m:ℝ)
    let a:=fun u=>(1-θ)*(((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=none)).card:ℝ)/n)/c-t
    let b:=fun u=>(m:ℝ)*a u+(1-θ)*∑ i,f i u
    let ηS:=fun (i:↥S) u=>(1-θ)*f i.val u/b u
    let η:=padIndexedFunctions S (fun _=>U) ηS
    let p₂:=(∑ u,b u)/D
    let k₂:=(∑ u,a u)/D
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*c)))
    let residual:=fun u=>1-(1/100:ℝ)-t-a u-b u
    let q:=fun (u:U) (j:Bool)=>if j then a u else t
    let sco:=fun (u:U) (j:Bool)=>if j then b u else (1/100:ℝ)
    let p₁:=ρ*(1/100:ℝ)/2
    let k₁:=ρ*t/2
    let udens:=2*(∑ u,residual u)/D
    let floor:=min (1/100:ℝ) pstar;
    ∃ w:∀ i:Fin K,OrdinaryCycle G (nO i+2)→ℝ,
    ∃ wK:(Fin (m+1)→Fin n)→ℝ,
      0<pstar ∧ pstar≤p₂ ∧ pstar≤k₂ ∧ (∀ u,pstar≤b u) ∧
      (∀ i u,η i u=(1-θ)*f i u/b u) ∧
      (∀ i∉S,∀ u,η i u=0) ∧
      (∀ i u,0≤η i u ∧ η i u≤1/b u) ∧
      (∀ u,(m:ℝ)*a u+(∑ i,η i u)*b u=b u) ∧
      (∑ u,a u)=D*k₂ ∧ (∑ u,b u)=D*p₂ ∧
      0<floor ∧ floor≤p₂ ∧ floor≤k₂ ∧ (∀ u j,floor≤sco u j) ∧
      (∀ u,q u false=t ∧ q u true=a u ∧ sco u false=1/100 ∧ sco u true=b u) ∧
      (∀ u j,0≤q u j) ∧ (∀ u,∑ j,q u j≤1/8) ∧
      (∀ u j,0≤sco u j) ∧ (∀ u,∑ j,sco u j ≤ intervalUncoveredProbability d (∑ j,q u j)) ∧
      0≤p₁ ∧ 0≤k₁ ∧ 0≤udens ∧ 2*p₁+2*k₁+2*p₂+2*k₂+udens=ρ ∧
      2*p₁+2*k₁+2*p₂+2*k₂+udens≤1 ∧ k₁=p₁/(m:ℝ) ∧
      (∀ i C,0≤w i C ∧ w i C≤B i/(Fintype.card (Fin n):ℝ)^(nO i)) ∧
      (∀ i:↥S,∀ x y,(∑ C,if C.val.val.Adj x y then w i.val C else 0)=if G.Adj x y then 1 else 0) ∧
      (∀ i∉S,∀ C,w i C=0) ∧
      (∀ i:↥S,5*((nO i.val+2:ℕ):ℝ)^4*B i.val*(2*(3*d))/Fintype.card (Fin n)≤τ ∧
        6*((nO i.val+2:ℕ):ℝ)^4*B i.val*(2*(3*d))+ε*(Fintype.card (Fin n):ℝ)≤τ*D) ∧
      SuccessorSequenceWeightConditions G π (3*d) D τ A BK wK:=by
  obtain ⟨m,hm,hLm,heven,A,BK,hA,hBK,hW⟩:=preparation_padded_weights_from_allowed_threshold L α hα
  refine ⟨m,by omega,hLm,heven,A,BK,hA,hBK,?_⟩
  intro K d hK hd nO
  have hnO:∀ i,1≤nO i:=by intro i;exact le_max_left _ _
  obtain ⟨B,hB,hW⟩:=hW K d hd nO hnO
  refine ⟨B,hB,?_⟩
  intro τ hτ
  obtain ⟨ε,hε,hετ,N,hN,hW⟩:=hW τ hτ
  refine ⟨ε,hε,hετ,N,hN,?_⟩
  intro n hn U _ F hF Allowed hAllowed hvalid hS θ ρ₀ ρ D hθ hθmax hρ₀ hρlo hρ1 hD hsize hcut hlong G π hDlo hDhi hreg hdeg
    fraction S f c t a b ηS η p₂ k₂ pstar residual q sco p₁ k₁ udens floor
  have hnpos:0<n:=by omega
  have hmem:∀ i:↥S,nO i.val+2∈Allowed:=by
    have hi:=long_preparation_seed_indices hnpos F hF Allowed hS K hK θ hθ
    intro i
    exact (hi.2 i.val i.property).2
  obtain ⟨w,wK,hw,he,hzero,hbudget,hwK⟩:=hW (Fin n) (by simpa using hn) S Allowed G π D hAllowed hvalid hDlo hDhi hreg hmem hdeg
  have hseed:=long_preparation_uniform_family_seed_coefficients hnpos F hF K hK m d (by omega) hd θ ρ₀ ρ D
    hθ.le hθmax hρ₀ hρlo hρ1 hD hsize hcut hlong
  have hηS:∀ i:↥S,∀ u,0≤ηS i u ∧ ηS i u≤1/b u:=hseed.2.2.2.2.1
  have hbpos:∀ u,0<b u:=fun u=>hseed.1.trans_le (hseed.2.2.2.1 u)
  have hη:∀ i u,0≤η i u ∧ η i u≤1/b u:=by
    apply pad_indexed_functions_pointwise_bounds S (fun _=>U) ηS (fun _ u=>1/b u)
    · intro i u;have hu:=hbpos u;positivity
    · exact hηS
  have hbalance:∀ u,(m:ℝ)*a u+(∑ i,η i u)*b u=b u:=by
    intro u
    rw [pad_indexed_functions_sum S ηS u]
    exact hseed.2.2.2.2.2.1 u
  have hηexact:∀ i u,η i u=(1-θ)*f i u/b u:=
    retained_coefficient_padding fraction (θ/(100*(K:ℝ))) θ b
  have hMarg:=long_preparation_factor_family_actual_marginals hnpos F hF K hK m d (by omega) hd θ ρ D hθ.le hθmax
    (hρ₀.trans_le hρlo) hρ1 hD hsize hcut hlong
  have hMarg':(∀ u,q u false=t ∧ q u true=a u ∧ sco u false=1/100 ∧ sco u true=b u) ∧
      (∀ u j,0≤q u j) ∧ (∀ u,∑ j,q u j≤1/8) ∧
      (∀ u j,0≤sco u j) ∧ (∀ u,∑ j,sco u j ≤ intervalUncoveredProbability d (∑ j,q u j)) ∧
      0≤p₁ ∧ 0≤k₁ ∧ ρ/8≤p₂ ∧ ρ/(6*c)≤k₂ ∧ 0≤udens ∧
      2*p₁+2*k₁+2*p₂+2*k₂+udens=ρ ∧ 2*p₁+2*k₁+2*p₂+2*k₂+udens≤1 ∧ k₁=p₁/(m:ℝ):=by
    dsimp only [fraction,f,c,t,a,b,residual,q,sco,p₁,k₁,p₂,k₂,udens]
    simpa [Finset.mem_filter] using hMarg.2
  have hfloor:=two_colour_uniform_seed_floor (1/100) pstar p₂ k₂ b (by norm_num) hseed.1 hseed.2.1 hseed.2.2.1 hseed.2.2.2.1
  have hηzero:∀ i∉S,∀ u,η i u=0:=by
    intro i hi u
    exact pad_indexed_functions_off S (fun _=>U) ηS i hi u
  refine ⟨w,wK,hseed.1,hseed.2.1,hseed.2.2.1,hseed.2.2.2.1,hηexact,hηzero,hη,hbalance,hseed.2.2.2.2.2.2.1,
    hseed.2.2.2.2.2.2.2,hfloor.1,hfloor.2.1,hfloor.2.2.1,hfloor.2.2.2,?_⟩
  exact ⟨hMarg'.1,hMarg'.2.1,hMarg'.2.2.1,hMarg'.2.2.2.1,hMarg'.2.2.2.2.1,
    hMarg'.2.2.2.2.2.1,hMarg'.2.2.2.2.2.2.1,hMarg'.2.2.2.2.2.2.2.2.2.1,
    hMarg'.2.2.2.2.2.2.2.2.2.2.1,hMarg'.2.2.2.2.2.2.2.2.2.2.2.1,hMarg'.2.2.2.2.2.2.2.2.2.2.2.2,hw,he,hzero,hbudget,hwK⟩
end Oberwolfach
