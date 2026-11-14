module

public import Oberwolfach.PreparationActualReferenceReady
public import Oberwolfach.LongAssignedClassReservation
public import Oberwolfach.PreparationActualPaddedFamilyWithMarginals
public import Oberwolfach.MarkedPreparationReferenceLength

@[expose] public section
/-! The actual factor-family sampling and weight inputs use a marked length
which also satisfies the all-level reference theorem's density margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_preparation_actual_reference_ready (L₀:ℕ) (α:ℝ) (hα:0<α):
    ∃ m r k₀:ℕ,7≤m ∧ L₀≤m ∧ Even (m+1) ∧ 2≤r ∧ r+4=m ∧ r+4+1=(k₀+2)*2 ∧
      successorCycleRatio k₀+α/4≤1/2+α/2 ∧
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
      (hclass:∀u,factorPreparationClass (F u) K=none)
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
      SuccessorSequenceWeightConditions G π (3*d) D τ A BK wK :=by
  obtain ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmargin,A,BK,hA,hBK,hcore⟩:=preparation_actual_reference_ready L₀ α hα
  refine ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmargin,A,BK,hA,hBK,?_⟩
  intro K d hK hd nO
  obtain ⟨B,hB,hcore⟩:=hcore K d hK hd
  refine ⟨B,hB,?_⟩
  intro τ hτ
  obtain ⟨ε,hε,hετ,N,hN,hcore⟩:=hcore τ hτ
  refine ⟨ε,hε,hετ,N,hN,?_⟩
  intro n hn U _ F hF Allowed hAllowed hvalid hS θ ρ₀ ρ D hθ hθmax hρ₀ hρlo hρ1 hD hsize hcut hclass G π hDlo hDhi hreg hdeg
  have hnpos:0<n:=by omega
  have hlong:=long_class_assigned_frequency hnpos F hF Allowed hS K hK hclass
  exact hcore n hn U F hF Allowed hAllowed hvalid hS θ ρ₀ ρ D hθ hθmax hρ₀ hρlo hρ1 hD hsize hcut hlong G π hDlo hDhi hreg hdeg
end Oberwolfach
