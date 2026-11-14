module

public import Oberwolfach.LongAssignedPreparationReferenceReady
public import Oberwolfach.PrunedLongClassReferenceInputs
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

theorem pruned_long_class_preparation_reference_ready (L₀:ℕ) (α:ℝ) (hα:0<α):
    ∃ m r k₀:ℕ,7≤m ∧ L₀≤m ∧ Even (m+1) ∧ 2≤r ∧ r+4=m ∧ r+4+1=(k₀+2)*2 ∧
      successorCycleRatio k₀+α/4≤1/2+α/2 ∧
    ∃ A BK:ℝ,0<A ∧ 0<BK ∧
    ∀ (K d:ℕ),0<K→2≤d→
    let nO:=fun i:Fin K=>max 1 (i.val-1);
    ∃ B:Fin K→ℝ,(∀ i,0<B i) ∧
    ∀ τ:ℝ,0<τ→∃ ε:ℝ,0<ε ∧ ε≤τ/4 ∧ ∃ N:ℕ,0<N ∧
    ∀ n:ℕ,N≤n→∀ {W:Type} [Fintype W]
      (F:W→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
      (Allowed:Set ℕ) (hAllowed:Allowed.Nonempty) (hvalid:∀ r∈Allowed,3≤r)
      (hS:∀w,AllowedCycleLengths (F w) Allowed)
      (D:ℕ) (hEven:Even D) (hsize:Fintype.card W=D/2) (hDn:D≤n)
      (δ κL κS:ℝ) (hδ:1/2≤δ) (hδA:allowedThreshold Allowed≤δ)
      (hL0:0<κL) (hS0:0<κS) (hL:κL≤(2*α)/1000) (hS0bound:κS≤(2*α)/(1000*(K:ℝ)))
      (hdegree:(δ+2*α)*(n:ℝ)≤D)
      (θ:ℝ) (hθ:0<θ) (hθmax:θ≤1/100)
      (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ),
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
    ∀ (G:SimpleGraph (Fin n)),G.IsRegularOfDegree D0→∀ (π:Equiv.Perm (Fin n)),
    let fraction:=fun (u:U) (i:Fin K)=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass (Fclass u) (hFclass u) K v=some i)).card:ℝ)/n
    let S:=Finset.univ.filter (fun i=>∃ u,θ/(100*(K:ℝ))≤fraction u i)
    let f:=fun (i:Fin K) u=>if θ/(100*(K:ℝ))≤fraction u i then fraction u i else 0
    let c:ℝ:=(m:ℝ)+1
    let t:ℝ:=(1/100)/(m:ℝ)
    let a:=fun u=>(1-θ)*(((Finset.univ.filter (fun v=>longPreparationCycleClass (Fclass u) (hFclass u) K v=none)).card:ℝ)/n)/c-t
    let b:=fun u=>(m:ℝ)*a u+(1-θ)*∑ i,f i u
    let ηS:=fun (i:↥S) u=>(1-θ)*f i.val u/b u
    let η:=padIndexedFunctions S (fun _=>U) ηS
    let p₂:=(∑ u,b u)/Dclass
    let k₂:=(∑ u,a u)/Dclass
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*c)))
    let residual:=fun u=>1-(1/100:ℝ)-t-a u-b u
    let q:=fun (u:U) (j:Bool)=>if j then a u else t
    let sco:=fun (u:U) (j:Bool)=>if j then b u else (1/100:ℝ)
    let p₁:=ρ*(1/100:ℝ)/2
    let k₁:=ρ*t/2
    let udens:=2*(∑ u,residual u)/Dclass
    let floor:=min (1/100:ℝ) pstar;
    ∃ w:∀ i:Fin K,OrdinaryCycle G (nO i+2)→ℝ,
    ∃ wK:(Fin (m+1)→Fin n)→ℝ,
      0<pstar ∧ pstar≤p₂ ∧ pstar≤k₂ ∧ (∀ u,pstar≤b u) ∧
      (∀ i u,η i u=(1-θ)*f i u/b u) ∧
      (∀ i∉S,∀ u,η i u=0) ∧
      (∀ i u,0≤η i u ∧ η i u≤1/b u) ∧
      (∀ u,(m:ℝ)*a u+(∑ i,η i u)*b u=b u) ∧
      (∑ u,a u)=Dclass*k₂ ∧ (∑ u,b u)=Dclass*p₂ ∧
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
        6*((nO i.val+2:ℕ):ℝ)^4*B i.val*(2*(3*d))+ε*(Fintype.card (Fin n):ℝ)≤τ*Dclass) ∧
      SuccessorSequenceWeightConditions G π (3*d) Dclass τ A BK wK :=by
  obtain ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmargin,A,BK,hA,hBK,hcore⟩:=long_assigned_preparation_actual_reference_ready L₀ α hα
  refine ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmargin,A,BK,hA,hBK,?_⟩
  intro K d hK hd nO
  obtain ⟨B,hB,hcore⟩:=hcore K d hK hd
  refine ⟨B,hB,?_⟩
  intro τ hτ
  obtain ⟨ε,hε,hετ,N,hN,hcore⟩:=hcore τ hτ
  refine ⟨ε,hε,hετ,N,hN,?_⟩
  intro n hn W _ F hF Allowed hAllowed hvalid hS D hEven hsize hDn δ κL κS hδ hδA hL0 hS0 hL hS0bound hdegree θ hθ hθmax hcut
    classify fibres cutoff small removed remaining cf D0 fibres0 C k e j hj U Fclass hFclass ρ₀ ρ Dclass G hG π
  have hnpos:0<n:=by omega
  have hin:=pruned_long_class_reference_inputs hnpos K hK F hF Allowed hS D hEven hsize hDn δ (2*α) κL κS
    hδ hδA (by positivity) hL0 hS0 hL hS0bound hdegree j hj
  obtain ⟨hD,hρ₀,hρlo,hρhi,hmass,hcls,hDlo,hDhi,hgraph⟩:=hin
  have hDreal:0<Dclass:=by dsimp [Dclass];exact_mod_cast hD
  have hAllowedClass:∀u:U,AllowedCycleLengths (Fclass u) Allowed:=fun u=>(hcls u).2.1
  have hclass:∀u:U,factorPreparationClass (Fclass u) K=none:=fun u=>(hcls u).2.2
  have hmarg:∀v,(allowedThreshold Allowed+α)*(n:ℝ)≤(G.degree v:ℝ):=by
    intro v
    have hh:=(hgraph G hG).1 v
    nlinarith [hh]
  have hreg:∀v,|(G.degree v:ℝ)-Dclass|≤ε*(n:ℝ):=(hgraph G hG).2 ε hε.le
  exact hcore n hn U Fclass hFclass Allowed hAllowed hvalid hAllowedClass θ ρ₀ ρ Dclass hθ hθmax hρ₀ hρlo hρhi hDreal hmass hcut hclass G π
    (by dsimp only [Dclass]; simpa only [Fintype.card_fin] using hDlo)
    (by dsimp only [Dclass]; simpa only [Fintype.card_fin] using hDhi) (by simpa using hreg) (by simpa using hmarg)
end Oberwolfach
