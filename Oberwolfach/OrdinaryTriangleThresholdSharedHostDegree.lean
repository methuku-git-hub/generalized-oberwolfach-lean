module

public import Oberwolfach.OrdinaryFullTriangleHostContinuationUniform
public import Oberwolfach.OrdinaryTriangleSharedHostDegreeEventually

@[expose] public section
/-! Choose the ordinary host weights before sampling, then use the same
expanded sample for the host event and physical class degree event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) triangleThresholdSharedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

def OrdinaryTriangleThresholdSharedHostDegreeContinuation {n:ℕ}
    (δ χ:ℝ) (d k:ℕ) (hd:2≤d) (P:SimpleGraph (Fin n))
    (θhost α pstar ω βP ηP ηH L βH c B ε:ℝ)
    (weight:OrdinaryCycle P 3→ℝ):Prop :=
  ∀{U:Type} [Fintype U] [DecidableEq U]
    (Factors:U→SimpleGraph (Fin n)) (hFactors:∀w,(Factors w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θfreq caux ρ D:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθfreq:0<θfreq) (hθfreq1:θfreq≤1/100) (hcaux:8≤caux)
    (hda:1/θfreq≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (Factors w) S)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,factorPreparationClass (Factors w) K=some i₀)
    (Conflict:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (hUlo:ω*n≤(Fintype.card U:ℝ)) (hUhi:Fintype.card U≤n)
    (hFdeg:∀v,(Conflict.degree v:ℝ)≤L) (hF:permutationConflictGraph π (3*d)≤Conflict)
    (hπ:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hRlo:pstar≤ρ*rsv) (hRhi:ρ*rsv≤1) (hHlo:pstar≤rsv) (hHhi:rsv≤1)
    (hDlo:(n:ℝ)/2≤D) (hnear:∀v,|(P.degree v:ℝ)-D|≤ε*n)
    (p₂ u:ℝ) (hp₂:0≤p₂) (hu:0≤u) (hstates:ρ*rsv+p₂+u=ρ),
    let q:=ordinaryAssignedMarkedProbability Factors hFactors K θfreq caux
    let s:=ordinaryAssignedSpokeProbability Factors hFactors K i₀ rsv θfreq caux;
    ∃ (hq:∀w j,0≤q w j) (hQ:∀w,∑j,q w j≤1/8)
      (hs:∀w j,0≤s w j) (hSc:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑j,q w j)),
    ∀{R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) ((ρ*rsv)/2) 0 (p₂/2) 0 u
      (by positivity) (by norm_num) (by positivity) (by norm_num) hu (by linarith) d hd q hq hQ s hs hSc);
    1-χ≤(μ.sigma ν).probability (fun z=>
      ordinaryCombinedTriangleEvent d k P Conflict π θhost α pstar βP ηP ηH βH c B (ρ*rsv) rsv weight false
        (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) ∧
      ∀v,|((longPhysicalStateGraph P z.1 {0,1,2,3,4}).degree v:ℝ)-ρ*(P.degree v:ℝ)|<δ*n)

theorem ordinary_triangle_threshold_shared_host_degree
    (d:ℕ) (hd:2≤d) (θ α pstar ω βP ηP ηH L:ℝ)
    (hθ:cycleThreshold 3≤θ) (hα:0<α) (hα1:α≤1) (hθ1:θ+α/2≤1)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω)
    (hβP:0<βP) (hβmax:βP≤2*(min (α/2) (1/4))*pstar^4*pstar^4)
    (hβhub:βP≤ω*pstar^9/4) (hηP:0<ηP) (hηH:0<ηH) (hL:0≤L)
    (δ χ:ℝ) (hδ:0<δ) (hχ:0<χ):
    ∃ (k:ℕ) (βH c B ε:ℝ),5≤k ∧ 0<βH ∧ 0<c ∧ 0<B ∧ 0<ε ∧ ∃N:ℕ,
    ∀n≥N,∀P:SimpleGraph (Fin n),(∀v,(θ+α)*n≤(P.degree v:ℝ))→
    ∃weight:OrdinaryCycle P 3→ℝ,
      (∀C,c/(n:ℝ)^(3-2)≤weight C ∧ weight C≤B/(n:ℝ)^(3-2)) ∧
      (∀x y,(∑C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) ∧
      OrdinaryTriangleThresholdSharedHostDegreeContinuation δ χ d k hd P θ α pstar ω βP ηP ηH L βH c B ε weight :=by
  obtain ⟨k,βH,c,B,ε,hk,hβH,hc,hB,hε,Nhost,hHost⟩:=ordinary_full_triangle_host_continuation_uniform
    d hd θ α pstar ω βP ηP ηH L hθ hα hα1 hθ1 hpstar hpstar1 hω
    hβP hβmax hβhub hηP hηH hL
  obtain ⟨Nevent,hNevent,hEvent⟩:=ordinary_triangle_shared_host_degree_eventually δ χ hδ hχ
  refine ⟨k,βH,c,B,ε,hk,hβH,hc,hB,hε,max Nhost Nevent,?_⟩
  intro n hn P hP
  obtain ⟨weight,hw,hedge,hcont⟩:=hHost (Fin n) (by simpa using (show Nhost≤n by omega)) P (by simpa using hP)
  refine ⟨weight,by simpa using hw,hedge,?_⟩
  intro U _ _ Factors hFactors K hK i₀ rsv θfreq caux ρ D hs0 hs1 hθfreq hθfreq1 hcaux hda hρ hρ1 hD hsize S hS hsclass hclass Conflict π hUlo hUhi hFdeg hF hπ hRlo hRhi hHlo hHhi hDlo hnear p₂ u hp₂ hu hstates q s
  have hh:=hEvent (by omega : Nevent≤n) Factors hFactors K hK i₀ rsv θfreq caux ρ D d hd
    hs0 hs1 hθfreq hθfreq1 hcaux hda hρ hρ1 hD hsize S hS hsclass hclass k P Conflict π
    θ α pstar ω βP ηP ηH L βH c B ε weight hpstar hcont hUlo hUhi hFdeg hF hπ hRlo hRhi hHlo hHhi hDlo hnear p₂ u hp₂ hu hstates
  convert hh using 1 <;> congr!
end Oberwolfach
