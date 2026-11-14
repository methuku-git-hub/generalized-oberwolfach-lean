module

public import Oberwolfach.OrdinaryAssignedHostDegreePrescribedEventually
public import Oberwolfach.OrdinaryFullHostContinuationUniform

@[expose] public section
/-! Choose host weights and the prescribed-packing scale before the sample;
the assigned-factor event then uses its own exact physical probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) ordinaryHostPrescribedUniformFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

def OrdinaryAssignedPrescribedHostContinuation {n:ℕ}
    (δ χ γ αpack:ℝ) (m d k:ℕ) (hm:3≤m) (hd:2≤d) (P:SimpleGraph (Fin n))
    (θhost αhost pstar ω βP ηP row ηH L βH c B ε:ℝ)
    (weight:OrdinaryCycle P (m+1)→ℝ):Prop :=
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
    ,
    ∃(p p₂ u:ℝ) (hp:0≤p) (hp₂:0≤p₂) (hu:0≤u)
      (hsum:2*p+2*p₂+u=ρ) (hpEq:2*p=ρ*rsv), ρ/4≤p₂ ∧
      p₂*D=∑w,(ordinaryAssignedLongWeight Factors hFactors K θfreq caux w+
        ordinaryAssignedShortWeight Factors hFactors K i₀ rsv θfreq caux w) ∧
      u*D=2*∑w,(1-rsv-ordinaryAssignedLongWeight Factors hFactors K θfreq caux w-
        ordinaryAssignedShortWeight Factors hFactors K i₀ rsv θfreq caux w) ∧
    let q:=ordinaryAssignedMarkedProbability Factors hFactors K θfreq caux
    let s:=ordinaryAssignedSpokeProbability Factors hFactors K i₀ rsv θfreq caux;
    ∃ (hq:∀w j,0≤q w j) (hQ:∀w,∑j,q w j≤1/8)
      (hs:∀w j,0≤s w j) (hSc:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑j,q w j)),
    ∀{R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) ((ρ*rsv)/2) 0 ((2*p₂)/2) 0 u
      (by positivity) (by norm_num) (by positivity) (by norm_num) hu (by linarith) d hd q hq hQ s hs hSc);
    1-χ≤(μ.sigma ν).probability (fun z=>
      (ordinaryCombinedHostEvent m d k hm P Conflict π θhost αhost pstar βP ηP row ηH βH c B (ρ*rsv) rsv weight s false
        (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) ∧
       (∀v,|((longPhysicalStateGraph P z.1 {0,1,2,3,4}).degree v:ℝ)-ρ*(P.degree v:ℝ)|<δ*n)) ∧
      OrdinaryPrescribedPackingEvent (m+1) d pstar γ αpack P Conflict π Finset.univ Finset.univ false
        (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)))

theorem ordinary_threshold_assigned_prescribed_host
    (m d:ℕ) (hm:3≤m) (hd:2≤d) (θ α pstar ω βP ηP row ηH L:ℝ)
    (hθ:cycleThreshold (m+1)≤θ) (hα:0<α) (hα1:α≤1) (hθ1:θ+α/2≤1)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω)
    (hβP:0<βP) (hβmax:βP≤(α/2)*pstar^2*pstar^2)
    (hβhub:βP≤ω*pstar^(m+7)/4) (hηP:0<ηP) (hrow:0<row)
    (hrowmax:row≤pstar^(m+7)/2) (hηH:0<ηH) (hL:0≤L)
    (δ χ:ℝ) (hδ:0<δ) (hχ:0<χ):
    ∃ (k:ℕ) (βH c B ε αpack:ℝ),m+3≤k ∧ 0<βH ∧ 0<c ∧ 0<B ∧ 0<ε ∧ 0<αpack ∧ ∃N:ℕ,
    ∀n≥N,∀P:SimpleGraph (Fin n),(∀v,(θ+α)*n≤(P.degree v:ℝ))→
    ∃weight:OrdinaryCycle P (m+1)→ℝ,
      (∀C,c/(n:ℝ)^((m+1)-2)≤weight C ∧ weight C≤B/(n:ℝ)^((m+1)-2)) ∧
      (∀x y,(∑C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) ∧
      OrdinaryAssignedPrescribedHostContinuation δ χ (α/2) αpack m d k hm hd P θ α pstar ω βP ηP row ηH L βH c B ε weight :=by
  obtain ⟨k,βH,c,B,ε,hk,hβH,hc,hB,hε,Nhost,hHost⟩:=ordinary_full_host_continuation_uniform
    m d hm hd θ α pstar ω βP ηP row ηH L hθ hα hα1 hθ1 hpstar hpstar1 hω
    hβP hβmax hβhub hηP hrow hrowmax hηH hL
  obtain ⟨α₀,hα₀,hα₁,hPack⟩:=ordinary_assigned_host_degree_prescribed_eventually m hm pstar (α/2) ω hpstar hpstar1 (by positivity) (by linarith) hω δ χ hδ hχ
  obtain ⟨Npack,hNpack⟩:=hPack (α₀/2) L (by positivity) (by linarith) hL d hd
  refine ⟨k,βH,c,B,ε,α₀/2,hk,hβH,hc,hB,hε,by positivity,max 1 (max Nhost Npack),?_⟩
  intro n hn P hP
  have hnpos:0<n:=by omega
  obtain ⟨weight,hw,hedge,hcont⟩:=hHost (Fin n) (by simpa using (show Nhost≤n by omega)) P (by simpa using hP)
  refine ⟨weight,by simpa using hw,hedge,?_⟩
  intro U _ _ Factors hFactors K hK i₀ rsv θfreq caux ρ D hs0 hs1 hθfreq hθfreq1 hcaux hda hρ hρ1 hD hsize S hS hsclass hclass Conflict π hUlo hUhi hFdeg hF hπ hRlo hRhi hHlo hHhi hDlo hnear
  have hhalf:(1/2:ℝ)≤θ:=(cycleThreshold_half_le (by omega:3≤m+1)).trans hθ
  have hmin:∀v,(1/2+α/2)*n≤(P.degree v:ℝ):=by
    intro v
    have hnR:0≤(n:ℝ):=by positivity
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)+α/2≤θ+α by linarith) hnR
    exact hh.trans (hP v)
  have hh:=hNpack n (by omega) hnpos Factors hFactors K hK i₀ rsv θfreq caux ρ D hs0 hs1 hθfreq hθfreq1 hcaux hda hρ hρ1 hD hsize S hS hsclass hclass k P Conflict π θ α βP ηP row ηH βH c B ε weight hcont hUlo hUhi hFdeg hF hπ hmin hRlo hRhi hHlo hHhi hDlo hnear
  convert hh using 1 <;> congr!
end Oberwolfach
