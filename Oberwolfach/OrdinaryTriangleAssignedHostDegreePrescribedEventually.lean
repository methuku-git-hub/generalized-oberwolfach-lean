module

public import Oberwolfach.OrdinaryExpandedAddPrescribedPacking
public import Oberwolfach.OrdinaryTriangleSharedHostDegreeEvents
public import Oberwolfach.OrdinaryAssignedSamplingWitness
public import Oberwolfach.OrdinaryTriangleAssignedHostDegreePrescribedRecipe
public import Oberwolfach.OrdinaryPrescribedFailureBudget

@[expose] public section
/-! Assigned ordinary host, physical degree concentration and adaptive
prescribed-edge wheel packing on one expanded experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) ordinaryTriangleAssignedPackEventuallyFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_triangle_assigned_host_degree_prescribed_eventually
    (pstar γ ω:ℝ)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hγ:0<γ) (hγ1:γ≤1) (hω:0<ω)
    (δ χ:ℝ) (hδ:0<δ) (hχ:0<χ):
    ∃α₀:ℝ,0<α₀ ∧ α₀≤1 ∧ ∀αpack L:ℝ,0<αpack→αpack≤α₀→0≤L→
    ∀d:ℕ,∀hd:2≤d,∃N:ℕ,∀n≥N,0<n→
    ∀{U:Type} [Fintype U] [DecidableEq U]
    (Factors:U→SimpleGraph (Fin n)) (hFactors:∀w,(Factors w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θfreq caux ρ D:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθfreq:0<θfreq) (hθfreq1:θfreq≤1/100) (hcaux:8≤caux)
    (hda:1/θfreq≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (Factors w) S)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,factorPreparationClass (Factors w) K=some i₀)
    (k:ℕ) (P Conflict:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (θhost αhost βP ηP ηH βH c B ε:ℝ)
    (weight:OrdinaryCycle P 3→ℝ)
    (hcont:ordinaryUniformTriangleHostContinuation d k hd P θhost αhost pstar ω βP ηP ηH L βH c B ε hpstar weight)
    (hUlo:ω*n≤(Fintype.card U:ℝ)) (hUhi:Fintype.card U≤n)
    (hFdeg:∀v,(Conflict.degree v:ℝ)≤L) (hF:permutationConflictGraph π (3*d)≤Conflict)
    (hπ:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hmin:∀v,(1/2+γ)*n≤(P.degree v:ℝ))
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
      (ordinaryCombinedTriangleEvent d k P Conflict π θhost αhost pstar βP ηP ηH βH c B (ρ*rsv) rsv weight false
        (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) ∧
       (∀v,|((longPhysicalStateGraph P z.1 {0,1,2,3,4}).degree v:ℝ)-ρ*(P.degree v:ℝ)|<δ*n)) ∧
      OrdinaryPrescribedPackingEvent 3 d pstar γ αpack P Conflict π Finset.univ Finset.univ false
        (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))) :=by
  obtain ⟨α₀,hα₀,hα₁,hpack⟩:=ordinary_triangle_assigned_host_degree_prescribed_packing_with_recipe pstar γ ω hpstar hpstar1 hγ hγ1 hω
  obtain ⟨Nfail,hNfail,hfail⟩:=ordinary_prescribed_failure_eventually_small δ χ hδ hχ
  refine ⟨α₀,hα₀,hα₁,?_⟩
  intro αpack L hαpack hαsmall hL d hd
  obtain ⟨N,hN⟩:=hpack αpack L hαpack hαsmall hL d 1 hd
  refine ⟨max N Nfail,?_⟩
  intro n hn hnpos U _ _ Factors hFactors K hK i₀ rsv θfreq caux ρ D hs0 hs1 hθfreq hθfreq1 hcaux hda hρ hρ1 hD hsize S hS hsclass hclass k P Conflict π θhost αhost βP ηP ηH βH c B ε weight hcont hUlo hUhi hFdeg hF hπ hmin hRlo hRhi hHlo hHhi hDlo hnear
  obtain ⟨p,p₂,u,hp,hp₂,hu,hsum,hpEq,hplower,hpD,huD,hq,hQ,hs,hSc,hEvent⟩:=hN n (by omega) hnpos Factors hFactors K hK i₀ rsv θfreq caux ρ D hs0 hs1 hθfreq hθfreq1 hcaux hda hρ hρ1 hD hsize S hS hsclass hclass k P Conflict π θhost αhost βP ηP ηH βH c B ε weight hcont hUlo hUhi hFdeg hF hπ hmin hRlo hRhi hHlo hHhi hDlo hnear (δ*n) (by positivity)
  refine ⟨p,p₂,u,hp,hp₂,hu,hsum,hpEq,hplower,hpD,huD,hq,hQ,hs,hSc,?_⟩
  intro R _ ν μ
  have hh:=hEvent ν
  have hbudget:=hfail n (by omega)
  have hbound:1-χ≤1-(((1/(n:ℝ)+3/(n:ℝ)^2)+2*(n:ℝ)*Real.exp (-2*(δ*(n:ℝ))^2/n))+1/(n:ℝ)^1):=by
    simp only [pow_one]
    linarith
  exact hbound.trans hh
end Oberwolfach
