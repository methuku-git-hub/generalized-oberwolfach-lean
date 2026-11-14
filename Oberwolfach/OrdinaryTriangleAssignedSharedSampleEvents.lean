module

public import Oberwolfach.OrdinaryAssignedTriangleFromHost
public import Oberwolfach.OrdinaryExpandedSharedSampleEvents

@[expose] public section
/-! The actual ordinary-class reference event and any full-class graph event
hold on one expanded experiment with the summed failure bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) triangleSharedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_triangle_assigned_shared_sample_events
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U] [DecidableEq U]
    (Factors:U→SimpleGraph (Fin n)) (hFactors:∀w,(Factors w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θfreq caux ρ D:ℝ) (d:ℕ) (hd:2≤d)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθfreq:0<θfreq) (hθfreq1:θfreq≤1/100) (hcaux:8≤caux)
    (hda:1/θfreq≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (Factors w) S)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,factorPreparationClass (Factors w) K=some i₀)
    (k:ℕ) (P Conflict:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (θhost α pstar ω βP ηP ηH L βH c B ε:ℝ)
    (weight:OrdinaryCycle P 3→ℝ) (hpstar:0<pstar)
    (hcont:ordinaryUniformTriangleHostContinuation d k hd P θhost α pstar ω βP ηP ηH L βH c B ε hpstar weight)
    (hUlo:ω*n≤(Fintype.card U:ℝ)) (hUhi:Fintype.card U≤n)
    (hFdeg:∀v,(Conflict.degree v:ℝ)≤L) (hF:permutationConflictGraph π (3*d)≤Conflict)
    (hπ:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hRlo:pstar≤ρ*rsv) (hRhi:ρ*rsv≤1) (hHlo:pstar≤rsv) (hHhi:rsv≤1)
    (hDlo:(n:ℝ)/2≤D) (hnear:∀v,|(P.degree v:ℝ)-D|≤ε*n)
    (p₂ u:ℝ) (hp₂:0≤p₂) (hu:0≤u) (hstates:ρ*rsv+p₂+u=ρ):
    let q:=ordinaryAssignedMarkedProbability Factors hFactors K θfreq caux
    let s:=ordinaryAssignedSpokeProbability Factors hFactors K i₀ rsv θfreq caux;
    ∃ (hq:∀w j,0≤q w j) (hQ:∀w,∑j,q w j≤1/8)
      (hs:∀w j,0≤s w j) (hSc:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑j,q w j)),
    ∀{R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (Good:SimpleGraph (Fin n)→Prop) (εGood:ℝ),
    (1-εGood≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin ρ hρ.le hρ1)).probability
      (fun σ=>Good (retainedGraph P σ)))→
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) ((ρ*rsv)/2) 0 (p₂/2) 0 u
      (by positivity) (by norm_num) (by positivity) (by norm_num) hu (by linarith) d hd q hq hQ s hs hSc);
    1-((1/(n:ℝ)+3/(n:ℝ)^2)+εGood)≤(μ.sigma ν).probability (fun z=>
      ordinaryCombinedTriangleEvent d k P Conflict π θhost α pstar βP ηP ηH βH c B (ρ*rsv) rsv weight false
        (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) ∧
      Good (longPhysicalStateGraph P z.1 {0,1,2,3,4})) :=by
  intro q s
  obtain ⟨hq,hQ,hs,hSc,hhost⟩:=ordinary_actual_triangle_class_event_given_host_continuation hn Factors hFactors K hK i₀ rsv θfreq caux ρ D d hd
    hs0 hs1 hθfreq hθfreq1 hcaux hda hρ hρ1 hD hsize S hS hsclass hclass k P Conflict π θhost α pstar ω βP ηP ηH L βH c B ε weight hpstar
    hcont hUlo hUhi hFdeg hF hπ hRlo hRhi hHlo hHhi hDlo hnear
  refine ⟨hq,hQ,hs,hSc,?_⟩
  intro R _ ν Good εGood hGood μ
  have hh:=ordinary_expanded_shared_sample_events P (ρ*rsv) p₂ u ρ (by positivity) hp₂ hu hρ1 hstates
    d hd q hq hQ s hs hSc ν
    (ordinaryCombinedTriangleEvent d k P Conflict π θhost α pstar βP ηP ηH βH c B (ρ*rsv) rsv weight false)
    Good (1/(n:ℝ)+3/(n:ℝ)^2) εGood hhost hGood
  convert hh using 1 <;> congr!
end Oberwolfach
