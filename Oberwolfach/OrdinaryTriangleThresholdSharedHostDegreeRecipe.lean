module

public import Oberwolfach.OrdinaryTriangleThresholdSharedHostDegree
public import Oberwolfach.OrdinaryAssignedSamplingWitness

@[expose] public section
/-! Instantiate the ordinary expanded physical states using the actual factor
frequencies, rather than treating the extra state probabilities as inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) ordinaryTriangleSharedRecipeFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_triangle_threshold_shared_host_degree_with_recipe {n:ℕ} (hn:0<n)
    (δ χ:ℝ) (d k:ℕ) (hd:2≤d) (P:SimpleGraph (Fin n))
    (θhost α pstar ω βP ηP ηH L βH c B ε:ℝ)
    (weight:OrdinaryCycle P 3→ℝ)
    (hShared:OrdinaryTriangleThresholdSharedHostDegreeContinuation δ χ d k hd P θhost α pstar ω βP ηP ηH L βH c B ε weight):
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
    ∃(p p₂ udens:ℝ) (hp:0≤p) (hp₂:0≤p₂) (hudens:0≤udens)
      (hsum:2*p+2*p₂+udens=ρ) (hpEq:2*p=ρ*rsv),ρ/4≤p₂ ∧
      p₂*D=∑w,(ordinaryAssignedLongWeight Factors hFactors K θfreq caux w+
        ordinaryAssignedShortWeight Factors hFactors K i₀ rsv θfreq caux w) ∧
      udens*D=2*∑w,(1-rsv-ordinaryAssignedLongWeight Factors hFactors K θfreq caux w-
        ordinaryAssignedShortWeight Factors hFactors K i₀ rsv θfreq caux w) ∧
    let q:=ordinaryAssignedMarkedProbability Factors hFactors K θfreq caux
    let s:=ordinaryAssignedSpokeProbability Factors hFactors K i₀ rsv θfreq caux;
    ∃ (hq:∀w j,0≤q w j) (hQ:∀w,∑j,q w j≤1/8)
      (hs:∀w j,0≤s w j) (hSc:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑j,q w j)),
    ∀{R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) ((ρ*rsv)/2) 0 ((2*p₂)/2) 0 udens
      (by positivity) (by norm_num) (by positivity) (by norm_num) hudens (by linarith) d hd q hq hQ s hs hSc);
    1-χ≤(μ.sigma ν).probability (fun z=>
      ordinaryCombinedTriangleEvent d k P Conflict π θhost α pstar βP ηP ηH βH c B (ρ*rsv) rsv weight false
        (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) ∧
      ∀v,|((longPhysicalStateGraph P z.1 {0,1,2,3,4}).degree v:ℝ)-ρ*(P.degree v:ℝ)|<δ*n) :=by
  intro U _ _ Factors hFactors K hK i₀ rsv θfreq caux ρ D hs0 hs1 hθfreq hθfreq1 hcaux hda hρ hρ1 hD hsize S hS hsclass hclass Conflict π hUlo hUhi hFdeg hF hπ hRlo hRhi hHlo hHhi hDlo hnear
  obtain ⟨p,p₂,udens,hp,hp₂,hudens,hsum,hpEq,hplower,hpD,huD,hrecipe⟩:=
    ordinary_assigned_class_sampling_witness hn Factors hFactors S hS K hK i₀ rsv θfreq caux ρ D d hd
      hs0 hs1 hθfreq hθfreq1 hcaux hda hρ hρ1 hD hsize hsclass hclass
  refine ⟨p,p₂,udens,hp,hp₂,hudens,hsum,hpEq,hplower,hpD,huD,?_⟩
  have hh:=hShared Factors hFactors K hK i₀ rsv θfreq caux ρ D hs0 hs1 hθfreq hθfreq1 hcaux hda hρ hρ1 hD hsize S hS hsclass hclass Conflict π hUlo hUhi hFdeg hF hπ hRlo hRhi hHlo hHhi hDlo hnear
    (2*p₂) udens (by positivity) hudens (by linarith)
  convert hh using 1 <;> congr!
end Oberwolfach
