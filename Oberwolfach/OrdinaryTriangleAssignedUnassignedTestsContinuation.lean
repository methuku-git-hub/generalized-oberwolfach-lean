module

public import Oberwolfach.OrdinaryTriangleAssignedFullMatchingTestsContinuation
public import Oberwolfach.OrdinaryUnassignedLocalTestsHigh

@[expose] public section
/-! Attach protected and full-domain unassigned tests to the same ordinary
host and wheel-load sample, including an arbitrary later sampling stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) ordinaryTriangleUnassignedTestsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

def OrdinaryTriangleAssignedUnassignedTestsContinuation {n:ℕ}
    (IM IO:Type) [Fintype IM] [Fintype IO] (mM:ℕ) (mO:IO→ℕ)
    (BM tM:ℝ) (BO tO:IO→ℝ)
    (δ χ γ αpack:ℝ) (d k:ℕ) (hd:2≤d) (P:SimpleGraph (Fin n))
    (θhost αhost pstar ω βP ηP ηH L βH c B ε:ℝ)
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
    ∀(H₀ Hₖ:Fin n→U→Prop)
      (wM:∀i:IM,MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd mM π (3*d) H₀ Hₖ→ℝ)
      (hwM:∀i W,0≤wM i W ∧ wM i W≤BM/(n:ℝ)^mM) (gM:IM→Bool) (jM:IM→Bool)
      (wO:∀i:IO,OrderedOrdinaryWheel (U:=U) π (3*d) (mO i+1)→ℝ)
      (hwO:∀i W,0≤wO i W ∧ wO i W≤BO i/(n:ℝ)^(mO i)) (gO:IO→Bool) (jO:IO→Bool),
    ∀(A:Finset (Fin n)) (J:Finset U),
    ∀{R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) ((ρ*rsv)/2) 0 ((2*p₂)/2) 0 u
      (by positivity) (by norm_num) (by positivity) (by norm_num) hu (by linarith) d hd q hq hQ s hs hSc);
    1-χ≤(μ.sigma ν).probability (fun z=>
      ((((ordinaryCombinedTriangleEvent d k P Conflict π θhost αhost pstar βP ηP ηH βH c B (ρ*rsv) rsv weight false
        (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) ∧
       (∀v,|((longPhysicalStateGraph P z.1 {0,1,2,3,4}).degree v:ℝ)-ρ*(P.degree v:ℝ)|<δ*n)) ∧
      OrdinaryPrescribedPackingEvent 3 d pstar γ αpack P Conflict π Finset.univ Finset.univ false
        (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))) ∧
      OrdinaryShiftedMixedLoadEvent P π d mM mO ((2*p₂)/2) 0 q s H₀ Hₖ wM gM jM wO gO jO tM tO z.1) ∧
      OrdinaryExpandedHubTotalEvent P π d mO ((2*p₂)/2) 0 q s wO gO jO tO z.1) ∧
      OrdinaryUnassignedLocalTests P π d q s u A J z.1)

theorem ordinary_triangle_assigned_unassigned_tests_continuation
    (IM IO:Type) [Fintype IM] [Fintype IO] (mM:ℕ) (mO:IO→ℕ)
    (BM tM:ℝ) (BO tO:IO→ℝ) (δ χ γ αpack:ℝ) (d k:ℕ) (hd:2≤d) (hχ:0<χ):
    ∃N:ℕ,∀n≥N,∀(P:SimpleGraph (Fin n)) (θhost αhost pstar ω βP ηP ηH L βH c B ε:ℝ)
    (weight:OrdinaryCycle P 3→ℝ),
    OrdinaryTriangleAssignedFullMatchingTestsContinuation IM IO mM mO BM tM BO tO δ (χ/2) γ αpack d k hd P θhost αhost pstar ω βP ηP ηH L βH c B ε weight→
    OrdinaryTriangleAssignedUnassignedTestsContinuation IM IO mM mO BM tM BO tO δ χ γ αpack d k hd P θhost αhost pstar ω βP ηP ηH L βH c B ε weight :=by
  obtain ⟨N,_,hN⟩:=ordinary_unassigned_local_tests_high d hd (χ/2) (by positivity)
  refine ⟨N,?_⟩
  intro n hn P θhost αhost pstar ω βP ηP ηH L βH c B ε weight hBase
  intro U _ _ Factors hFactors K hK i₀ rsv θfreq caux ρ D hs0 hs1 hθfreq hθfreq1 hcaux hda hρ hρ1 hD hsize S hS hsclass hclass Conflict π hUlo hUhi hFdeg hF hπ hRlo hRhi hHlo hHhi hDlo hnear
  have hU0:0<Fintype.card U:=by
    have hh:0<(Fintype.card U:ℝ):=by nlinarith [mul_pos hρ hD]
    exact_mod_cast hh
  obtain ⟨p,p₂,u,hp,hp₂,hu,hsum,hpEq,hplower,hpD,huD,hq,hQ,hs,hSc,hEvent⟩:=
    hBase Factors hFactors K hK i₀ rsv θfreq caux ρ D hs0 hs1 hθfreq hθfreq1 hcaux hda hρ hρ1 hD hsize S hS hsclass hclass Conflict π hUlo hUhi hFdeg hF hπ hRlo hRhi hHlo hHhi hDlo hnear
  refine ⟨p,p₂,u,hp,hp₂,hu,hsum,hpEq,hplower,hpD,huD,hq,hQ,hs,hSc,?_⟩
  intro H₀ Hₖ wM hwM gM jM wO hwO gO jO A J R _ ν μ
  have hExtra:=hN (Fin n) U Bool Bool (by simpa using hn) hU0 (by simpa using hUhi) P π A J
    ((ρ*rsv)/2) 0 ((2*p₂)/2) 0 u (by positivity) (by norm_num) (by positivity) (by norm_num) hu (by linarith)
    _ hq hQ _ hs hSc hπ ν
  have hh:=finiteLaw_intersection_lower (μ.sigma ν) _ _ (χ/2) (χ/2) (hEvent H₀ Hₖ wM hwM gM jM wO hwO gO jO ν) hExtra
  have hbound:1-χ≤1-χ/2-χ/2:=by linarith
  apply hbound.trans
  convert hh using 1 <;> congr!
end Oberwolfach
