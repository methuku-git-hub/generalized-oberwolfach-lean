module

public import Oberwolfach.OrdinaryAssignedTriangleClassUniformLateClass

@[expose] public section
/-! The one-class triangle conclusion at a fixed threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) triangleFiniteEquality4 (n:ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

def ordinaryAssignedTriangleAtBound (d K:ℕ) (hd:2≤d)
    (θhost α ρ₀ s₀ ω βP ηP ηH L:ℝ) (hρ₀:0<ρ₀) (hs₀:0<s₀)
    (k:ℕ) (βH c B:ℝ) (N:ℕ):Prop :=
    ∀ (n:ℕ),N≤n→0<n→∀ (P:SimpleGraph (Fin n)) (D:ℕ),
      P.IsRegularOfDegree D→(∀ v,(θhost+α)*n≤(P.degree v:ℝ))→
    ∃ weight:OrdinaryCycle P 3→ℝ,
      (∀ C,c/(n:ℝ)^(3-2)≤weight C ∧ weight C≤B/(n:ℝ)^(3-2)) ∧
      (∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) ∧
    ∀ (U:Type) [Fintype U] [DecidableEq U], ω*n≤(Fintype.card U:ℝ)→Fintype.card U≤n→
    ∀ (i₀:Fin K) (Factors:U→SimpleGraph (Fin n)) (hFactors:∀ w,(Factors w).IsRegularOfDegree 2)
      (S:Set ℕ) (hS:∀ w,AllowedCycleLengths (Factors w) S)
      (hclass:∀ w,factorPreparationClass (Factors w) K=some i₀)
      (rsv θfreq caux:ℝ) (hslo:s₀/2≤rsv) (hshi:rsv≤s₀)
      (hsclass:rsv≤1/(2*(K:ℝ))) (hθfreq:0<θfreq) (hθfreq1:θfreq≤1/100)
      (hcaux:8≤caux) (hda:1/θfreq≤d),
    let ρ:=initialIndexDensity U D;
    ρ₀≤ρ→ρ≤1→
    ∀ (Conflict:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)),
      (∀ v,(Conflict.degree v:ℝ)≤L) → permutationConflictGraph π (3*d)≤Conflict →
      (∀ x l,0<l→l<2*d+1→(π^l) x≠x) →
    let q:=ordinaryAssignedMarkedProbability Factors hFactors K θfreq caux
    let s:=ordinaryAssignedSpokeProbability Factors hFactors K i₀ rsv θfreq caux
    let pR:=ρ*rsv
    let pH:=rsv
    let j:Bool:=false
    let pstar:ℝ:=ρ₀*s₀/2;
    ∃ (hRlo:ρ₀*s₀/2≤pR) (hRhi:pR≤1)
      (hq:∀ w j,0≤q w j) (hQ:∀ w,∑ j,q w j≤1/8)
      (hs:∀ w j,0≤s w j) (hS':∀ w,∑ j,s w j ≤ intervalUncoveredProbability d (∑ j,q w j)),
    let μ:=FiniteLaw.pi (rawWheelLaw (V:=Fin n) (fun _=>pR) (fun _=>(lt_of_lt_of_le (div_pos (mul_pos hρ₀ hs₀) (by norm_num)) hRlo).le) (fun _=>hRhi) d hd q hq hQ s hs hS')
    1-(1/(n:ℝ)+3/(n:ℝ)^2)≤
      μ.probability (ordinaryCombinedTriangleEvent d k P Conflict π θhost α pstar βP ηP ηH βH c B pR pH weight j)
end Oberwolfach
