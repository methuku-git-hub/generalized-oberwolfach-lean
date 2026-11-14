module

public import Oberwolfach.Vortex
public import Oberwolfach.OrdinaryCombinedFullHostInputs
public import Oberwolfach.OrdinaryAssignedSamplingParameters
public import Oberwolfach.OrdinaryUniformSelectedDensity
public import Oberwolfach.OrdinaryAssignedClassRecipeValid
public import Oberwolfach.OrdinaryAssignedFromHostContinuation

@[expose] public section
/-! Apply the same-sample ordinary host and absorber input estimates with the
actual probabilities constructed from an assigned family of factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) ordinaryFiniteLateEquality0 (n:ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

theorem ordinary_assigned_class_combined_event_uniform_late_class
    (m d K:ℕ) (hm:3≤m) (hd:2≤d) (hK:0<K)
    (θhost α ρ₀ s₀ ω βP ηP row ηH L:ℝ)
    (hθhost:cycleThreshold (m+1)≤θhost) (hα:0<α) (hα1:α≤1) (hθhost1:θhost+α/2≤1)
    (hρ₀:0<ρ₀) (hρ₁:ρ₀≤1) (hs₀:0<s₀) (hs₁:s₀≤1/100) (hω:0<ω)
    (hβP:0<βP) (hβmax:βP≤(α/2)*(ρ₀*s₀/2)^2*(ρ₀*s₀/2)^2)
    (hβhub:βP≤ω*(ρ₀*s₀/2)^(m+7)/4) (hηP:0<ηP) (hrow:0<row)
    (hrowmax:row≤(ρ₀*s₀/2)^(m+7)/2) (hηH:0<ηH) (hL:0≤L):
    ∃ (k:ℕ) (βH c B:ℝ),m+3≤k ∧ 0<βH ∧ 0<c ∧ 0<B ∧ ∃ N:ℕ,
    ∀ (n:ℕ),N≤n→0<n→∀ (P:SimpleGraph (Fin n)) (D:ℕ),
      P.IsRegularOfDegree D→(∀ v,(θhost+α)*n≤(P.degree v:ℝ))→
    ∃ weight:OrdinaryCycle P (m+1)→ℝ,
      (∀ C,c/(n:ℝ)^((m+1)-2)≤weight C ∧ weight C≤B/(n:ℝ)^((m+1)-2)) ∧
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
      μ.probability (ordinaryCombinedHostEvent m d k hm P Conflict π θhost α pstar βP ηP row ηH βH c B pR pH weight s j)
 := by
  have hs01:s₀≤1:=by linarith
  obtain ⟨hpstar,hpstar1,hfloor⟩:=ordinary_uniform_selected_density_floor ρ₀ s₀ hρ₀ hρ₁ hs₀ hs01
  obtain ⟨k,βH,c,B,ε,hk,hβH,hc,hB,hε,N,hbase⟩:=ordinary_full_host_continuation_uniform
    m d hm hd θhost α (ρ₀*s₀/2) ω βP ηP row ηH L hθhost hα hα1 hθhost1
    hpstar hpstar1 hω hβP hβmax hβhub hηP hrow hrowmax hηH hL
  refine ⟨k,βH,c,B,hk,hβH,hc,hB,N,?_⟩
  intro n hn hn0 P D hreg hdeg
  obtain ⟨weight,hw,hedge,hbase⟩:=hbase (Fin n) (by simpa using hn) P (by simpa using hdeg)
  refine ⟨weight,by simpa using hw,hedge,?_⟩
  intro U _ _ hUlo hUhi i₀ Factors hFactors S hS hclass rsv θfreq caux hslo hshi hsclass hθfreq hθfreq1 hcaux hda ρ hρlo hρhi Conflict π hFdeg hF hπ
    q s pR pH j pstar
  have hrsv0:0≤rsv:=by linarith
  have hrsv1:rsv≤1/100:=by linarith
  let v:Fin n:=⟨0,hn0⟩
  have hθlo:(1/2:ℝ)≤θhost:=(cycleThreshold_half_le (by omega:3≤m+1)).trans hθhost
  have hDn:(n:ℝ)/2≤D:=by
    have hh:=hdeg v
    rw [hreg v] at hh
    have hnR:(0:ℝ)≤n:=by positivity
    nlinarith
  have hD:(0:ℝ)<D:=by
    have hnR:(0:ℝ)<n:=by exact_mod_cast hn0
    nlinarith
  have hsize:ρ*(D:ℝ)=2*(Fintype.card U:ℝ):=by dsimp [ρ,initialIndexDensity];field_simp
  have hδ:=hfloor ρ rsv hρlo hρhi hslo hshi
  have hRlo:ρ₀*s₀/2≤pR:=hδ.1
  have hRhi:pR≤1:=hδ.2.1
  have hHlo:ρ₀*s₀/2≤pH:=hδ.2.2.1
  have hHhi:pH≤1:=hδ.2.2.2
  have hε0:0≤ε:=hε.le
  have hnR:(0:ℝ)≤n:=by positivity
  have hnear:∀ v,|(P.degree v:ℝ)-(D:ℝ)|≤ε*n:=by
    intro v
    rw [hreg v]
    simp only [sub_self,abs_zero]
    exact mul_nonneg hε0 hnR
  refine ⟨hRlo,hRhi,?_⟩
  exact ordinary_actual_class_event_given_host_continuation hn0 Factors hFactors K hK i₀ rsv θfreq caux ρ (D:ℝ) d hd
    hrsv0 hrsv1 hθfreq hθfreq1 hcaux hda (hρ₀.trans_le hρlo) hρhi hD hsize S hS hsclass hclass
    m k hm P Conflict π θhost α (ρ₀*s₀/2) ω βP ηP row ηH L βH c B ε weight hpstar hbase
    hUlo hUhi hFdeg hF hπ hRlo hRhi hHlo hHhi hDn hnear
end Oberwolfach
