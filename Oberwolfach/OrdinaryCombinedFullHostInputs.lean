module

public import Oberwolfach.OrdinaryFullHostSampling
public import Oberwolfach.OrdinaryUniformLongInputsProbability
public import Oberwolfach.TwoCommonEvents

@[expose] public section
/-! Use the same physical and interval sample for the full-host potential
estimates and the ordinary absorber input estimates, with the original fixed
parent cycle weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_full_host_and_absorber_inputs_common
    (m d:ℕ) (hm:3≤m) (hd:2≤d) (θ α pstar ω βP ηP row ηH L:ℝ)
    (hθ:cycleThreshold (m+1)≤θ) (hα:0<α) (hα1:α≤1) (hθ1:θ+α/2≤1)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω)
    (hβP:0<βP) (hβmax:βP≤(α/2)*pstar^2*pstar^2)
    (hβhub:βP≤ω*pstar^(m+7)/4) (hηP:0<ηP) (hrow:0<row)
    (hrowmax:row≤pstar^(m+7)/2) (hηH:0<ηH) (hL:0≤L):
    ∃ (k:ℕ) (βH c B ε:ℝ),m+3≤k ∧ 0<βH ∧ 0<c ∧ 0<B ∧ 0<ε ∧ ∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V →
    ∀ P:SimpleGraph V,(∀ v,(θ+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∃ weight:OrdinaryCycle P (m+1)→ℝ,
      (∀ C,c/(Fintype.card V:ℝ)^((m+1)-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^((m+1)-2)) ∧
      (∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) ∧
    ∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U],
      ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (F:SimpleGraph V) (π:Equiv.Perm V),
      (∀ v,(F.degree v:ℝ)≤L) → permutationConflictGraph π (3*d)≤F →
      (∀ x l,0<l→l<2*d+1→(π^l) x≠x) →
    ∀ pR pH D₀:ℝ,∀ hRlo:pstar≤pR,∀ hRhi:pR≤1,pstar≤pH→pH≤1→
      (Fintype.card V:ℝ)/2≤D₀→
      (∀ v,|(P.degree v:ℝ)-D₀|≤ε*Fintype.card V) → pR*D₀=2*(Fintype.card U:ℝ)*pH →
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ g,q u g))
      (j:Color),(∀ u,s u j=pH) →
    let μ:=FiniteLaw.pi (rawWheelLaw (fun _:Sym2 V=>pR) (fun _=>(hpstar.trans_le hRlo).le) (fun _=>hRhi) d hd q hq hQ s hs hS)
    let w:=ordinaryFullHostSeed (U:=U) P F (m+1) weight pR pH;
    1-(1/(Fintype.card V:ℝ)+3/(Fintype.card V:ℝ)^2)≤μ.probability (fun σ=>
      ((∀ v:V,βH*Fintype.card V≤(Fintype.card {u:U // rawWheelSpokes π d σ j v u}:ℝ)) ∧
      ((∀ x y,P.Adj x y→¬F.Adj x y→
        |ordinaryPotentialLoad w (Sum.inl s(x,y)) ((rawWheelGraph P σ)\F) (rawWheelSpokes π d σ j)-1|≤ηH) ∧
       (∀ v u,|ordinaryPotentialLoad w (Sum.inr (v,u)) ((rawWheelGraph P σ)\F) (rawWheelSpokes π d σ j)-1|≤ηH)) ∧
      (∀ x y:V,x≠y→¬F.Adj x y→
        βH≤ordinaryIsolatorPotential P F (rawWheelSpokes π d σ j) k θ (α/4) x y (fun e=>σ (Sum.inl e))) ∧
      (∀ v:V,∀ u u':U,u≠u'→βH≤transferSurvivalSum (m+1) (by omega) P F
        (transferRootCompletedSpokes (rawWheelSpokes π d σ j) v) v u u' (fun e=>σ (Sum.inl e)))) ∧
      (ordinarySampledProfileProperty (r:=m+1) P F π d σ pstar pstar j βP ηP c B ∧
       Nonempty (OrdinaryCommonCycleProfiles (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) (m+1)
         (fun (_:Unit)=>pairedAbsorberTemplate (m+1)) βP ((ordinaryLocalCountCoeff m βP/2)^(m+2))
         c (4*B/(pstar^(m+1)*(pstar*pstar)^m)) ηP) ∧
       RawOrdinaryRows P π d (m+7) Finset.univ pR s j (row*Fintype.card V) σ ∧
       (∀ T:Finset V,T.card≤m+7→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
         βP*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))).card:ℝ)))) := by
  obtain ⟨k,βH,c,B,hk,hβH,hc,hB,hhost⟩:=ordinary_full_host_sampling_numerical (m+1) (by omega) θ α pstar ω hθ hα hα1 hθ1 hpstar hpstar1 hω
  obtain ⟨εH,hεH,hhost⟩:=hhost ηH hηH
  obtain ⟨NH,hhost⟩:=hhost L hL d 2 hd
  obtain ⟨εP,hεP,NP,hprofile⟩:=ordinary_uniform_sampled_long_inputs_probability m d hm hd (α/2) pstar pstar βP ηP c B L ω row
    (by positivity) hpstar hpstar hpstar1 hω hrow hrowmax hβP hβmax hβhub hηP hc.le hB hL
  let ε:=min 1 (min εH εP)
  let N:=max 1 (max NH NP)
  refine ⟨k,βH,c,B,ε,by omega,hβH,hc,hB,by dsimp [ε];positivity,N,?_⟩
  intro V _ _ hn P hP
  have hn1:1≤Fintype.card V:=by dsimp [N] at hn;omega
  obtain ⟨weight,hw,hedge,hhost⟩:=hhost V (by dsimp [N] at hn;omega) P hP
  refine ⟨weight,hw,hedge,?_⟩
  intro U Γ Color _ _ _ _ hUlo hUhi F π hFdeg hF hπ pR pH D₀ hRlo hRhi hHlo hHhi hDlo hreg hbal q hq hQ s hs hS j hj μ w
  have hε0:0≤ε:=by dsimp [ε];positivity
  have hεH':ε≤εH:=by dsimp [ε];exact (min_le_right _ _).trans (min_le_left _ _)
  have hεP':ε≤εP:=by dsimp [ε];exact (min_le_right _ _).trans (min_le_right _ _)
  have hε1:ε≤1:=by dsimp [ε];exact min_le_left _ _
  have hnR:(0:ℝ)≤Fintype.card V:=by positivity
  have hregH:∀ v,|(P.degree v:ℝ)-D₀|≤εH*Fintype.card V:=fun v=>(hreg v).trans (mul_le_mul_of_nonneg_right hεH' hnR)
  have hregP:∀ v,|(P.degree v:ℝ)-D₀|≤εP*Fintype.card V:=fun v=>(hreg v).trans (mul_le_mul_of_nonneg_right hεP' hnR)
  have hθlo:(1/2:ℝ)≤θ:=(cycleThreshold_half_le (by omega:3≤m+1)).trans hθ
  have hPmin:∀ v,(1/2+α/2)*Fintype.card V≤(P.degree v:ℝ):=by
    intro v
    have hcoef:(1/2+α/2:ℝ)≤θ+α:=by linarith
    exact (mul_le_mul_of_nonneg_right hcoef hnR).trans (hP v)
  let v:V:=Classical.choice (Fintype.card_pos_iff.mp (by omega))
  have hdeg:(P.degree v:ℝ)≤Fintype.card V:=by exact_mod_cast (P.degree_lt_card_verts v).le
  have hDhi:D₀≤2*Fintype.card V:=by
    have hh:=abs_le.mp (hreg v)
    nlinarith
  obtain ⟨_,hH⟩:=hhost U Γ Color hUlo hUhi F π hFdeg hF hπ pR pH D₀ ε hRlo hRhi hHlo hHhi hDlo hε0 hεH' hreg hbal q hq hQ s hs hS j hj
  have hweight:∀ C,0≤weight C:=fun C=>(div_nonneg hc.le (by positivity)).trans (hw C).1
  have hprof:=hprofile V U Γ Color (by dsimp [N] at hn;omega) hUhi hUlo P F π hF hπ weight hweight (fun C=>(hw C).1) (fun C=>(hw C).2)
    hFdeg hPmin hedge D₀ hDlo hDhi hregP pR hRlo hRhi q hq hQ s hs hS j
    (fun u=>by rw [hj u];exact hHlo) (fun u=>by rw [hj u];exact hHhi) pH hHlo hj
  have hboth:=finiteLaw_two_events_lower μ _ _ (1/(Fintype.card V:ℝ)^2)
    (1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2) hH hprof
  convert hboth using 1 <;> ring
end Oberwolfach
