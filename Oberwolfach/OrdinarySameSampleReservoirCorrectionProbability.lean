module

public import Oberwolfach.OrdinaryUniformSampleReservoirCorrection
public import Oberwolfach.OrdinaryExpandedGlobalCorrectionPrior
public import Oberwolfach.OrdinaryExpandedRawEventProductPrior

@[expose] public section
/-! The actual protected correction and reservoir are selected on the same
expanded sample as any supplied prior, with explicit failure probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_same_sample_reservoir_correction_probability
    (r:ℕ) (hr:3≤r) (α pstar ω:ℝ)
    (hα:0<α) (hα1:α≤1/2) (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω):
    ∃δ h:ℝ,0<δ ∧ δ<1/4 ∧ 0<h ∧
    ∀ξ:ℝ,∀hξ:0<ξ,∀hξh:ξ≤h/100,
    ∃εsample εv ζ:ℝ,0<εsample ∧ 0<εv ∧ 0<ζ ∧ ζ≤h ∧
    ∀(L:ℝ),0≤L→∀d q₀:ℕ,∀hd:2≤d,∀(m t f a b:ℕ),∃N:ℕ,1≤N ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V→ω*Fintype.card V≤(Fintype.card U:ℝ)→Fintype.card U≤Fintype.card V→
    ∀(P F:SimpleGraph V) (D:ℕ),P.IsRegularOfDegree D→0<D→
      (∀v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ))→(∀v,(F.degree v:ℝ)≤L)→
    ∀(π:Equiv.Perm V),permutationConflictGraph π (3*d)≤F→
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (pH:ℝ),pstar≤2*p→pstar≤pH→
      2*p=initialIndexDensity U D*pH→
    ∀(q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)) (j:Color),(∀w,s w j=pH)→
    ∀(εabs:ℝ) (A Z Wterm W:Finset V) (Bterm B:Finset U),
      A=Finset.univ\Z→(Z.card:ℝ)≤εabs*Fintype.card V→
      Wterm.card+Bterm.card≤t→Wterm⊆W→Bterm⊆B→W.card≤f→
      (B.card:ℝ)≤εabs*Fintype.card V+f→
      (Z.card:ℝ)≤εv*Fintype.card V→(B.card:ℝ)≤εv*Fintype.card V+f→
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ))
      (E:(Σσ,R σ)×(Sym2 V→Bool)→Prop) (lossE lossRes:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let ν:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    let μraw:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS);
    1-lossE≤((μ.sigma ρ).prod ν).probability E→
    1-lossRes≤μraw.probability (fun raw=>OrdinaryUniformProtectedReservoirEvent r m t f a b εabs
      (rawWheelGraph P raw\F) F (rawWheelSpokes π d raw j))→
    1-lossE-2/(Fintype.card V:ℝ)^q₀-lossRes≤((μ.sigma ρ).prod ν).probability (fun z=>E z ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      OrdinaryCorrectedProtectedReservoir r m t a b ξ (rawWheelGraph P raw\F) F
        (rawWheelSpokes π d raw j) A Z Wterm Bterm B):=by
  obtain ⟨δ,h,hδ,hδsmall,hh,hglobal⟩:=ordinary_expanded_global_correction_with_prior α pstar ω hα hα1 hpstar hpstar1 hω
  refine ⟨δ,h,hδ,hδsmall,hh,?_⟩
  intro ξ hξ hξh
  obtain ⟨εsample,εv,ζ,hεsample,hεv,hζ,hζh,hcorrect⟩:=
    ordinary_uniform_sample_reservoir_correction r hr ω h δ ξ hω hh hδ hδsmall hξ hξh
  refine ⟨εsample,εv,ζ,hεsample,hεv,hζ,hζh,?_⟩
  intro L hL d q₀ hd m t f a b
  obtain ⟨Ng,hglobal⟩:=hglobal εsample L hεsample hL d q₀ hd
  obtain ⟨Nc,hNc,hcorrect⟩:=hcorrect L hL m t f a b
  let N:=max Ng Nc
  refine ⟨N,by dsimp [N];omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hωn hUn P F D hreg hD hP hF π hconf hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpEq q hq hQ s hs hS j hj
    εabs A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB hZsmall hBsmall R _ ρ E lossE lossRes μ ν μraw hE hRes
  have hnpos:0<Fintype.card V:=by dsimp [N] at hn;omega
  have hupos:0<Fintype.card U:=by
    have hv:(0:ℝ)<Fintype.card V:=by exact_mod_cast hnpos
    have hu':0<(Fintype.card U:ℝ):=(mul_pos hω hv).trans_le hωn
    exact_mod_cast hu'
  let J:RawWheelOutcome V U Γ Color→Prop:=fun raw=>OrdinaryUniformProtectedReservoirEvent r m t f a b εabs
    (rawWheelGraph P raw\F) F (rawWheelSpokes π d raw j)
  let Prior:(Σσ,R σ)×(Sym2 V→Bool)→Prop:=fun z=>E z ∧
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
    RawOrdinaryRows P π d 2 Finset.univ (2*p) s j (εsample*Fintype.card V) raw ∧
    RawOrdinaryDomainIndices F π d 3 Finset.univ pH j (εsample*Fintype.card U) raw ∧
    OrdinaryTriangleReferenceMatrixCuts P F π d j δ h raw z.2
  have hPrior:1-lossE-2/(Fintype.card V:ℝ)^q₀≤((μ.sigma ρ).prod ν).probability Prior:=by
    exact hglobal V U Γ Color (by dsimp [N] at hn;omega) hωn hUn P F hP hF π hconf hnoshort
      p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH q hq hQ s hs hS j hj ρ E lossE hE
  have hBoth:=ordinary_expanded_add_raw_event_with_product_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    ρ ν Prior J (lossE+2/(Fintype.card V:ℝ)^q₀) lossRes (by linarith only [hPrior]) hRes
  have hBoth':1-lossE-2/(Fintype.card V:ℝ)^q₀-lossRes≤((μ.sigma ρ).prod ν).probability (fun z=>Prior z ∧ J (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))):=by
    convert hBoth using 1 <;> ring
  apply hBoth'.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1.1,?_⟩
  have ht:=hcorrect V U Γ Color (by dsimp [N] at hn;omega) hnpos hupos hωn hUn P F D hreg hD π d j
    (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) z.2 (2*p) pH s hpEq hz.1.2.1 hz.1.2.2.1 hF hz.1.2.2.2
    εabs A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB hZsmall hBsmall hz.2
  convert ht using 1 <;> congr! 40
end Oberwolfach
