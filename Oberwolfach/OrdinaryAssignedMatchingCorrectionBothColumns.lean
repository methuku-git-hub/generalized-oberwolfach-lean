module

public import Oberwolfach.OrdinaryMatchingCorrectionBothLocalColumns
public import Oberwolfach.OrdinaryAssignedReservoirRateInputs
public import Oberwolfach.OrdinaryAssignedVortexExactSamplingData
public import Oberwolfach.OrdinaryAssignedFalseMarkedZero

@[expose] public section

/-! Specialize the matching-prior, correction and local-test join to the
original assigned sampling law used by the ordinary construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 45000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_matching_correction_both_columns
    (r:ℕ) (hr:3 ≤ r) (α pstar ω:ℝ)
    (hα:0<α) (hpstar:0<pstar) (hpstar1:pstar ≤ 1) (hω:0<ω):
    ∃δ h εabs εv:ℝ,0<δ ∧ δ<1/4 ∧ 0<h ∧ 0<εabs ∧ 0<εv ∧
    ∀(d:ℕ) (hd:2 ≤ d),∀L:ℝ,0 ≤ L → ∀ξ:ℝ,∀hξ:0<ξ,∀hξh:ξ ≤ h/100,
    ∀mAbs:ℕ,∃a b:ℕ,∀t f q₀:ℕ,∃N:ℕ,1 ≤ N ∧
    ∀(ζlocal χlocal χglobal χhub χcol C:ℝ),0<ζlocal → 0<χlocal → 0<χglobal → 0<χhub → 0<χcol → 0 ≤ C → 
    ∃Nc Ng Nh Ncol:ℕ,1 ≤ Nc ∧ 1 ≤ Ng ∧ 1 ≤ Nh ∧ 1 ≤ Ncol ∧
    ∀(n qCount K D:ℕ),N ≤ n → Ng ≤ n → ω*n ≤ (qCount:ℝ) → qCount ≤ n → 0<D → 
    ∀(P Bad:SimpleGraph (Fin n)),P.IsRegularOfDegree D → 
      (cycleThreshold r+α)*n ≤ D → (∀v,(Bad.degree v:ℝ) ≤ L) → 
    ∀(π:Equiv.Perm (Fin n)),permutationConflictGraph π (3*d) ≤ Bad → 
      (∀x k,0<k → k<2*d+1 → (π^k) x ≠ x) → 
    ∀(F:Fin qCount → SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (i₀:Fin K) (rsv θ ρ₀ smin:ℝ) (mMatch:ℕ)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((mMatch:ℝ)+1) ρ₀ smin d),
    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((mMatch:ℝ)+1) D
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((mMatch:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((mMatch:ℝ)+1);
    0<ρ₀  →  ρ₀ ≤ initialIndexDensity (Fin qCount) D  →  (1/2:ℝ)*(n:ℝ) ≤ D  → 
    2*pstar ≤ ρ₀*smin  → 
    ∀(A Z Wterm W:Finset (Fin n)) (Bterm B Htest:Finset (Fin qCount)),
      A=Finset.univ\Z → (Z.card:ℝ) ≤ εabs*n → 
      Wterm.card+Bterm.card ≤ t → Wterm⊆W → Bterm⊆B → W.card ≤ f → 
      (B.card:ℝ) ≤ εabs*n+f → (Z.card:ℝ) ≤ εv*n → (B.card:ℝ) ≤ εv*n+f → 
      Nc ≤ Z.card → Nh ≤ Z.card → Ncol ≤ Z.card → 0<Htest.card → Htest.card ≤ Z.card → (Htest.card:ℝ) ≤ C*Z.card → 
    ∀{R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e) → Type}
      [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)) (E:(Σσ,R σ) → Prop) (lossE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let ν:=FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin);
    1-lossE ≤ (μ.sigma ρ).probability E → 
    1-lossE-χcol-χhub-χglobal-2/(n:ℝ)^q₀-(1/(n:ℝ)+2/(n:ℝ)^2)-χlocal ≤ 
      ((μ.sigma ρ).prod ν).probability (fun z=>
      (∀c:Fin 6,∀x∈Z,
        |(((P.neighborFinset x∩Z).filter (fun y=>(z.1.1 (Sum.inl s(x,y))).1=c)).card:ℝ)-
          markedExpandedPhysicalProbability p 0 p₂ 0 sampling.u c*(P.neighborFinset x∩Z).card|<ζlocal*Z.card) ∧
      ((((E z.1 ∧ (∀v∈Z,|rawIntervalUnassignedColumnCount π d (fun e=>z.1.1 (Sum.inr e)) v Htest-
        ∑w∈Htest,(1-(∑g,q w g)-(∑j,s w j))|<(Z.card:ℝ)^(3/4:ℝ))) ∧ (∀w∈Htest,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1.1 (Sum.inr e)) w Z-
        (Z.card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(Z.card:ℝ)^(3/4:ℝ))) ∧
        OrdinaryZeroRetentionEvent π d false z.1.1) ∧ ∀c x,
        |(sampledColourDegree P (fun e=>(z.1.1 (Sum.inl e)).1) c x:ℝ)-
          markedExpandedPhysicalProbability p 0 p₂ 0 sampling.u c*P.degree x|<(n:ℝ)^(3/5:ℝ)) ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      OrdinaryCorrectedProtectedReservoir r mAbs t a b ξ (rawWheelGraph P raw\Bad) Bad
        (rawWheelSpokes π d raw false) A Z Wterm Bterm B) :=by
  obtain ⟨δ,h,εabs,εv,hδ,hδsmall,hh,hεabs,hεv,hbase⟩:=
    ordinary_matching_correction_both_local_columns r hr α pstar ω hα hpstar hpstar1 hω
  refine ⟨δ,h,εabs,εv,hδ,hδsmall,hh,hεabs,hεv,?_⟩
  intro d hd L hL ξ hξ hξh mAbs
  obtain ⟨a,b,hbase⟩:=hbase d hd L hL ξ hξ hξh mAbs
  refine ⟨a,b,?_⟩
  intro t f q₀
  obtain ⟨N,hN,hbase⟩:=hbase t f q₀
  refine ⟨N,hN,?_⟩
  intro ζlocal χlocal χglobal χhub χcol C hζlocal hχlocal hχglobal hχhub hχcol hC
  obtain ⟨Nc,Ng,Nh,Ncol,hNc,hNg,hNh,hNcol,hbase⟩:=hbase ζlocal χlocal χglobal χhub χcol C hζlocal hχlocal hχglobal hχhub hχcol hC
  refine ⟨Nc,Ng,Nh,Ncol,hNc,hNg,hNh,hNcol,?_⟩
  intro n qCount K D hn hng hωn hqn hD P Bad hreg hdegree hBad π hconf hnoshort
    F hF i₀ rsv θ ρ₀ smin mMatch sampling p p₂ q s hρ₀ hρlo hdegreeHalf hpmin
    A Z Wterm W Bterm B Htest hA hZ hsize hWW hBB hW hB hZsmall hBsmall hZlarge hZhub hZcol hHpos hHle hHtest R _ ρ E lossE μ ν hE
  obtain ⟨_,_,hpR,hrsv,hrsv1,hpEq,hs,hzero⟩:=
    ordinary_assigned_reservoir_rate_inputs F hF P hreg hD K i₀ rsv θ ((mMatch:ℝ)+1) ρ₀ smin pstar d
      hρ₀ hρlo hdegreeHalf hpstar.le hpmin sampling
  have hcall:=hbase (Fin n) (Fin qCount) Bool Bool
  have hFin:(fun (a b:Fin n)=>Classical.propDecidable (a=b))=instDecidableEqFin n:=Subsingleton.elim _ _
  rw [hFin] at hcall
  have hh:=hcall (by simpa using hn) (by simpa using hng)
    (by simpa using hωn) (by simpa using hqn) P Bad D hreg hD (by simpa using hdegree) hBad π hconf hnoshort
    p 0 p₂ 0 sampling.u sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum rsv hpR hrsv hrsv1 hpEq
    q sampling.hq sampling.hQ false hzero s sampling.hs sampling.hS false hs
    A Z Wterm W Bterm B Htest hA (by simpa using hZ) hsize hWW hBB hW (by simpa using hB)
    (by simpa using hZsmall) (by simpa using hBsmall) hZlarge hZhub hZcol hHpos hHle hHtest ρ E lossE hE
  simpa only [Fintype.card_fin] using hh
end Oberwolfach
