module

public import Oberwolfach.SuccessorWeightsTheorem
public import Oberwolfach.MarkedReferenceLoadActualSpokeDensity
public import Oberwolfach.MarkedReferenceLoadChosenErrorsEvent
public import Oberwolfach.MarkedReferenceLoadFromDensityBounds
public import Oberwolfach.MarkedJointLoadMargin
public import Oberwolfach.MarkedReferenceDensitiesLoadEvent
public import Oberwolfach.MarkedParentLocalLoadExtraEvent
public import Oberwolfach.MarkedSeedDensities

@[expose] public section
/-! Full-parent marked loads under the reference normalization, intersected
with an arbitrary event of the same retained sampling law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem marked_parent_reference_load_with_constructed_weights
    (r d:ℕ) (hd:2≤d) (heven:Even (r+5)) (β:ℝ) (hβ:0<β) (rho t ρstar sstar K eta χ Q pret κ θ ω:ℝ)
    (hρ:0<rho) (ht:0<t) (hω:0<ω) (hρstar:0<ρstar) (hsstar:0<sstar)
    (hρlo:ρstar≤rho) (hρhi:rho≤1) (hslo:sstar≤((r+4:ℕ):ℝ)*t) (hshi:((r+4:ℕ):ℝ)*t≤1/100)
    (hκ:0<κ) (hθ:0<θ) (hK:1≤K)
    (heta:0<eta) (heta1:eta<1) (hχ:0<χ) (hpret:0<pret):
    let m:=r+4;
    let s₀:ℝ:=m*t;
    let pRef:ℝ:=rho*s₀/2;
    let kRef:ℝ:=pRef/m;
    let pstar:ℝ:=ρstar*sstar/(2*m);
    ∃ A B τ ε ζ εreg:ℝ,0<A ∧ 0<B ∧ 0<τ ∧ 0<ε ∧ 0<ζ ∧ 0<εreg ∧ ∃ N:ℕ,1≤N ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),
    (∀ x l,0<l→l<2*d+1→(π^l) x≠x) →
    let DRef:ℝ:=2*Fintype.card U/rho;
    (Fintype.card V:ℝ)/2≤DRef → DRef≤2*Fintype.card V →
    (∀ v,|(P.degree v:ℝ)-DRef|≤εreg*Fintype.card V) →
    (∀ v,(((r+5:ℕ):ℝ)/(2*((r+5:ℕ):ℝ)-2)+β)*Fintype.card V≤(P.degree v:ℝ)) →
    ∃ weight:(Fin (m+1)→V)→ℝ,SuccessorSequenceWeightConditions P π (3*d) DRef τ A B weight ∧
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Γ) (j:Color),
    (∀ u,q u a=t) → (∀ u,s u j=s₀) → pret*Fintype.card V≤t*Fintype.card U →
    let hp:0<pRef:=by dsimp [pRef,s₀,m]; positivity
    let hk:0<kRef:=by dsimp [kRef,pRef,s₀,m]; positivity
    let hphys:2*pRef+2*kRef≤1:=by
      have hh:=marked_seed_density_bounds m (by dsimp [m];omega) rho s₀ ρstar sstar hρstar hsstar hρlo hρhi (by simpa [m,s₀] using hslo) (by simpa [m,s₀] using hshi)
      exact hh.2.2.2.2.2.2.2.2;
    let μ:=rawMarkedRetentionLaw π d hd a pRef kRef hp.le hk.le hphys q hq hQ s hs hS;
    ∀ Extra:(RawMarkedRetainedOutcome π d a)→Prop,
    μ.probability Extra-χ-(Fintype.card V:ℝ)^(-Q)≤μ.probability (fun z=>Extra z ∧ ((fun z=>
        let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j;
        let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
          (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(DRef*pRef^m*kRef*s₀^m);
        (∀ root,rawMarkedWheelMarginal P π d pRef kRef q s a j root≠0 →
          |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d z.1) H root-1|≤κ/4) ∧
        MarkedLocalSpokeLoadsWithSpokes P π d m DRef pRef kRef s₀ weight (θ/4) z.1 H)) z) := by
  intro m s₀ pRef kRef pstar
  obtain ⟨A,B,hA,hB,hweights⟩:=successor_weights_theorem (r+5) (by omega) heven β hβ
  obtain ⟨τ,ε,ζ,hτ,hε,hζ,Nevt,hNevt,hevt⟩:=marked_reference_load_with_actual_spoke_density r d hd rho t B ρstar sstar K eta χ Q pret κ θ ω
    hρ ht hω hB hρstar hsstar hρlo hρhi hslo hshi hκ hθ hK heta heta1 hχ hpret
  obtain ⟨εreg,hεreg,hweights⟩:=hweights τ hτ
  obtain ⟨Nweight,hweights⟩:=hweights (3*d) (by omega)
  refine ⟨A,B,τ,ε,ζ,εreg,hA,hB,hτ,hε,hζ,hεreg,max Nevt Nweight,le_trans hNevt (le_max_left _ _),?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn hU hUV P π hnoshort DRef hDlo hDhi hnear hmin
  obtain ⟨weight,hw⟩:=hweights V (by omega) P π DRef hDlo hDhi hnear hmin
  have hweq:(m+1)=(r+5):=by dsimp [m]
  have hw':∃ weight:(Fin (m+1)→V)→ℝ,SuccessorSequenceWeightConditions P π (3*d) DRef τ A B weight:=by
    simpa only [hweq] using (show ∃ weight:(Fin (r+5)→V)→ℝ,SuccessorSequenceWeightConditions P π (3*d) DRef τ A B weight from ⟨weight,hw⟩)
  obtain ⟨weight,hw⟩:=hw'
  refine ⟨weight,hw,?_⟩
  intro q hq hQ s hs hS a j ha hj hmass hp hk hphys μ Extra
  exact hevt V U Γ Color (by omega) hU hUV P π hnoshort A hDlo hDhi weight hw q hq hQ s hs hS a j ha hj hmass Extra
end Oberwolfach
