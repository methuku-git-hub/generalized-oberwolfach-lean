module

public import Oberwolfach.OrdinaryCorrectedProtectedReservoir
public import Oberwolfach.OrdinaryReservoirProtectionUniformBudget
public import Oberwolfach.OrdinaryGlobalBalanceUniformMargin
public import Oberwolfach.OrdinaryGlobalMeanFromDensity

@[expose] public section
/-! Choose the sample and protection tolerances before the host and derive
both the sparse-correction error and finite reservoir budget uniformly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uniform_sample_reservoir_correction
    (r:ℕ) (hr:3≤r) (ω h δ ξ:ℝ)
    (hω:0<ω) (hh:0<h) (hδ:0<δ) (hδsmall:δ<1/4) (hξ:0<ξ) (hξh:ξ≤h/100):
    ∃εsample εv ζ:ℝ,0<εsample ∧ 0<εv ∧ 0<ζ ∧ ζ≤h ∧
    ∀(L:ℝ),0≤L→∀(m t f a b:ℕ),∃N:ℕ,1≤N ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→0<Fintype.card V→0<Fintype.card U→
      ω*Fintype.card V≤(Fintype.card U:ℝ)→Fintype.card U≤Fintype.card V→
    ∀(P F:SimpleGraph V) (D:ℕ),P.IsRegularOfDegree D→0<D→
    ∀(π:Equiv.Perm V) (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool)
      (pR pH:ℝ) (s:U→Color→ℝ),pR=initialIndexDensity U D*pH→
      RawOrdinaryRows P π d 2 Finset.univ pR s j (εsample*Fintype.card V) σ→
      RawOrdinaryDomainIndices F π d 3 Finset.univ pH j (εsample*Fintype.card U) σ→
      (∀v,(F.degree v:ℝ)≤L)→OrdinaryTriangleReferenceMatrixCuts P F π d j δ h σ coins→
    ∀(εabs:ℝ) (A Z Wterm W:Finset V) (Bterm B:Finset U),
      A=Finset.univ\Z→(Z.card:ℝ)≤εabs*Fintype.card V→
      Wterm.card+Bterm.card≤t→Wterm⊆W→Bterm⊆B→W.card≤f→
      (B.card:ℝ)≤εabs*Fintype.card V+f→
      (Z.card:ℝ)≤εv*Fintype.card V→(B.card:ℝ)≤εv*Fintype.card V+f→
    let Q:=rawWheelGraph P σ\F; let H:=rawWheelSpokes π d σ j;
    OrdinaryUniformProtectedReservoirEvent r m t f a b εabs Q F H→
    OrdinaryCorrectedProtectedReservoir r m t a b ξ Q F H A Z Wterm Bterm B :=by
  let par:=ordinarySparseCorrectionParameters r hr ω h δ ξ hω hh hδ hδsmall hξ hξh
  have hη:0<par.1:=(ordinary_sparse_correction_parameters_spec r hr ω h δ ξ hω hh hδ hδsmall hξ hξh).1
  obtain ⟨εsample,hεsample,hmargin⟩:=ordinary_global_balance_uniform_margin par.1 hη
  obtain ⟨εv,ζ,hεv,hζ,hζh,hprotect⟩:=ordinary_reservoir_protection_uniform_budget ω h hω hh
  refine ⟨εsample,εv,ζ,hεsample,hεv,hζ,hζh,?_⟩
  intro L hL m t f a b
  obtain ⟨Nbal,hNbal,hmargin⟩:=hmargin L hL
  obtain ⟨Npro,hNpro,hprotect⟩:=hprotect f a b t
  let N:=max par.2 (max Nbal Npro)
  refine ⟨N,by dsimp [N];omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hnpos hupos hωn hUn P F D hreg hD π d j σ coins pR pH s hp hrows hcols hF hcuts
    εabs A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB hZsmall hBsmall Q H hRes
  have hmean:=ordinary_global_mean_from_density U D hD pR pH hp
  have hbudget:=hmargin (Fintype.card V) (Fintype.card U) (by dsimp [N] at hn;omega) hUn
  have hpairs:=hprotect V U Z B εv (by dsimp [N] at hn;omega) hωn hεv.le (le_refl _) hZsmall hBsmall
  have hout:=ordinary_sample_reservoir_and_protected_correction r m t f a b hr εabs ω h δ ξ hω hh hδ hδsmall hξ hξh
    V U Γ Color par.1 hη.le (le_refl _) (by dsimp [N] at hn;exact le_trans (le_max_left _ _) hn)
    hnpos hupos hωn hUn P F D hreg π d j σ coins pR pH (εsample*Fintype.card V) (εsample*Fintype.card U) L s
    (by positivity) (by positivity) hL hmean hrows hcols hF hbudget hcuts
    A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB ζ hζ.le hζh hpairs.1 hpairs.2 hRes
  change _ at hout
  unfold OrdinaryCorrectedProtectedReservoir
  convert hout using 1 <;> congr! 50
end Oberwolfach
