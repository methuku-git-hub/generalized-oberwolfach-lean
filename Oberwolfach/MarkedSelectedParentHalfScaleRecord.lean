module

public import Oberwolfach.MarkedParentRefinedLevelMargins
public import Oberwolfach.MarkedVortexSmallerParentToRecordConsequences

@[expose] public section
/-! The selector's fixed parent and active weights give the smaller record
on the selected retained sample. The tolerance is chosen before the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_selected_parent_half_scale_record
    (r k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref ε εBal ζBal:ℝ)
    (βA βrec ζCfg δ₀ κ theta eta:ℝ)
    (hζ:0<ζCfg) (ht:0<tstar) (hδ₀:0<δ₀) (hη:0<eta) (hκ:0<κ)
    (hβ:βrec≤βA) (hβA:βA≤βCommon)
    (hcycle:3*βA≤markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*ζCfg)
    (hpath:3*βA≤markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*ζCfg)
    (hCp:0≤11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1)))
    (hCw:0≤5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε))
    (hκbudget:δ₀+(r+12:ℕ)*δ₀≤κ/4)
    (hpκ:δ₀+δ₀+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*δ₀≤κ/4)
    (hpθ:δ₀+δ₀+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*δ₀≤theta/4)
    (hεref:εref≤κ/8):
    ∃δ:ℝ,0<δ ∧ δ≤δ₀ ∧ 2*δ≤ζCfg ∧ δ+δ≤tstar/16 ∧
      δ+δ+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*δ≤eta/8 ∧
      3*βrec≤markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*(2*δ) ∧
      3*βrec≤markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*(2*δ) ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    ∀(size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β:ℝ)
      (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
      (hpres:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
      (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
      (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
      (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
      (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a),
    MarkedVortexParentRecordSmallerReferenceEvent r (r+12) k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref (κ/2) δ δ δ δ δ δ δ δ εBal ζBal δ δ δ δ δ δ
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z→
    ∀(etaBal x deltaI hIcut:ℝ),
    0≤x→εBal+((r+4)+2:ℕ)*ζBal≤etaBal→εBal+((r+4)+2:ℕ)*ζBal≤x/2→
    L+1=Q.length→tstar≤s₀/((r+4:ℕ):ℝ)→β≤1/4→0≤hIcut→
    deltaI≤(α/2)/32→deltaI≤kstar/32→2*deltaI≤tstar/8→
    2*hIcut≤(α/2)*kstar/4→2*hIcut≤tstar/8-δ→δ+(r+12:ℕ)*δ≤x/2→
    MarkedVortexCorrectedRecordConsequences r (r+12) k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref (κ/2) δ δ δ δ δ δ δ δ εBal ζBal δ δ δ δ δ δ
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z.1
      (retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j)
      βA βrec (κ/2) (theta/2) etaBal x eta deltaI hIcut :=by
  obtain ⟨δ,hδ,hδup,hcfg,hrow,hwide,hkb,hpk,hpt,hcy2,hpa2⟩:=
    marked_parent_refined_level_margins r βA βrec
      (markedLocalCycleCoefficient r (α/2) (tstar/2) kstar)
      (markedLocalPathCoefficient r (α/2) (tstar/2) kstar) ζCfg tstar δ₀ κ theta eta
      (11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1)))
      (5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε))
      hζ ht hδ₀ hη hCp hCw hβ hcycle hpath hκbudget hpκ hpθ
  refine ⟨δ,hδ,hδup,hcfg,hrow,hwide,hcy2,hpa2,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ size a₀ b₀ e₀ f₀ G D m β Q π hpres L s₀ p kval q s a j weightParent weight z hGood etaBal x deltaI hIcut hx hbal hmargin hlength htbound hb hh hδα hδstar hδt hhstar hhs hend
  have hnat:(0:ℝ)≤(r+12:ℕ):=by positivity
  have hnprod:0≤((r+12:ℕ):ℝ)*δ:=mul_nonneg hnat hδ.le
  have hsmall:δ≤κ/8:=by linarith
  have hcy:3*βA≤markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*δ:=by
    have hm:=mul_le_mul_of_nonneg_left (show δ≤ζCfg by linarith) (show (0:ℝ)≤(r+5:ℕ) by positivity)
    linarith only [hcycle,hm]
  have hpa:3*βA≤markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*δ:=by
    have hm:=mul_le_mul_of_nonneg_left (show δ≤ζCfg by linarith) (show (0:ℝ)≤(r+4:ℕ) by positivity)
    linarith only [hpath,hm]
  apply marked_vortex_smaller_parent_to_record_consequences r (r+12) k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref (κ/2) δ δ δ δ δ δ δ δ εBal ζBal δ δ δ δ δ δ
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z hGood
    βA βrec (κ/2) hβA (by linarith) hcy hpa hβ (by linarith) (by linarith) (by linarith) rfl
    (theta/2) (by linarith) (by linarith) etaBal x hx hbal hmargin hlength eta
    (by linarith) (by linarith) deltaI hIcut hb hh hδα hδstar hδt hhstar hhs hend
end Oberwolfach
