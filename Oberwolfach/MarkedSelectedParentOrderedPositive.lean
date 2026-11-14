module

public import Oberwolfach.MarkedSelectedParentOrderedHalfScaleRecord

@[expose] public section
/-! The selector's fixed parent and active weights give the smaller record
on the selected retained sample. The tolerance is chosen before the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_selected_parent_ordered_half_scale_record_positive
    (r k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref ε εBal ζBal:ℝ)
    (βA βrec ζCfg upper cutGap xBudget κ theta eta:ℝ)
    (hζ:0<ζCfg) (ht:0<tstar) (hupper:0<upper) (hcut:0<cutGap) (hxBudget:0<xBudget) (htheta:0<theta) (hη:0<eta) (hκ:0<κ)
    (hβ:βrec≤βA) (hβA:βA≤βCommon)
    (hcycle:3*βA≤markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*ζCfg)
    (hpath:3*βA≤markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*ζCfg)
    (hαpos:0<α) (hρpos:0<ρ₀) (hspos:0<sstar) (hεpos:0<ε)
    (hεref:εref≤κ/8):
    ∃δ:ℝ,0<δ ∧ δ≤upper ∧ δ≤cutGap ∧ δ+(r+12:ℕ)*δ≤xBudget/2 ∧ 2*δ≤ζCfg ∧ δ+δ≤tstar/16 ∧
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
    2*hIcut≤(α/2)*kstar/4→2*hIcut+cutGap≤tstar/8→xBudget≤x→
    MarkedVortexCorrectedRecordConsequences r (r+12) k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref (κ/2) δ δ δ δ δ δ δ δ εBal ζBal δ δ δ δ δ δ
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z.1
      (retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j)
      βA βrec (κ/2) (theta/2) etaBal x eta deltaI hIcut :=by
  have hUpper:0<successorWeightUpper k₀ (α/4):=(successorWeightConstants_pos k₀ (α/4) (by positivity)).2
  have hCp:0≤11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1)):=by positivity
  have hCw:0≤5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε):=by positivity
  exact marked_selected_parent_ordered_half_scale_record r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref ε εBal ζBal βA βrec ζCfg upper cutGap xBudget κ theta eta
    hζ ht hupper hcut hxBudget htheta hη hκ hβ hβA hcycle hpath hCp hCw hεref
end Oberwolfach
