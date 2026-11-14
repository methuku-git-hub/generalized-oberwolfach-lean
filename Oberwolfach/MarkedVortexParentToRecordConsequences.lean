module

public import Oberwolfach.MarkedVortexCorrectedRecordConsequences

@[expose] public section
/-! The parent event supplies the record bundle at its own retained outcome;
the weights are exactly the original parent and active-level weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_vortex_parent_to_record_consequences
    (r h k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hGood:MarkedVortexParentRecordEvent r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z):
    let pstarLocal:=ρ₀*sstar/(2*((r+4:ℕ):ℝ));
    ∀ βA βrec κ:ℝ, βA≤βCommon → ζCommon≤κ/4 →
      3*βA≤markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*ζCfg →
      3*βA≤markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*ζCfg →
      βrec≤βA → tolRef+(r+12:ℕ)*ζActive≤κ/4 → ζActive≤κ/4 → εref=κ/4 → δref=κ →
      ∀ thetaDeep:ℝ,
      τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*ζParent≤κ/4 →
      τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*ζParent≤thetaDeep/4 →
      ∀ etaBal x:ℝ,0≤x → epsBal+((r+4)+2:ℕ)*ζBal≤etaBal →
      epsBal+((r+4)+2:ℕ)*ζBal≤x/2 → L+1=Q.length →
      ∀ eta:ℝ, rowErr+ζRow≤(s₀/((r+4:ℕ):ℝ))/8 →
      τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*(4/ε)*ζWide≤eta/4 →
      ∀ deltaI hIcut:ℝ, β≤1/4 → 0≤hIcut → deltaI≤(α/2)/32 → deltaI≤kstar/32 →
      2*deltaI≤tstar/8 → 2*hIcut≤(α/2)*kstar/4 → 2*hIcut≤tstar/8-ζCut →
      tolRef+h*ζActive≤x/2 →
      MarkedVortexCorrectedRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
        εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
        size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z.1
        (retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j)
        βA βrec κ thetaDeep etaBal x eta deltaI hIcut:=by
  intro pstarLocal βA βrec κ hβA hζ hcycle hpath hrec htol hactive href hdelta thetaDeep hp hdeep etaBal x hx hbal hbalx hlength eta hrow hwide deltaI hIcut hβ hcut hδ1 hδ2 hδ3 hδ4 hδ5 hlast
  have h:=marked_vortex_parent_record_event_fields r h k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z hGood
  unfold MarkedVortexCorrectedRecordConsequences
  exact h βA βrec κ hβA hζ hcycle hpath hrec htol hactive href hdelta thetaDeep hp hdeep etaBal x hx hbal hbalx hlength eta hrow hwide deltaI hIcut hβ hcut hδ1 hδ2 hδ3 hδ4 hδ5 hlast
end Oberwolfach
