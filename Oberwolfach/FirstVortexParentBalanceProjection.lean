module

public import Oberwolfach.MarkedVortexParentRecordSmallerReferenceEvent

@[expose] public section
/-! The selected parent event itself carries the inner and deeper balance
conditions on the identical retained outcome and with its actual weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem first_vortex_parent_balance_projection
    (r h k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hGood:MarkedVortexParentRecordSmallerReferenceEvent r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent
      epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z):
    MarkedActualVortexBalanceProperty Q π hpres d (r+4) L a j epsBal ζBal
      (markedVortexInnerVertices Q) (markedVortexInnerHubs Q) z ∧
    (L=0 ∨ MarkedActualVortexBalanceProperty Q π hpres d (r+4) (L-1) a j epsBal ζBal
      (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) z) :=by
  exact ⟨hGood.1,hGood.2.1⟩
end Oberwolfach
