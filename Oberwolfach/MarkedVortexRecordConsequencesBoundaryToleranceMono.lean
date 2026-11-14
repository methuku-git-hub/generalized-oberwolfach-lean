module

public import Oberwolfach.MarkedVortexCorrectedRecordConsequences

@[expose] public section

/-! The record extracted from a stronger parent event can be used at a
smaller density parameter while keeping all weights and samples fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
theorem marked_vortex_record_consequences_boundary_tolerance_mono
    (r h k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σglobal:RawMarkedOutcome V U Γ Color) (Hglobal:Bool→V→U→Prop)
    (βA βrec κ thetaDeep etaBal x eta deltaI hIcut x':ℝ)
    (hx:x≤x')
    (hOld:MarkedVortexCorrectedRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal βA βrec κ thetaDeep etaBal x eta deltaI hIcut):
    MarkedVortexCorrectedRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal βA βrec κ thetaDeep etaBal x' eta deltaI hIcut :=by
  unfold MarkedVortexCorrectedRecordConsequences at hOld ⊢
  rcases hOld with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  refine ⟨h1,h2,h3,h4,?_,h6,h7,?_⟩
  · intro i hi W Z f g ρ σ H E K S I J T R bal
    obtain ⟨errI,errT,ht,hi,ht',hI,hT,hRel⟩:=h5 i hi
    have hb:(x/2)*Fintype.card W≤(x'/2)*Fintype.card W:=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    exact ⟨errI,errT,ht,hi.trans hb,ht'.trans hb,hI,hT,hRel⟩
  · intro i hi W Z fP gP ρ fA f gA X Zinner ω H
    obtain ⟨errR,errI,hr,hi,hrX,hiX,hrow,hindex⟩:=h8 i hi
    have hb:(x/2)*Fintype.card W≤(x'/2)*Fintype.card W:=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    exact ⟨errR,errI,hr,hi,hrX.trans hb,hiX.trans hb,hrow,hindex⟩
end Oberwolfach
