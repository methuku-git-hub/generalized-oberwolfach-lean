module

public import Oberwolfach.MarkedVortexCorrectedRecordConsequences
public import Oberwolfach.MarkedLocalPrerequisiteMonotone

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
theorem marked_vortex_record_consequences_spoke_tolerance_mono
    (r h k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σglobal:RawMarkedOutcome V U Γ Color) (Hglobal:Bool→V→U→Prop)
    (βA βrec κ thetaDeep etaBal x eta deltaI hIcut theta' eta':ℝ)
    (hθ:thetaDeep≤theta') (hη:eta≤eta')
    (hOld:MarkedVortexCorrectedRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal βA βrec κ thetaDeep etaBal x eta deltaI hIcut):
    MarkedVortexCorrectedRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal βA βrec κ theta' etaBal x eta' deltaI hIcut :=by
  unfold MarkedVortexCorrectedRecordConsequences at hOld ⊢
  rcases hOld with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  refine ⟨h1,h2,h3,?_,h5,?_,h7,h8⟩
  · intro i hi W Z P ρ Dload σ H qi si
    obtain ⟨hl,hpot⟩:=h4 i hi
    refine ⟨?_,hpot⟩
    exact marked_local_spoke_loads_tolerance_mono P ρ d (r+4) Dload p kval s₀ (weightParent i)
      (thetaDeep/4) (theta'/4) σ H (by linarith) hl
  · intro i hi Z Zkeep fP gP fA f gA ρ σP HP
    obtain ⟨hrow,hload⟩:=h6 i hi
    refine ⟨hrow,?_⟩
    exact marked_local_spoke_loads_tolerance_mono _ ρ d (r+4) _ p kval s₀ (weight (i+1))
      (eta/4) (eta'/4) _ _ (by linarith) hload
end Oberwolfach
