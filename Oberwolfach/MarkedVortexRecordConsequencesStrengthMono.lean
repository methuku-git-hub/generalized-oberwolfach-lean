module

public import Oberwolfach.MarkedVortexCorrectedRecordConsequences
public import Oberwolfach.MarkedReferenceStrengthMono

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
theorem marked_vortex_record_consequences_strength_mono
    (r h k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σglobal:RawMarkedOutcome V U Γ Color) (Hglobal:Bool→V→U→Prop)
    (βA βrec κ thetaDeep etaBal x eta deltaI hIcut α':ℝ)
    (hα:α'≤α) (hρ:0 ≤ initialIndexDensity U D) (hs₀:0≤s₀)
    (hOld:MarkedVortexCorrectedRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal βA βrec κ thetaDeep etaBal x eta deltaI hIcut):
    MarkedVortexCorrectedRecordConsequences r h k₀ d α' ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal βA βrec κ thetaDeep etaBal x eta deltaI hIcut :=by
  unfold MarkedVortexCorrectedRecordConsequences at hOld ⊢
  rcases hOld with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  refine ⟨h1,h2,?_,h4,h5,h6,h7,h8⟩
  intro i hi W Z f g ρ rho c t pRef kRef DRef σ
  have hp:0≤pRef:=by dsimp [pRef,rho,c,t]; positivity
  have hk:0≤kRef:=by dsimp [kRef,pRef,rho,c,t]; positivity
  have ha:2*(α'/16)≤2*(α/16):=by linarith
  obtain ⟨hs,hc⟩:=h3 i hi
  exact ⟨marked_reference_statistics_strength_mono (G.comap f) ρ d a j DRef (κ/4) κ (2*(α/16)) (2*(α'/16)) pRef kRef (c*t) t σ ha hs,
    marked_reference_cut_strength_mono (G.comap f) ρ d a j (2*(α/16)) (2*(α'/16)) pRef kRef t σ ha hp hk hc⟩
end Oberwolfach
