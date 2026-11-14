module

public import Oberwolfach.MarkedVortexCorrectedRecordConsequences
public import Oberwolfach.MarkedReferenceEpsilonMonotone
public import Oberwolfach.MarkedReferenceStatisticsDeltaMonotone
public import Oberwolfach.MarkedCommonConfigurationsAfterHostChange
public import Oberwolfach.MarkedSpokeToleranceMonotone

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
theorem marked_vortex_record_consequences_tolerance_mono
    (r h k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σglobal:RawMarkedOutcome V U Γ Color) (Hglobal:Bool→V→U→Prop)
    (βA βrec κ thetaDeep etaBal x eta deltaI hIcut κ':ℝ)
    (hκ:κ≤κ')
    (hOld:MarkedVortexCorrectedRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal βA βrec κ thetaDeep etaBal x eta deltaI hIcut):
    MarkedVortexCorrectedRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal βA βrec κ' thetaDeep etaBal x eta deltaI hIcut :=by
  unfold MarkedVortexCorrectedRecordConsequences at hOld ⊢
  rcases hOld with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  have hk:κ/4≤κ'/4:=by linarith
  refine ⟨?_,?_,?_,?_,h5,h6,h7,h8⟩
  · intro i hi fP gP fA f gA ρP ρ σP HP
    obtain ⟨hc,hl,ha⟩:=h1 i hi
    exact ⟨marked_common_configurations_error_mono r (G.comap fP) ρP d βA (κ/4) (κ'/4) σP HP hk hc,hl,ha⟩
  · intro i hi W Z f g ρ σ H
    obtain ⟨hr,ht,hrow,hcol⟩:=h2 i hi
    have hW:(κ/4)*Fintype.card W≤(κ'/4)*Fintype.card W:=mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg _)
    have hZ:(κ/4)*Fintype.card Z≤(κ'/4)*Fintype.card Z:=mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg _)
    refine ⟨marked_rows_with_spokes_tolerance_mono (G.comap f) ρ d (r+12) Finset.univ p kval _ _ a j _ _ σ H hW hr,?_,?_,?_⟩
    · exact marked_indices_with_spokes_tolerance_mono ρ d (r+12) Finset.univ _ _ a j _ _ σ H hW ht
    · intro b v;exact (hrow b v).trans hZ
    · intro b u;exact (hcol b u).trans hW
  · intro i hi W Z f g ρ rho c t pRef kRef DRef σ
    obtain ⟨hs,hc⟩:=h3 i hi
    have hs':=marked_reference_statistics_epsilon_mono (G.comap f) ρ d a j DRef (κ/4) (κ'/4) κ _ pRef kRef (c*t) t σ hk hs
    exact ⟨marked_reference_statistics_delta_mono (G.comap f) ρ d a j DRef (κ'/4) κ κ' _ pRef kRef (c*t) t σ hκ hs',hc⟩
  · intro i hi W Z P ρ Dload σ H qi si
    obtain ⟨hl,hp⟩:=h4 i hi
    refine ⟨hl,?_⟩
    intro seed root hm
    exact (hp root hm).trans hk
end Oberwolfach
