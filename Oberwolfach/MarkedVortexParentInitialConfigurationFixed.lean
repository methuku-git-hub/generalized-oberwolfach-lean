module

public import Oberwolfach.MarkedVortexParentInitialConfiguration
public import Oberwolfach.MarkedLocalPrerequisiteMonotone
public import Oberwolfach.MarkedVortexParentRecordSmallerReferenceEvent

@[expose] public section
/-! Project the first parent-level configuration event without expanding the
entire event in later correction proofs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_vortex_parent_initial_configuration_fixed
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
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z)
    (ζFixed:ℝ) (hCfg:2*ζCfg≤ζFixed)
    (σold:RawMarkedOutcome V U Γ Color) (Hold:Bool→V→U→Prop)
    (hraw:σold=z.1)
    (hspokes:Hold=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j):
    MarkedLocalConfigurationsWithSpokes r
      (G.comap (markedVortexVertexEmbedding Q 0)) (markedVortexPermutation Q π hpres 0) d Finset.univ
      (markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*(ζFixed/2))
      (markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*(ζFixed/2))
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σold)
      (fun b v u=>Hold b (markedVortexVertexEmbedding Q 0 v) (markedVortexHubEmbedding Q 0 u)) :=by
  have hcfg:=marked_vortex_parent_initial_configuration r h k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z hGood
  have hmC:markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*(ζFixed/2) ≤
      markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*ζCfg:=by
    have hh:=mul_le_mul_of_nonneg_left (show ζCfg≤ζFixed/2 by linarith) (show (0:ℝ)≤(r+5:ℕ) by positivity)
    linarith only [hh]
  have hmP:markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*(ζFixed/2) ≤
      markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*ζCfg:=by
    have hh:=mul_le_mul_of_nonneg_left (show ζCfg≤ζFixed/2 by linarith) (show (0:ℝ)≤(r+4:ℕ) by positivity)
    linarith only [hh]
  have hfixed:=marked_local_configurations_with_spokes_mono r
    (G.comap (markedVortexVertexEmbedding Q 0)) (markedVortexPermutation Q π hpres 0) d Finset.univ
    (markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*ζCfg)
    (markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*ζCfg)
    (markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*(ζFixed/2))
    (markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*(ζFixed/2))
    (rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) z.1)
    (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
      (markedVortexVertexEmbedding Q 0 x) (markedVortexHubEmbedding Q 0 u)) hmC hmP hcfg
  simpa only [hraw,hspokes] using hfixed
end Oberwolfach
