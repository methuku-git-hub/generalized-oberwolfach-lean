module

public import Oberwolfach.MarkedVortexNestedActiveRowsInput
public import Oberwolfach.MarkedActualNextActiveNonDeeperHubsRowsEvent
public import Oberwolfach.MarkedVortexNonDeeperGeometry
public import Oberwolfach.RawMarkedPairNestedRims
public import Oberwolfach.MarkedRowsRimEquality
public import Oberwolfach.MarkedSpokeToleranceMonotone

@[expose] public section
/-! Transfer direct active-vertex, non-deeper-hub rows to the parent record's
nested physical representation, preserving the active error scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_nested_active_rows_arbitrary_spokes
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (i d:ℕ) (p k t err:ℝ) (herr:err≤t/8)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hrow:MarkedRowsWithSpokes (G.comap (markedVortexActiveVertexEmbedding Q (i+1)))
      (markedVortexActivePermutation Q π hπ (i+1)) d 1 Finset.univ p k
      (fun u=>q (markedVortexNonDeeperHubToPhysical Q i u))
      (fun u=>s (markedVortexNonDeeperHubToPhysical Q i u)) a j
      (err*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1))))
      (rawMarkedRestrictPair (markedVortexActiveVertexEmbedding Q (i+1)) (markedVortexNonDeeperHubToPhysical Q i) σ)
      (fun b x u=>H b
        (markedVortexActiveVertexEmbedding Q (i+1) x) (markedVortexNonDeeperHubToPhysical Q i u))):
    let Z:=markedVortexHubType Q i
    let Zkeep:=markedVortexNonDeeperHubType Q i
    let fP:=markedVortexVertexEmbedding Q i
    let gP:=markedVortexHubEmbedding Q i
    let fA:=markedVortexNonDeeperVertexEmbedding Q i
    let f:=markedVortexNextActiveInNonDeeper Q i
    let gA:Zkeep→Z:=Subtype.val
    let ρ:=markedVortexActivePermutation Q π hπ (i+1)
    let σP:=rawMarkedRestrictPair fP gP σ
    let HP:=fun b x u=>H b (fP x) (gP u);
    MarkedRowsWithSpokes ((G.comap fP).comap (fun x=>fA (f x))) ρ d 1 Finset.univ p k
      (fun u=>q (gP (gA u))) (fun u=>s (gP (gA u))) a j
      ((t/8)*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1))))
      (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP) (fun b x u=>HP b (fA (f x)) (gA u)):=by
  intro Z Zkeep fP gP fA f gA ρ σP HP
  have hrim (e:Sym2 _):
      rawMarkedRestrictPair (fun x=>fA (f x)) gA σP (Sum.inl e)=
      rawMarkedRestrictPair (markedVortexActiveVertexEmbedding Q (i+1)) (markedVortexNonDeeperHubToPhysical Q i) σ (Sum.inl e):=by
    exact rawMarked_pair_nested_rims fP (fun x=>fA (f x)) gP gA σ e
  have he:=marked_rows_with_spokes_rim_equality (G.comap (markedVortexActiveVertexEmbedding Q (i+1))) ρ d 1 Finset.univ p k
    (fun u=>q (markedVortexNonDeeperHubToPhysical Q i u)) (fun u=>s (markedVortexNonDeeperHubToPhysical Q i u)) a j _
    (rawMarkedRestrictPair (markedVortexActiveVertexEmbedding Q (i+1)) (markedVortexNonDeeperHubToPhysical Q i) σ)
    (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP)
    (fun b x u=>H b
        (markedVortexActiveVertexEmbedding Q (i+1) x) (markedVortexNonDeeperHubToPhysical Q i u)) hrim hrow
  apply marked_rows_with_spokes_tolerance_mono _ ρ d 1 Finset.univ p k _ _ a j _ _ _ _ ?_ he
  exact mul_le_mul_of_nonneg_right herr (Nat.cast_nonneg _)
end Oberwolfach
