module

public import Oberwolfach.MarkedVortexNestedActiveRowsInput
public import Oberwolfach.MarkedVortexNestedActiveLoadInput

@[expose] public section
/-! The direct row and load estimates for the same retained outcome give
both active level-record inputs with the same nested physical maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_nested_active_rows_and_loads
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L d c:ℕ) (p k s₀ t rowErr loadErr η:ℝ) (hrowErr:rowErr≤t/8) (hloadErr:loadErr≤η/4)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (Dnext:ℕ→ℝ)
    (weight:∀ i,(Fin (c+1)→↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1))))→ℝ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hrow:∀ i≤L,
      MarkedRowsWithSpokes (G.comap (markedVortexActiveVertexEmbedding Q (i+1)))
        (markedVortexActivePermutation Q π hπ (i+1)) d 1 Finset.univ p k
        (fun u=>q (markedVortexNonDeeperHubToPhysical Q i u))
        (fun u=>s (markedVortexNonDeeperHubToPhysical Q i u)) a j
        (rowErr*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1))))
        (rawMarkedRestrictPair (markedVortexActiveVertexEmbedding Q (i+1)) (markedVortexNonDeeperHubToPhysical Q i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
          (markedVortexActiveVertexEmbedding Q (i+1) x) (markedVortexNonDeeperHubToPhysical Q i u)))
    (hload:∀ i≤L,
      MarkedLocalSpokeLoadsWithSpokes (G.comap (markedVortexActiveVertexEmbedding Q (i+1)))
        (markedVortexActivePermutation Q π hπ (i+1)) d c (Dnext i) p k s₀ (weight i) loadErr
        (rawMarkedRestrictPair (markedVortexActiveVertexEmbedding Q (i+1)) (markedVortexNonDeeperHubToPhysical Q i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
          (markedVortexActiveVertexEmbedding Q (i+1) x) (markedVortexNonDeeperHubToPhysical Q i u))):
    ∀ i≤L,
      let Z:=markedVortexHubType Q i
      let Zkeep:=markedVortexNonDeeperHubType Q i
      let fP:=markedVortexVertexEmbedding Q i
      let gP:=markedVortexHubEmbedding Q i
      let fA:=markedVortexNonDeeperVertexEmbedding Q i
      let f:=markedVortexNextActiveInNonDeeper Q i
      let gA:Zkeep→Z:=Subtype.val
      let ρ:=markedVortexActivePermutation Q π hπ (i+1)
      let σP:=rawMarkedRestrictPair fP gP z.1
      let HP:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fP x) (gP u);
      MarkedRowsWithSpokes ((G.comap fP).comap (fun x=>fA (f x))) ρ d 1 Finset.univ p k
        (fun u=>q (gP (gA u))) (fun u=>s (gP (gA u))) a j
        ((t/8)*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1))))
        (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP) (fun b x u=>HP b (fA (f x)) (gA u)) ∧
      MarkedLocalSpokeLoadsWithSpokes ((G.comap fP).comap (fun x=>fA (f x))) ρ d c (Dnext i) p k s₀ (weight i) (η/4)
        (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP) (fun b x u=>HP b (fA (f x)) (gA u)):=by
  intro i hi Z Zkeep fP gP fA f gA ρ σP HP
  exact ⟨marked_vortex_nested_active_rows_input Q π hπ i d p k t rowErr hrowErr q s a j z (hrow i hi),
    marked_vortex_nested_active_load_input Q π hπ i d c (Dnext i) p k s₀ loadErr (η/4) hloadErr a j (weight i) z (hload i hi)⟩
end Oberwolfach
