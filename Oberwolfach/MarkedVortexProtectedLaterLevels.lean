module

public import Oberwolfach.MarkedVortexRestrictionChain
public import Oberwolfach.MarkedProtectedPairFromChangeGraphs

@[expose] public section
/-! Changes avoiding the first inner pair leave every later vortex level's
typed rim and spoke predicates unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ}

theorem marked_vortex_protected_later_levels
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hR:∀ a,¬(rawMarkedPairRims G π d σ a↔rawMarkedPairRims G π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hS:∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀ x∈Q.extendedVertices 1,∀ y∈Q.extendedVertices 1,¬FR.Adj x y)
    (hFS:∀ x∈Q.extendedVertices 1,∀ u∈Q.extendedIndices 1,¬FS.Adj (Sum.inl x) (Sum.inr u)):
    ∀ i,1 ≤ i →
    let W:=markedVortexVertexType Q i
    let Z:=markedVortexHubType Q i
    let f:=markedVortexVertexEmbedding Q i
    let g:=markedVortexHubEmbedding Q i
    let ρ:=markedVortexPermutation Q π hπ i;
    (∀ a:(W×W)⊕(W×W),
      rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g σ) a ↔
      rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g τ) a) ∧
    (∀ b (v:W) (u:Z),H b (f v) (g u)↔H' b (f v) (g u)) := by
  obtain ⟨hr,hs⟩:=marked_protected_pair_from_change_graphs G π d σ τ H H'
    (Q.extendedVertices 1) (Q.extendedIndices 1) FR FS (fun x hx=>(hπ 1 x).mpr hx) hR hS hFR hFS
  intro i hi W Z f g ρ
  have hv:∀ x:W,f x∈Q.extendedVertices 1:=fun x=>Q.extendedVertices_subset hi x.property
  have hu:∀ u:Z,g u∈Q.extendedIndices 1:=fun u=>Q.extendedIndices_subset hi u.property
  constructor
  · intro a
    rw [rawMarkedRestrictPair_rims f g π ρ (marked_vortex_permutation_compatibility Q π hπ i).1 G d σ a,
      rawMarkedRestrictPair_rims f g π ρ (marked_vortex_permutation_compatibility Q π hπ i).1 G d τ a]
    cases a with
    | inl a=>
      rcases a with ⟨x,y⟩
      exact hr false (f x) (f y) (hv x) (hv y)
    | inr a=>
      rcases a with ⟨x,y⟩
      exact hr true (f x) (f y) (hv x) (hv y)
  · intro b v u
    exact hs b (f v) (g u) (hv v) (hu u)
end Oberwolfach
