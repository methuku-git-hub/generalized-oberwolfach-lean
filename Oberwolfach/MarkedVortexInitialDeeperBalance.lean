module

public import Oberwolfach.MarkedLevelFiniteBalanceBound
public import Oberwolfach.MarkedRestrictedSampleBalanceValues
public import Oberwolfach.MarkedVortexInitialExtendedEquivs

@[expose] public section
/-! Transfer the initial level's deeper-domain balance to the original host,
including every ambient vertex and hub root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_vortex_initial_deeper_balance_on_host
    (P:SimpleGraph V) (π:Equiv.Perm V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d c:ℕ) (err:ℝ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hbal:MarkedLevelFiniteBalanceBound (P.comap (markedVortexVertexEmbedding Q 0))
      (markedVortexPermutation Q π hpres 0) d c (markedVortexDeeperVertices Q 0) (markedVortexDeeperHubs Q 0) err
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σ)
      (fun b x u=>H b (markedVortexVertexEmbedding Q 0 x) (markedVortexHubEmbedding Q 0 u))):
    MarkedLevelFiniteBalanceBound P π d c (Q.extendedVertices 2) (Q.extendedIndices 2) err σ H := by
  let f:=markedVortexVertexEmbedding Q 0
  let g:=markedVortexHubEmbedding Q 0
  let eV:=markedVortexInitialExtendedVertexEquiv Q
  let eU:=markedVortexInitialExtendedHubEquiv Q
  have hf:Finset.univ.image f=Finset.univ:=by
    apply Finset.eq_univ_of_forall
    intro v
    exact Finset.mem_image.mpr ⟨eV.symm v,Finset.mem_univ _,by simp [f,eV,markedVortexInitialExtendedVertexEquiv,markedVortexVertexEmbedding]⟩
  have hg:Finset.univ.image g=Finset.univ:=by
    apply Finset.eq_univ_of_forall
    intro u
    exact Finset.mem_image.mpr ⟨eU.symm u,Finset.mem_univ _,by simp [g,eU,markedVortexInitialExtendedHubEquiv,markedVortexHubEmbedding]⟩
  have hX:∀ x,f x∈Q.extendedVertices 2↔x∈markedVortexDeeperVertices Q 0:=by
    intro x
    simp [f,markedVortexDeeperVertices,markedVortexVertexEmbedding]
  have hZ:∀ u,g u∈Q.extendedIndices 2↔u∈markedVortexDeeperHubs Q 0:=by
    intro u
    simp [g,markedVortexDeeperHubs,markedVortexHubEmbedding]
  have hA:∀ j,∀ a:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) j,
      a.val.1∈Finset.univ.image f∧a.val.2∈Finset.univ.image f:=by
    intro j a; rw [hf];simp
  have hS:∀ v u,H false v u∨H true v u→v∈Finset.univ.image f∧u∈Finset.univ.image g:=by
    intro v u h;rw [hf,hg];simp
  intro z j
  let z':=Sum.map eV.symm eU.symm z
  have heq:Sum.map f g z'=z:=by
    cases z with
    | inl v=>simp [z',f,eV,markedVortexInitialExtendedVertexEquiv,markedVortexVertexEmbedding]
    | inr u=>simp [z',g,eU,markedVortexInitialExtendedHubEquiv,markedVortexHubEmbedding]
  have hh:=hbal z' j
  have hb:=(marked_restricted_sample_balance_values f g π (markedVortexPermutation Q π hpres 0)
    (marked_vortex_initial_extended_equiv_commutes Q π hpres) P d c σ H
    (markedVortexDeeperVertices Q 0) (markedVortexDeeperHubs Q 0) (Q.extendedVertices 2) (Q.extendedIndices 2)
    hX hZ hA hS z' j).2
  rw [hb,heq] at hh
  exact hh
end Oberwolfach
