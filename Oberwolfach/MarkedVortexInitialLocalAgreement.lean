module

public import Oberwolfach.MarkedVortexInitialInnerCutsTransfer
public import Oberwolfach.MarkedInnerRawAgreementRim

@[expose] public section
/-! Exact protection of the first inner set supplies the local balance agreements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_initial_local_agreement
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [Nonempty V] [DecidableEq U]
    (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (d:ℕ) (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hraw:∀e:Sym2 V,e.toFinset⊆Q.extendedVertices 1→τ (Sum.inl e)=σ (Sum.inl e))
    (hspoke:∀b v u,v∈Q.extendedVertices 1→u∈Q.extendedIndices 1→(H b v u↔H' b v u)):
    let f:=markedVortexVertexEmbedding Q 0
    let g:=markedVortexHubEmbedding Q 0
    let ρ:=markedVortexPermutation Q π hπ 0
    let I:=markedVortexInnerVertices Q 0
    let J:=markedVortexInnerHubs Q 0;
    (∀mark v w,v∈I→w∈I→
      (markedPhysicalRim (G.comap f) ρ (3*d) (fun e=>rawMarkedRestrictPair f g σ (Sum.inl e)) mark v w=1 ↔
       markedPhysicalRim (G.comap f) ρ (3*d) (fun e=>rawMarkedRestrictPair f g τ (Sum.inl e)) mark v w=1)) ∧
    (∀b v u,v∈I→u∈J→(H b (f v) (g u)↔H' b (f v) (g u))):=by
  intro f g ρ I J
  have hcomm:∀v,f (ρ v)=π (f v):=(marked_vortex_permutation_compatibility Q π hπ 0).1
  have hf:∀v,v∈I→f v∈Q.extendedVertices 1:=by
    intro v hv
    change v.val∈Q.extendedVertices 1
    simpa only [I,markedVortexInnerVertices,Finset.mem_filter,Finset.mem_univ,true_and,zero_add] using hv
  have hg:∀u:markedVortexHubType Q 0,u∈J → g u∈Q.extendedIndices 1:=by
    intro u hu
    change u.val∈Q.extendedIndices 1
    simpa only [J,markedVortexInnerHubs,Finset.mem_filter,Finset.mem_univ,true_and,zero_add] using hu
  have hR:=marked_inner_raw_agreement_rims G π d (Q.extendedVertices 1) (hπ 1) σ τ hraw
  refine ⟨?_,?_⟩
  · intro mark v w hv hw
    rw [markedPhysicalRim_restrictPair_eq f g π ρ hcomm G d σ mark v w,
      markedPhysicalRim_restrictPair_eq f g π ρ hcomm G d τ mark v w]
    exact (hR mark (f v) (f w) (hf v hv) (hf w hw)).symm
  · intro b v u hv hu;exact hspoke b (f v) (g u) (hf v hv) (hg u hu)
end Oberwolfach
