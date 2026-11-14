module

public import Oberwolfach.OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent
public import Oberwolfach.OrdinaryVortexTriangleInnerSizeAndIndices

@[expose] public section
/-! At level zero the same all-level hub event supplies weights on the
actual corrected host at its selected edit budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_initial_inner_hub_from_uniform
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
    (P G:SimpleGraph V) (Hs:V→U→Prop) (D mv:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (pR pH density εR εH eParent hParent b B η cap:ℝ):
    let F:=permutationConflictGraph π (3*d);
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let I:=markedVortexInnerVertices Q 0;let Bset:=markedVortexInnerHubs Q 0;
    let ρi:=markedVortexPermutation Q π hπ 0;let Ploc:=P.comap f;let Floc:=F.comap f;
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u);let raw:=ordinaryRawRestrictPair f g σ;
    G≤P→
    (∀Lold:ℝ,0≤Lold→Lold≤cap*I.card→
      OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent 2 Ploc Floc I Bset ρi d pR pH density
        (εR*I.card) (εH*Bset.card) Lold (eParent*ε) (hParent*ε) b B η (fun u=>s (g u)) j raw)→
    ∀Ledit:ℝ,0≤Ledit→Ledit≤cap*I.card→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I Bset pR pH density
      (εR*I.card) (εH*Bset.card) Ledit (eParent*ε) (hParent*ε) (fun u=>s (g u)) j raw→
    Nonempty (OrdinaryMixedHubWeightsInnerScale 2 b B η Gloc Floc Hloc I Bset):=by
  intro F f g I Bset ρi Ploc Floc Gloc Hloc raw hG hfamily Ledit hL hcap profile
  have hsub:Gloc≤Ploc:=by intro v w hvw;exact hG hvw
  have hw:=hfamily Ledit hL hcap Gloc Hloc
    (by convert profile using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _) hsub
  convert hw using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
