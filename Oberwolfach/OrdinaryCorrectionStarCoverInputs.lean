module

public import Oberwolfach.OrdinaryCorrectedInnerStarResources
public import Oberwolfach.OrdinaryPhysicalResourceIncidence
public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! The actual correction-star resource set supplies the coverage and
    sparsity inputs to the finite prescribed-edge wheel constructor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_correction_star_cover_inputs
    (Q D:SimpleGraph V) (H J:V→U→Prop) (I T:Finset V) (B W:Finset U) (D₀:ℕ)
    (hTI:T⊆I) (hWB:W⊆B)
    (hDI:D≤spanningRestriction Q I)
    (hJ:∀v u,J v u→H v u∧v∈I∧u∈B)
    (hdegree:∀x:V⊕U,(ordinaryPhysicalGraph D J).degree x≤D₀):
    let C:=spanningRestriction Q I;
    let K:=fun v u=>H v u∧v∈I∧u∈B;
    let R:=ordinaryRimRootStar (C\D) T;
    let S:=ordinarySpokeRootStar (fun v u=>K v u∧¬J v u) T W;
    let Qout:=Q\R;
    let Hout:=fun v u=>H v u∧¬S v u;
    let E:=(ordinaryHostResources D J).filter (ordinaryResourceTouchesRoots T W);
    E⊆ordinaryHostResources (spanningRestriction Qout I) (fun v u=>Hout v u∧v∈I∧u∈B) ∧
    (∀v∈T,∀w∈I,Qout.Adj v w→Sum.inl s(v,w)∈E) ∧
    (∀v∈T,∀u∈B,Hout v u→Sum.inr (v,u)∈E) ∧
    (∀u∈W,∀v∈I,Hout v u→Sum.inr (v,u)∈E) ∧
    (∀x,(E.filter (ordinaryResourceIncident x)).card≤D₀) ∧
    E.card≤Fintype.card (V⊕U)*D₀ :=by
  intro C K R S Qout Hout E
  have hCQ:C≤Q:=by intro v w h;exact (spanningRestriction_adj Q I v w).mp h |>.1
  have hKH:∀v u,K v u→H v u:=by intro v u h;exact h.1
  have heq:=ordinary_corrected_star_exact_remainder Q C D H K J T W hCQ hDI hKH hJ
  change ((ordinaryHostResources Qout Hout∩ordinaryHostResources C K).filter
    (ordinaryResourceTouchesRoots T W))=E at heq
  have hinner:ordinaryHostResources Qout Hout∩ordinaryHostResources C K=
      ordinaryHostResources (spanningRestriction Qout I) (fun v u=>Hout v u∧v∈I∧u∈B):=by
    ext e
    cases e with
    | inl e =>
      induction e using Sym2.ind with
      | _ v w =>
        simp only [Finset.mem_inter,ordinaryHostResources_rim,SimpleGraph.mem_edgeSet,C,spanningRestriction_adj]
        change (Qout.Adj v w ∧ (Q.Adj v w ∧ v∈I ∧ w∈I)) ↔ Qout.Adj v w ∧ v∈I ∧ w∈I
        have hh:Qout≤Q:=sdiff_le
        constructor
        · tauto
        · intro h;exact ⟨h.1,hh h.1,h.2⟩
    | inr vu =>
      rcases vu with ⟨v,u⟩
      simp only [Finset.mem_inter,ordinaryHostResources_spoke,K]
      change (Hout v u ∧ (H v u ∧ v∈I ∧ u∈B)) ↔ Hout v u ∧ v∈I ∧ u∈B
      constructor
      · tauto
      · intro h;exact ⟨h.1,h.1.1,h.2⟩
  rw [hinner] at heq
  have hE:E⊆ordinaryHostResources (spanningRestriction Qout I) (fun v u=>Hout v u∧v∈I∧u∈B):=by
    rw [←heq];exact Finset.filter_subset _ _
  have hsparse:=ordinary_resources_from_physical_degree D J E D₀ (Finset.filter_subset _ _) hdegree
  refine ⟨hE,?_,?_,?_,hsparse.1,hsparse.2⟩
  · intro v hv w hw hadj
    rw [←heq]
    apply Finset.mem_filter.mpr
    exact ⟨(ordinaryHostResources_rim _ _ _).mpr ((spanningRestriction_adj Qout I v w).mpr ⟨hadj,hTI hv,hw⟩),⟨v,hv,by simp⟩⟩
  · intro v hv u hu hh
    rw [←heq]
    exact Finset.mem_filter.mpr ⟨(ordinaryHostResources_spoke _ _ v u).mpr ⟨hh,hTI hv,hu⟩,Or.inl hv⟩
  · intro u hu v hv hh
    rw [←heq]
    exact Finset.mem_filter.mpr ⟨(ordinaryHostResources_spoke _ _ v u).mpr ⟨hh,hv,hWB hu⟩,Or.inr hu⟩
end Oberwolfach
