module

public import Oberwolfach.OrdinaryCorrectedInnerStarBalance
public import Oberwolfach.OrdinaryDecompositionEdges

@[expose] public section
/-! Exact accounting of the correction star: the corrected inner star is
    temporarily reserved, and the remaining inner star is exactly the
    corresponding star of the correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryResourceTouchesRoots (T:Finset V) (W:Finset U):Sym2 V⊕(V×U)→Prop
  | Sum.inl e => ∃v∈T,v∈e
  | Sum.inr vu => vu.1∈T ∨ vu.2∈W

theorem ordinary_root_star_resources (C:SimpleGraph V) (K:V→U→Prop) (T:Finset V) (W:Finset U):
    ordinaryHostResources (ordinaryRimRootStar C T) (ordinarySpokeRootStar K T W)=
      (ordinaryHostResources C K).filter (ordinaryResourceTouchesRoots T W) :=by
  ext e
  cases e with
  | inl e =>
    induction e using Sym2.ind with
    | _ v w =>
      simp only [Finset.mem_filter,ordinaryHostResources_rim,SimpleGraph.mem_edgeSet]
      change (C.Adj v w ∧ (v∈T ∨ w∈T)) ↔ C.Adj v w ∧ (∃x∈T,x∈s(v,w))
      simp only [Sym2.mem_iff]
      constructor
      · rintro ⟨ha,hv|hw⟩
        · exact ⟨ha,v,hv,Or.inl rfl⟩
        · exact ⟨ha,w,hw,Or.inr rfl⟩
      · rintro ⟨ha,x,hx,hxv|hxw⟩
        · exact ⟨ha,Or.inl (hxv ▸ hx)⟩
        · exact ⟨ha,Or.inr (hxw ▸ hx)⟩
  | inr vu =>
    rcases vu with ⟨v,u⟩
    simp [ordinaryHostResources_spoke,ordinarySpokeRootStar,ordinaryResourceTouchesRoots]

theorem ordinary_corrected_star_exact_remainder
    (Q C D:SimpleGraph V) (H K J:V→U→Prop) (T:Finset V) (W:Finset U)
    (hCQ:C≤Q) (hDC:D≤C) (hKH:∀v u,K v u→H v u) (hJK:∀v u,J v u→K v u):
    let R:=ordinaryRimRootStar (C\D) T;
    let S:=ordinarySpokeRootStar (fun v u=>K v u∧¬J v u) T W;
    let Inner:=ordinaryHostResources C K;
    let Correction:=ordinaryHostResources D J;
    let Touch:=ordinaryResourceTouchesRoots T W;
    ((ordinaryHostResources (Q\R) (fun v u=>H v u∧¬S v u)∩Inner).filter Touch)=
      Correction.filter Touch :=by
  intro R S Inner Correction Touch
  have hIC:Correction⊆Inner:=by
    intro e he
    cases e with
    | inl e => exact (ordinaryHostResources_rim C K e).mpr (SimpleGraph.edgeSet_mono hDC ((ordinaryHostResources_rim D J e).mp he))
    | inr vu => rcases vu with ⟨v,u⟩;exact (ordinaryHostResources_spoke C K v u).mpr (hJK v u ((ordinaryHostResources_spoke D J v u).mp he))
  have hIH:Inner⊆ordinaryHostResources Q H:=by
    intro e he
    cases e with
    | inl e => exact (ordinaryHostResources_rim Q H e).mpr (SimpleGraph.edgeSet_mono hCQ ((ordinaryHostResources_rim C K e).mp he))
    | inr vu => rcases vu with ⟨v,u⟩;exact (ordinaryHostResources_spoke Q H v u).mpr (hKH v u ((ordinaryHostResources_spoke C K v u).mp he))
  have hstar:ordinaryHostResources R S=(Inner\Correction).filter Touch:=by
    rw [ordinary_root_star_resources,ordinaryHostResources_sdiff]
  rw [ordinaryHostResources_sdiff,hstar]
  ext e
  simp only [Finset.mem_filter,Finset.mem_inter,Finset.mem_sdiff]
  have h1:=fun he=>hIC (x:=e) he
  have h2:=fun he=>hIH (x:=e) he
  tauto
end Oberwolfach
