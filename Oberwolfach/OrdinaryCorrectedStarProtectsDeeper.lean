module

public import Oberwolfach.OrdinaryCorrectedInnerStarResources
public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! Reserving the corrected inner star excludes the whole deeper pair from
    the working host when the correction avoids that pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_corrected_star_protects_deeper
    (Q D:SimpleGraph V) (H J:V→U→Prop) (I T:Finset V) (B W:Finset U)
    (hTI:T⊆I) (hWB:W⊆B)
    (hD:∀v∈T,∀w∈T,¬D.Adj v w)
    (hJ:∀v u,J v u→¬(v∈T∧u∈W)):
    let R:=ordinaryRimRootStar ((spanningRestriction Q I)\D) T;
    let S:=ordinarySpokeRootStar (fun v u=>(H v u∧v∈I∧u∈B)∧¬J v u) T W;
    let Qout:=Q\R;let Hout:=fun v u=>H v u∧¬S v u;
    (∀v∈T,∀w∈T,¬Qout.Adj v w) ∧
    (∀v∈T,∀u∈W,¬Hout v u) ∧
    Disjoint (ordinaryHostResources Qout Hout)
      (ordinaryHostResources (spanningRestriction Q T) (fun v u=>H v u∧v∈T∧u∈W)):=by
  intro R S Qout Hout
  have hr:∀v∈T,∀w∈T,¬Qout.Adj v w:=by
    intro v hv w hw he
    have hi:(spanningRestriction Q I).Adj v w:=
      (spanningRestriction_adj Q I v w).mpr ⟨he.1,hTI hv,hTI hw⟩
    have hd:¬D.Adj v w:=hD v hv w hw
    apply he.2
    exact ⟨⟨hi,hd⟩,Or.inl hv⟩
  have hs:∀v∈T,∀u∈W,¬Hout v u:=by
    intro v hv u hu he
    have hj:¬J v u:=fun h=>hJ v u h ⟨hv,hu⟩
    apply he.2
    exact ⟨⟨⟨he.1,hTI hv,hWB hu⟩,hj⟩,Or.inl hv⟩
  refine ⟨hr,hs,?_⟩
  apply Finset.disjoint_left.mpr
  intro e he he'
  cases e with
  | inl e=>
    induction e using Sym2.ind with
    | _ v w=>
      have heq:Qout.Adj v w:=(ordinaryHostResources_rim _ _ _).mp he
      have ht:=(spanningRestriction_adj Q T v w).mp ((ordinaryHostResources_rim _ _ _).mp he')
      exact hr v ht.2.1 w ht.2.2 heq
  | inr vu=>
    rcases vu with ⟨v,u⟩
    have hh:Hout v u:=(ordinaryHostResources_spoke _ _ _ _).mp he
    have ht: H v u∧v∈T∧u∈W:=(ordinaryHostResources_spoke (spanningRestriction Q T) (fun v u=>H v u∧v∈T∧u∈W) v u).mp he'
    exact hs v ht.2.1 u ht.2.2 hh
end Oberwolfach
