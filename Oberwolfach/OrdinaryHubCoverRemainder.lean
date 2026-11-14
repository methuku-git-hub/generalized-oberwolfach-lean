module

public import Oberwolfach.OrdinaryHubWheelPacking
public import Oberwolfach.OrdinaryWheelRemainders

@[expose] public section

/-! Identify the exact spoke graph covered by the successive hub factors.
If each factor uses the entire original neighbourhood of its hub, deletion
removes all and only those hub columns; wheel divisibility is preserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F : SimpleGraph V} {H : V→U→Prop} {r n : ℕ}

theorem ordinaryHubResources (R : SimpleGraph V) (u : Fin n→U) (T : Fin n→Finset V) :
    ordinaryHostResources R (fun v w=>∃ i,u i=w ∧ v∈T i)=
      R.edgeFinset.image Sum.inl ∪ Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i))) := by
  ext e
  cases e with
  | inl e =>
    simp only [ordinaryHostResources_rim,Finset.mem_union,Finset.mem_image,Sum.inl.injEq,
      Sum.inr_ne_inl,and_false,exists_false,Finset.mem_biUnion,Finset.mem_univ,true_and,or_false,
      SimpleGraph.mem_edgeFinset,exists_eq_right]
  | inr vu =>
    rcases vu with ⟨v,w⟩
    simp only [ordinaryHostResources_spoke,Finset.mem_union,Finset.mem_image,Sum.inl_ne_inr,
      and_false,exists_false,false_or,Finset.mem_biUnion,Finset.mem_univ,true_and,
      Sum.inr.injEq,Prod.mk.injEq,exists_eq_right]
    constructor
    · rintro ⟨i,hi,hv⟩;exact ⟨i,v,hv,rfl,hi⟩
    · rintro ⟨i,z,hz,hzv,hi⟩;subst z;exact ⟨i,hi,hz⟩

theorem ordinary_hub_packing_decomposition (u : Fin n→U) (T : Fin n→Finset V)
    (M : Finset (OrdinaryWheel Q F H r))
    (hM : ∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z))
    (hunion : M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i)))) :
    HasOrdinaryWheelDecomposition (ordinaryWheelRimGraph M) (fun v w=>∃ i,u i=w ∧ v∈T i) r := by
  apply ordinary_packing_exact_decomposition M hM
  rw [ordinaryHubResources]
  exact hunion

theorem ordinary_hub_cover_remainder (u : Fin n→U)
    (T : Fin n→Finset V) (hT : ∀ i v,v∈T i ↔ H v (u i))
    (M : Finset (OrdinaryWheel Q F H r))
    (hM : ∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z))
    (hunion : M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i))))
    (hQ : ∀ v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hU : ∀ w,r∣(Finset.univ.filter (fun v=>H v w)).card) :
    let H' : V→U→Prop:=fun v w=>H v w ∧ w∉Finset.univ.image u
    ordinaryHostResources (Q\ordinaryWheelRimGraph M) H'=
      ordinaryHostResources Q H\M.biUnion ordinaryWheelResources ∧
    (∀ v,(Q\ordinaryWheelRimGraph M).degree v=2*(Finset.univ.filter (H' v)).card) ∧
    (∀ w,r∣(Finset.univ.filter (fun v=>H' v w)).card) := by
  dsimp only
  let K : V→U→Prop:=fun v w=>∃ i,u i=w ∧ v∈T i
  have hK (v : V) (w : U) : K v w ↔ H v w ∧ w∈Finset.univ.image u := by
    constructor
    · rintro ⟨i,hi,hv⟩
      exact ⟨hi ▸ (hT i v).mp hv,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩⟩
    · rintro ⟨hv,hw⟩
      obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hw
      exact ⟨i,hi,(hT i v).mpr (hi.symm ▸ hv)⟩
  have hrest : (fun v w=>H v w ∧ ¬K v w)=(fun v w=>H v w ∧ w∉Finset.univ.image u) := by
    funext v w;apply propext;rw [hK];tauto
  have hcover : M.biUnion ordinaryWheelResources=ordinaryHostResources (ordinaryWheelRimGraph M) K := by
    rw [ordinaryHubResources]
    exact hunion
  have hbal:=ordinary_decomposition_remainder_balance Q (ordinaryWheelRimGraph M) H K r
    (ordinaryWheelRimGraph_subhost M) (fun v w h=>(hK v w).mp h |>.1) hQ hU
    (ordinary_hub_packing_decomposition u T M hM hunion)
  have hrestpt (v : V) (w : U) : (H v w ∧ ¬K v w)=(H v w ∧ w∉Finset.univ.image u) :=
    congrFun (congrFun hrest v) w
  simp_rw [hrestpt] at hbal
  refine ⟨?_,hbal⟩
  rw [hcover,←ordinaryHostResources_sdiff,hrest]

end Oberwolfach
