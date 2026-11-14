module

public import Oberwolfach.OrdinaryHubWheelPacking

@[expose] public section

/-! The rim-degree loss in successive hub covers is controlled by actual
row incidences, not the total number of hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

theorem ordinary_hub_packing_rim_support (M:Finset (OrdinaryWheel Q F H r))
    (T:Finset V) (u:U)
    (hunion:M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      T.image (fun v=>Sum.inr (v,u))) (v w:V) (hvw:(ordinaryWheelRimGraph M).Adj v w) : v∈T := by
  obtain ⟨W,hW,hWvw⟩:=(ordinaryWheelRimGraph_edges M s(v,w)).mp hvw
  have hvW:v∈(ordinaryWheelRim W).support:=hWvw.mem_support_left
  have hs:Sum.inr (v,ordinaryWheelHub W)∈M.biUnion ordinaryWheelResources:=by
    apply Finset.mem_biUnion.mpr
    refine ⟨W,hW,?_⟩
    rw [ordinaryWheelResources_spoke]
    exact ⟨rfl,hvW⟩
  rw [hunion] at hs
  rcases Finset.mem_union.mp hs with h|h
  · obtain ⟨e,_,he⟩:=Finset.mem_image.mp h
    cases he
  · obtain ⟨a,ha,he⟩:=Finset.mem_image.mp h
    have hav:a=v:=(Prod.mk.inj (Sum.inr.inj he)).1
    exact hav ▸ ha

theorem graph_family_degree_by_support {I:Type} [Fintype I]
    (G:I→SimpleGraph V) (T:I→Finset V) (D:ℕ) (v:V)
    (hdegree:∀ i,(G i).degree v≤D)
    (hsupport:∀ i,∀ w,(G i).Adj v w→v∈T i) :
    (⨆ i,G i).degree v≤D*(Finset.univ.filter (fun i=>v∈T i)).card := by
  have hh:=graph_iSup_local_degree_bound G Finset.univ v D hdegree
  simp only [Finset.inter_univ,SimpleGraph.card_neighborFinset_eq_degree] at hh
  apply hh.trans
  apply Nat.mul_le_mul_left D
  apply Finset.card_le_card
  intro i hi
  obtain ⟨w,_,hw⟩:=(Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsupport i w hw⟩

end Oberwolfach
