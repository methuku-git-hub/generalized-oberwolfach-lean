module

public import Oberwolfach.EndpointTypedIndexPhysicalPredicate
public import Oberwolfach.EndpointIndexResources
public import Oberwolfach.PhysicalWheelFamilies

@[expose] public section
/-! The original two-domain unordered-edge pattern equals the actual
physical hub-root potential with the same fixed parent weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem endpoint_typed_index_physical_identity (P R F:SimpleGraph V) (H:V→U→Prop)
    (A:Finset V) (x:V) (u:U) (weight:Sym2 (V⊕U)→ℝ) (D:ℝ):
    (∑ e:↥(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,
      (weight (Sym2.map Sum.inl e.val)/D)*
        patternValue (endpointIndexResources x u e.val) (fun _=>true) (ordinaryResourceState R H))=
    endpointIndexPotential (ordinaryPhysicalGraph P (fun _ _=>False))
      (ordinaryPhysicalGraph R (fun _ _=>False)) (ordinaryPhysicalGraph ⊥ H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (A.image Sum.inl)
      (Sum.inl x) (Sum.inr u) weight D:=by
  let E:=endpointEligibleGraph P F (A∩P.neighborFinset x) x
  let f:V↪V⊕U:=Function.Embedding.inl
  let Ephys:SimpleGraph (V⊕U):=ordinaryPhysicalGraph E (fun _ _=>False)
  let pred:=EndpointIndexPotentialPredicate (ordinaryPhysicalGraph P (fun _ _=>False))
      (ordinaryPhysicalGraph R (fun _ _=>False)) (ordinaryPhysicalGraph ⊥ H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (A.image Sum.inl) (Sum.inl x) (Sum.inr u)
  have hsupport (e:Sym2 (V⊕U)) (h:pred e):e∈Ephys.edgeFinset:=by
    apply SimpleGraph.mem_edgeFinset.mpr
    change e∈(ordinaryPhysicalGraph E (fun _ _=>False)).edgeSet
    rw [←ordinary_endpoint_eligible_graph]
    exact h.1
  have hsum:(∑e∈Ephys.edgeFinset,if pred e then weight e/D else 0)=
      ∑e:Sym2 (V⊕U),if pred e then weight e/D else 0:=by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e he hnot
    have hn:¬pred e:=fun hp=>hnot (hsupport e hp)
    simp [hn]
  have hcoe:(∑ e:↥E.edgeFinset,(weight (Sym2.map Sum.inl e.val)/D)*
      patternValue (endpointIndexResources x u e.val) (fun _=>true) (ordinaryResourceState R H))=
      ∑e∈E.edgeFinset,(weight (Sym2.map Sum.inl e)/D)*
        patternValue (endpointIndexResources x u e) (fun _=>true) (ordinaryResourceState R H):=by
    exact Finset.sum_coe_sort E.edgeFinset (fun e=>(weight (Sym2.map Sum.inl e)/D)*
      patternValue (endpointIndexResources x u e) (fun _=>true) (ordinaryResourceState R H))
  rw [hcoe]
  calc
    _ = ∑e∈E.edgeFinset,if pred (Sym2.map Sum.inl e) then weight (Sym2.map Sum.inl e)/D else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [endpointIndexResources_value]
      have hel:e∈E.edgeSet:=SimpleGraph.mem_edgeFinset.mp he
      have hp:=endpoint_typed_index_physical_predicate P R F H A x u e
      change pred (Sym2.map Sum.inl e) ↔ _ at hp
      rw [hp]
      split_ifs <;> simp_all [E]
    _ = ∑e∈Ephys.edgeFinset,if pred e then weight e/D else 0 := by
      have htransport:(∑e∈(E.map f).edgeFinset,if pred e then weight e/D else 0)=
          ∑e∈E.edgeFinset,if pred (Sym2.map Sum.inl e) then weight (Sym2.map Sum.inl e)/D else 0:=by
        rw [SimpleGraph.edgeFinset_map,Finset.sum_map]
        rfl
      have hmap:Ephys=E.map f:=(graph_map_inl_physical E).symm
      have hedge:Ephys.edgeFinset=(E.map f).edgeFinset:=by
        apply Finset.ext
        intro e
        simp only [SimpleGraph.mem_edgeFinset]
        rw [hmap]
      have hphys:(∑e∈Ephys.edgeFinset,if pred e then weight e/D else 0)=
          ∑e∈(E.map f).edgeFinset,if pred e then weight e/D else 0:=by
        apply Finset.sum_congr hedge
        intro e he
        rfl
      exact htransport.symm.trans hphys.symm
    _ = _ := hsum
end Oberwolfach
