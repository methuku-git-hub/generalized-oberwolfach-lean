module

public import Oberwolfach.OrdinaryTriangleSelectedFactors
public import Oberwolfach.SelectionCandidateBudget

@[expose] public section
/-! Select actual triangle endpoint and hub-cycle factors from two families
using one bounded-degree physical-edge selection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_factor_selection_from_families (p:ℝ) (hp:0<p):
    ∃n₀:ℕ,2≤n₀ ∧ ∀(V U I J:Type) [Fintype V] [Fintype U] [Fintype I] [Fintype J]
      [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J],n₀≤Fintype.card (V⊕U)→
    ∀(Q F:SimpleGraph V) (H:V→U→Prop) (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
      (hAB:∀i,Disjoint ((A i).image Sum.inl) ((B i).image Sum.inr))
      (N D:ℕ) (G:SimpleGraph (V⊕U)) (S:Fin N→Finset (V⊕U))
      (family:Fin N→Set (SimpleGraph (V⊕U))) (x:I↪Fin N) (u:J↪Fin N) (hsep:∀i j,x i≠u j),
    (∀i W,W∈family (x i)→∃M:Finset (EndpointTriangle (ordinaryPhysicalGraph Q H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) ((A i).image Sum.inl) ((B i).image Sum.inr)),
      (∀C∈M,∀C'∈M,C≠C'→Disjoint C.val C'.val) ∧
      M.biUnion endpointTriangleVertices=(A i).image Sum.inl∪(B i).image Sum.inr ∧
      W=endpointFactorGraph (hAB i) M) →
    (∀j W,W∈family (u j)→∃M:Finset (LocalOrdinaryCycle Q F (T j) 3),
      (∀C∈M,∀C'∈M,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
      M.biUnion localOrdinaryVertices=Y j ∧
      W=(localOrdinaryFactorGraph M).map (Function.Embedding.inl:V↪V⊕U)) →
    (∀i j,i≠j→((S i∩S j).card:ℝ)≤p^2*Fintype.card (V⊕U)) →
    (∀v,((Finset.univ.filter (fun i=>v∈S i)).card:ℝ)≤p*Fintype.card (V⊕U)) →
    (∀i,∀K:SimpleGraph (V⊕U),K≤spanningRestriction G (S i)→
      (∀v,(K.degree v:ℝ)≤D*(p*Real.sqrt p*Fintype.card (V⊕U))+
        D*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card (V⊕U))):ℝ))→
      ∃W:SimpleGraph (V⊕U),W∈family i ∧ W≤spanningRestriction G (S i) ∧
        (∀v,W.degree v≤D) ∧ Disjoint W K) →
    Nonempty (OrdinaryTriangleSelectedFactors Q F H A B T Y hAB (D*(p*Fintype.card (V⊕U)))):=by
  obtain ⟨n₀,hn₀,hselect⟩:=bounded_degree_selection_from_single_copy p hp
  refine ⟨n₀,hn₀,?_⟩
  intro V U I J _ _ _ _ _ _ _ _ hn Q F H A B T Y hAB N D G S family x u hsep hrow hhub hinter hmem hsingle
  obtain ⟨W,hW,hdis,hdeg⟩:=hselect (V⊕U) hn N D G S family hinter hmem hsingle
  have hr:∀i,∃M:Finset (EndpointTriangle (ordinaryPhysicalGraph Q H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) ((A i).image Sum.inl) ((B i).image Sum.inr)),
      (∀C∈M,∀C'∈M,C≠C'→Disjoint C.val C'.val) ∧
      M.biUnion endpointTriangleVertices=(A i).image Sum.inl∪(B i).image Sum.inr ∧
      W (x i)=endpointFactorGraph (hAB i) M:=fun i=>hrow i _ (hW (x i)).1
  have hh:∀j,∃M:Finset (LocalOrdinaryCycle Q F (T j) 3),
      (∀C∈M,∀C'∈M,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
      M.biUnion localOrdinaryVertices=Y j ∧
      W (u j)=(localOrdinaryFactorGraph M).map (Function.Embedding.inl:V↪V⊕U):=fun j=>hhub j _ (hW (u j)).1
  let R:=fun i=>Classical.choose (hr i)
  let M:=fun j=>Classical.choose (hh j)
  have hR (i:I):=(Classical.choose_spec (hr i))
  have hM (j:J):=(Classical.choose_spec (hh j))
  refine ⟨⟨M,fun j=>(hM j).1,fun j=>(hM j).2.1,?_,R,fun i=>(hR i).1,fun i=>(hR i).2.1,?_,?_,?_⟩⟩
  · intro i j hij
    have hd:=hdis (u i) (u j) (fun he=>hij (u.injective he))
    rw [(hM i).2.2,(hM j).2.2,graph_map_inl_physical,graph_map_inl_physical] at hd
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    exact (disjoint_iff_inf_le.mp hd) (v:=Sum.inl a) (w:=Sum.inl b) ⟨hab.1,hab.2⟩
  · intro i j hij
    have hd:=hdis (x i) (x j) (fun he=>hij (x.injective he))
    rw [(hR i).2.2,(hR j).2.2] at hd
    exact hd
  · intro j i
    have hd:=hdis (u j) (x i) (Ne.symm (hsep i j))
    rw [(hM j).2.2,(hR i).2.2] at hd
    exact hd
  · intro v
    have hsub:((⨆j,(localOrdinaryFactorGraph (M j)).map (Function.Embedding.inl:V↪V⊕U))⊔
        (⨆i,endpointFactorGraph (hAB i) (R i)))≤⨆k,W k:=by
      apply sup_le
      · apply iSup_le;intro j;rw [←(hM j).2.2];exact le_iSup W (u j)
      · apply iSup_le;intro i;rw [←(hR i).2.2];exact le_iSup W (x i)
    have hd:(((⨆j,(localOrdinaryFactorGraph (M j)).map (Function.Embedding.inl:V↪V⊕U))⊔
        (⨆i,endpointFactorGraph (hAB i) (R i))).degree v:ℝ)≤((⨆k,W k).degree v:ℝ):=by
      exact_mod_cast (SimpleGraph.degree_le_of_le hsub (v:=v))
    exact hd.trans (hdeg v)
end Oberwolfach
