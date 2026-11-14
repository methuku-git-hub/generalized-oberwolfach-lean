module

public import Oberwolfach.MarkedSelectedHubWheels
public import Oberwolfach.MarkedPackingStageCombination

@[expose] public section

/-! Assemble the selected factors at distinct outside hubs. The resulting
packing has exactly the selected spoke incidences and the selected physical
rim graph, so neither an auxiliary edge nor a hub occurrence is duplicated. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T J:Type} [Fintype V] [Fintype U] [Fintype J]
    [DecidableEq V] [DecidableEq U] [DecidableEq J]
    {tail head:E→V} {ktail khead:T→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_selected_hub_packing (u:J↪U) (Y:J→Finset V)
    (hm:1≤m) (hb:1≤b) (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hsep:∀ j v z,H₀ v (u j)→HK z (u j)→v≠π z)
    (P:∀ j,MarkedHubFactorOn tail head ktail khead m π b H₀ HK (u j) (Y j))
    (hcross:∀ i j,i≠j→Disjoint (P i).rim (P j).rim):
    ∃ M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK),
      (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      markedPackingRimGraph M=(⨆ j,(P j).rim)∧
      (∀ x z,markedPackingSpokes M x z↔∃ j,u j=z∧x∈Y j)∧
      (∀ W∈M,∃ j,W.2.val=u j∧markedWheelRows W⊆Y j) := by
  have hf (j:J):=marked_selected_hub_factor_to_wheels (u j) hm hb hp (hsep j)
    (Y j) (P j).cycles (P j).disjoint (P j).covers
  choose N hN hres hdeg hhub hpairs hrim using hf
  have hgraph (j:J):markedPackingRimGraph (N j)=(P j).rim:=by
    unfold markedPackingRimGraph MarkedHubFactorOn.rim
    rw [hrim j]
  have hdis (i j:J) (hij:i≠j):
      Disjoint ((N i).biUnion markedWheelPhysicalResources) ((N j).biUnion markedWheelPhysicalResources):=by
    apply marked_packing_distinct_hubs_disjoint (N i) (N j) (u i) (u j)
      (fun he=>hij (u.injective he)) (hhub i) (hhub j) (hpairs i)
    rw [hgraph i,hgraph j]
    exact hcross i j hij
  have hsp (j:J) (x:V) (z:U):markedPackingSpokes (N j) x z↔u j=z∧x∈Y j:=by
    have he:markedPackingSpokes (N j) x z↔Sum.inr (x,z)∈(N j).biUnion markedWheelPhysicalResources:=by
      simp only [markedPackingSpokes,Finset.mem_biUnion,markedWheelPhysicalResources_spoke,markedWheelRows]
    rw [he,hres j]
    simp only [Finset.mem_union,Finset.mem_image,Sum.inl_ne_inr,and_false,exists_false,false_or,
      Sum.inr.injEq,Prod.mk.injEq]
    aesop
  let M:=Finset.univ.biUnion N
  refine ⟨M,?_,?_,?_,?_⟩
  · intro W hW Z hZ hne
    obtain ⟨i,_,hWi⟩:=Finset.mem_biUnion.mp hW
    obtain ⟨j,_,hZj⟩:=Finset.mem_biUnion.mp hZ
    by_cases hij:i=j
    · subst j;exact hN i W hWi Z hZj hne
    · exact (hdis i j hij).mono (resource_subset_union _ _ W hWi) (resource_subset_union _ _ Z hZj)
  · ext x y
    simp only [M,markedPackingRimGraph,markedPackingRims,physicalEdgeGraph,SimpleGraph.iSup_adj,
      Finset.mem_biUnion,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨hne,W,⟨j,hW⟩,he⟩
      have hg:(markedPackingRimGraph (N j)).Adj x y:=⟨hne,Finset.mem_biUnion.mpr ⟨W,hW,he⟩⟩
      rw [hgraph j] at hg
      exact ⟨j,hg⟩
    · rintro ⟨j,hj⟩
      rw [←hgraph j] at hj
      obtain ⟨hne,hj⟩:=hj
      obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp hj
      exact ⟨hne,W,⟨j,hW⟩,he⟩
  · intro x z
    change (∃ W∈M,W.2.val=z∧x∈markedWheelRows W)↔_
    constructor
    · rintro ⟨W,hW,hw⟩
      obtain ⟨j,_,hW⟩:=Finset.mem_biUnion.mp hW
      exact ⟨j,(hsp j x z).mp ⟨W,hW,hw⟩⟩
    · rintro ⟨j,hj⟩
      obtain ⟨W,hW,hw⟩:=(hsp j x z).mpr hj
      exact ⟨W,Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hW⟩,hw⟩
  · intro W hW
    obtain ⟨j,_,hW⟩:=Finset.mem_biUnion.mp hW
    refine ⟨j,hhub j W hW,?_⟩
    intro x hx
    exact ((hsp j x (u j)).mp ⟨W,hW,hhub j W hW,hx⟩).2

end Oberwolfach
