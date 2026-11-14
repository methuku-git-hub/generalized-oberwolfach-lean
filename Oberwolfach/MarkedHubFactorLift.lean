module

public import Oberwolfach.MarkedPackingRimGraphs
public import Oberwolfach.MarkedFactorResourceDecomposition

@[expose] public section

/-! Lift a factor chosen after a physical rim deletion to an actual
packing of wheels in the original host, with exact spoke coverage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

def hubMarkedCycleToLarger (PE:E→Prop) (PK:K→Prop) (u:U)
    (C:HubMarkedCycle (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀ Hₖ u):
    HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u:=
  ⟨C.val,(markedCycleToLarger PE PK (hubCycleAsMarked u C)).property,C.property.2⟩

theorem hubMarkedCycleWheel_injective (u:U):
    Function.Injective (hubCycleWheel (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ) u):=by
  intro C Z he
  exact Subtype.ext (congrArg (fun W=>W.1.val) he)

theorem marked_hub_factor_to_wheels (u:U) (hm:1≤m) (hb:1≤b)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hsep:∀ v z,H₀ v u→Hₖ z u→v≠π z)
    (M:Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u))
    (hM:∀ C∈M,∀ Z∈M,C≠Z→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u Z))
    (hcov:M.biUnion (hubMarkedCycleVertices u)=Finset.univ.filter (fun v=>H₀ v u∨Hₖ v u)):
    ∃ N:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ),
      (∀ W∈N,∀ Z∈N,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      N.biUnion markedWheelPhysicalResources=(markedPackingRims N).image Sum.inl∪
        (Finset.univ.filter (fun v=>H₀ v u∨Hₖ v u)).image (fun v=>Sum.inr (v,u))∧
      (∀ v,(markedPackingRimGraph N).degree v≤2)∧
      (∀ W∈N,W.2.val=u)∧(∀ e∈markedPackingRims N,e.card=2)∧
      markedPackingRims N=M.biUnion (hubCyclePhysicalEdges u):=by
  let N:=M.image (hubCycleWheel u)
  have hr:markedPackingRims N=M.biUnion (hubCyclePhysicalEdges u):=by
    rw [markedPackingRims,Finset.image_biUnion]
    rfl
  refine ⟨N,?_,?_,?_,?_,?_,hr⟩
  · intro W hW Z hZ hne
    obtain ⟨C,hC,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨D,hD,rfl⟩:=Finset.mem_image.mp hZ
    have hCD:C≠D:=fun h=>hne (congrArg (hubCycleWheel u) h)
    apply Finset.disjoint_left.mpr
    intro e he hf
    cases e with
    | inl e=>
      rw [markedWheelPhysicalResources_rim] at he hf
      exact Finset.disjoint_left.mp (marked_factor_physical_edges_disjoint u hp M hM C hC D hD hCD) he hf
    | inr e=>
      rw [markedWheelPhysicalResources_spoke] at he hf
      exact Finset.disjoint_left.mp (hM C hC D hD hCD) he.2 hf.2
  · rw [←hcov]
    ext e
    cases e with
    | inl e=>
      simp only [Finset.mem_biUnion,markedWheelPhysicalResources_rim,Finset.mem_union,
        Finset.mem_image,Sum.inl.injEq,Sum.inr_ne_inl,and_false,exists_false,or_false,
        exists_eq_right,markedPackingRims]
    | inr e=>
      rcases e with ⟨v,z⟩
      simp only [N,Finset.mem_biUnion,Finset.mem_image,markedWheelPhysicalResources_spoke,
        Finset.mem_union,Sum.inl_ne_inr,and_false,exists_false,false_or,Sum.inr.injEq,Prod.mk.injEq]
      constructor
      · rintro ⟨W,⟨C,hC,rfl⟩,he,hv⟩
        exact ⟨v,⟨C,hC,Finset.mem_image.mpr hv⟩,rfl,he⟩
      · rintro ⟨v,⟨C,hC,hv⟩,he,hu⟩
        exact ⟨hubCycleWheel u C,⟨C,hC,rfl⟩,hu,he ▸ (Finset.mem_image.mp hv)⟩
  · intro v
    change (physicalEdgeGraph (markedPackingRims N)).degree v≤2
    rw [hr]
    exact marked_factor_physical_degree u hsep M hM v
  · intro W hW
    obtain ⟨C,hC,rfl⟩:=Finset.mem_image.mp hW
    rfl
  · intro e he
    rw [hr] at he
    obtain ⟨C,hC,he⟩:=Finset.mem_biUnion.mp he
    obtain ⟨i,hi,he⟩:=Finset.mem_image.mp he
    rw [←he]
    exact markedCycle_physical_edge_card tail head ktail khead m π b hm hb (hubCycleAsMarked u C) i

theorem marked_hub_factor_wheels_avoiding (u:U) (hm:1≤m) (hb:1≤b)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hsep:∀ v z,H₀ v u→Hₖ z u→v≠π z) (D:SimpleGraph V)
    (M:Finset (HubMarkedCycle (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val) m π b H₀ Hₖ u))
    (hM:∀ C∈M,∀ Z∈M,C≠Z→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u Z))
    (hcov:M.biUnion (hubMarkedCycleVertices u)=Finset.univ.filter (fun v=>H₀ v u∨Hₖ v u)):
    ∃ N:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ),
      (∀ W∈N,∀ Z∈N,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      N.biUnion markedWheelPhysicalResources=(markedPackingRims N).image Sum.inl∪
        (Finset.univ.filter (fun v=>H₀ v u∨Hₖ v u)).image (fun v=>Sum.inr (v,u))∧
      (∀ v,(markedPackingRimGraph N).degree v≤2)∧
      (∀ W∈N,W.2.val=u)∧(∀ e∈markedPackingRims N,e.card=2)∧Disjoint (markedPackingRimGraph N) D:=by
  let PE:=fun e:E=>¬D.Adj (tail e) (head e)
  let PK:=fun e:K=>¬D.Adj (ktail e) (π (khead e))
  let M':=M.image (hubMarkedCycleToLarger PE PK u)
  have hM':∀ C∈M',∀ Z∈M',C≠Z→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u Z):=by
    intro C hC Z hZ hne
    obtain ⟨C₀,hC₀,rfl⟩:=Finset.mem_image.mp hC
    obtain ⟨Z₀,hZ₀,rfl⟩:=Finset.mem_image.mp hZ
    exact hM C₀ hC₀ Z₀ hZ₀ (fun he=>hne (congrArg (hubMarkedCycleToLarger PE PK u) he))
  have hc':M'.biUnion (hubMarkedCycleVertices u)=Finset.univ.filter (fun v=>H₀ v u∨Hₖ v u):=by
    rw [Finset.image_biUnion]
    exact hcov
  obtain ⟨N,hN,hunion,hdegree,hhub,hpairs,hrim⟩:=marked_hub_factor_to_wheels u hm hb hp hsep M' hM' hc'
  refine ⟨N,hN,hunion,hdegree,hhub,hpairs,?_⟩
  apply disjoint_iff_inf_le.mpr
  intro x y hxy
  have he:({x,y}:Finset V)∈markedPackingRims N:=hxy.1.2
  rw [hrim,Finset.image_biUnion] at he
  obtain ⟨C,hC,he⟩:=Finset.mem_biUnion.mp he
  change _∈markedCyclePhysicalEdges tail head ktail khead m π b
    (markedCycleToLarger PE PK (hubCycleAsMarked u C)) at he
  rw [markedCycleToLarger_physical] at he
  exact (marked_cycle_rim_avoids_deleted_graph D (hubCycleAsMarked u C) x y he hxy.2).elim

end Oberwolfach
