module

public import Oberwolfach.MarkedActiveDeletedPreimages
public import Oberwolfach.MarkedPackingCoversOutsideInner
public import Oberwolfach.MarkedResourceEmbeddingGeometry

@[expose] public section

/-! The active cover returns to the original physical sample with its exact
resource set. Surviving edges outside the protected pair are covered; the
temporarily removed rows and hubs remain outside this packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A B Γ Color:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype B]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder A] [DecidableEq U] [DecidableEq B]

theorem marked_active_cover_packing_lift
    (f:A↪oV) (g:B↪U) (P:SimpleGraph V) (π:Equiv.Perm V) (ρ:Equiv.Perm A)
    (hf:∀ x,f (ρ x)=π (f x)) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (I T:Finset V) (J W:Finset U)
    (hfX:Finset.univ.image f=Finset.univ\T) (hgX:Finset.univ.image g=Finset.univ\W)
    (X:Finset A) (Z:Finset B) (hX:∀ x,f x∈I↔x∈X) (hZ:∀ u,g u∈J↔u∈Z)
    (M:Finset (MarkedActiveDeletedWheel f g P π ρ d m σ H DR DS))
    (hM:∀ C∈M,∀ C'∈M,C≠C'→Disjoint (markedWheelPhysicalResources C) (markedWheelPhysicalResources C')):
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset)
    let HA:=fun j x u=>markedDeletePhysicalSpokes H DS j (f x) (g u)
    let EA:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false
    let KA:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) true;
    (∀ a∈(Finset.univ:Finset (EA⊕KA))\M.biUnion markedWheelArcs,
      Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a∈X∧Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a∈X)→
    (∀ s∈(Finset.univ.filter (fun s:A×B=>HA false s.1 s.2∨HA true s.1 s.2))\M.biUnion markedWheelSpokePairs,
      s.1∈X∧s.2∈Z)→
    ∃ N:Finset (MarkedWheel
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      m π (3*d) (H false) (H true)),
    N.biUnion markedWheelPhysicalResources=(M.biUnion markedWheelPhysicalResources).image (markedResourceEmbedding f.toEmbedding g)∧
    (∀ C∈N,∀ C'∈N,C≠C'→Disjoint (markedWheelPhysicalResources C) (markedWheelPhysicalResources C'))∧
    Disjoint (markedPackingRimGraph N) DR∧
    (∀ x u,markedPackingSpokes N x u→¬DS.Adj (Sum.inl x) (Sum.inr u))∧
    (N.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
      (N.biUnion markedWheelPhysicalResources).filter (markedInnerResource (I\T) (J\W))∧
    (∀ j x y,x∉T→y∉T→
      markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) j x y=1→
      ¬DR.Adj x (if j then π y else y)→x∉I∨y∉I→
      Sum.inl ({x,if j then π y else y}:Finset V)∈N.biUnion markedWheelPhysicalResources)∧
    (∀ j x u,x∉T→u∉W→H j x u→¬DS.Adj (Sum.inl x) (Sum.inr u)→x∉I∨u∉J→
      Sum.inr (x,u)∈N.biUnion markedWheelPhysicalResources):=by
  intro σA HA EA KA hArcs hSpokes
  obtain ⟨N,hres,hN,hDR,hDS⟩:=marked_active_deleted_packing_lift f g P π ρ hf d m σ H DR DS M hM
  obtain ⟨hcoverR,hcoverS⟩:=marked_packing_covers_outside_inner M X Z Finset.univ
    (Finset.univ.filter (fun s:A×B=>HA false s.1 s.2∨HA true s.1 s.2)) hArcs hSpokes
  have hfnot:∀ x,f x∉T:=by
    intro x
    have hx:f x∈Finset.univ.image f:=Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
    rw [hfX] at hx
    exact (Finset.mem_sdiff.mp hx).2
  have hgnot:∀ u,g u∉W:=by
    intro u
    have hu:g u∈Finset.univ.image g:=Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩
    rw [hgX] at hu
    exact (Finset.mem_sdiff.mp hu).2
  refine ⟨N,hres,hN,hDR,hDS,?_,?_,?_⟩
  · rw [hres]
    exact markedResourceEmbedding_active_inner_filter f.toEmbedding g I T J W hfnot hgnot _
  · intro j x y hx hy hxy hD hout
    obtain ⟨a,hax,hay⟩:=marked_active_deleted_rim_preimage f g P π ρ hf d σ DR T hfX j x y hx hy hxy hD
    have haout:a.val.1∉X∨a.val.2∉X:=by
      rcases hout with h|h
      · exact Or.inl (fun hh=>h (hax ▸ (hX _).mpr hh))
      · exact Or.inr (fun hh=>h (hay ▸ (hX _).mpr hh))
    have hmem:Sum.inl ({a.val.1,if j then ρ a.val.2 else a.val.2}:Finset A)∈M.biUnion markedWheelPhysicalResources:=by
      cases j
      · exact hcoverR (Sum.inl a) (Finset.mem_univ _) haout
      · exact hcoverR (Sum.inr a) (Finset.mem_univ _) haout
    rw [hres]
    apply Finset.mem_image.mpr
    refine ⟨Sum.inl ({a.val.1,if j then ρ a.val.2 else a.val.2}:Finset A),hmem,?_⟩
    change Sum.inl (({a.val.1,if j then ρ a.val.2 else a.val.2}:Finset A).image f)=
      Sum.inl ({x,if j then π y else y}:Finset V)
    cases j <;> simp only [Finset.image_insert,Finset.image_singleton,
      Bool.false_eq_true,ite_false,ite_true,hf,hax,hay]
  · intro j x u hx hu hH hD hout
    obtain ⟨a,b,ha,hb,hab⟩:=marked_active_deleted_spoke_preimage f g H DS T W hfX hgX j x u hx hu hH hD
    have haout:a∉X∨b∉Z:=by
      rcases hout with h|h
      · exact Or.inl (fun hh=>h (ha ▸ (hX _).mpr hh))
      · exact Or.inr (fun hh=>h (hb ▸ (hZ _).mpr hh))
    have hmem:(a,b)∈Finset.univ.filter (fun s:A×B=>HA false s.1 s.2∨HA true s.1 s.2):=by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      cases j
      · exact Or.inl hab
      · exact Or.inr hab
    rw [hres]
    exact Finset.mem_image.mpr ⟨Sum.inr (a,b),hcoverS (a,b) hmem haout,by
      change Sum.inr (f a,g b)=Sum.inr (x,u)
      rw [ha,hb]⟩

end Oberwolfach
