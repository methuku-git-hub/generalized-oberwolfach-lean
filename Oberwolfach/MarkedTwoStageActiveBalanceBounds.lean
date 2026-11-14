module

public import Oberwolfach.MarkedCanonicalActiveBalanceBounds
public import Oberwolfach.MarkedCanonicalDeletedPacking
public import Oberwolfach.MarkedStarCoverDeletedSupport

@[expose] public section

/-! Quantitative balance on the actual active sample after a canonical
prior deletion and a constructed star-cover packing. The original-host
occurrence complement and the active sample are identified exactly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U VA UA Γ Color:Type} [Fintype V] [Fintype U] [Fintype VA] [Fintype UA]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder VA] [DecidableEq U] [DecidableEq UA]

theorem marked_two_stage_active_balance_bounds
    (f:VA↪oV) (g:UA↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm VA)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (T:Finset V) (W:Finset U) (hT:∀ x,π x∈T↔x∈T)
    (hfT:∀ v,v∈Finset.univ.image f↔v∉T) (hgW:∀ u,u∈Finset.univ.image g↔u∉W)
    (X:Finset VA) (Z:Finset UA) (I:Finset V) (J:Finset U)
    (hX:∀ x,f x∈I↔x∈X) (hZ:∀ u,g u∈J↔u∈Z):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2);
    ∀ (A:Finset (E₀⊕E₁)) (B:Finset (V×U)),
    let DR:=markedSampleArcSetGraph P π d σ A
    let DS:=markedFiniteSpokeGraph B
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E₀':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    ∀ M:Finset (MarkedPhysicalDeletedSampleWheel P π d m σ DR DS H),
    (∀ Y∈M,∀ Z∈M,Y≠Z→Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z))→
    (∀ a:E₀'⊕E₁',markedStarResource T W
      (Sum.inl (markedPhysicalEdge (fun e=>e.val.1) (fun e=>e.val.2) (fun e=>e.val.1) (fun e=>e.val.2) π a))→
      Sum.inl (markedPhysicalEdge (fun e=>e.val.1) (fun e=>e.val.2) (fun e=>e.val.1) (fun e=>e.val.2) π a)
        ∈M.biUnion markedWheelPhysicalResources)→
    (∀ v u,H' false v u∨H' true v u→markedStarResource T W (Sum.inr (v,u))→
      Sum.inr (v,u)∈M.biUnion markedWheelPhysicalResources)→
    let N:=M.image (markedPhysicalDeletedSampleWheelLift P π d m σ DR DS H);
    ∀ (εF εI:ℝ),
    (∀ (z:V⊕U),Sum.elim (fun v=>v∉T) (fun u=>u∉W) z→∀ i:Fin 4,
      |markedFiniteBalance (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:E₁=>e.val.1) (fun e=>e.val.2)
        (H true) (Finset.univ\(A∪N.biUnion markedWheelArcs)) (S\(B∪N.biUnion markedWheelSpokePairs)) m z i|≤εF∧
      |markedFiniteDomainBalance (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:E₁=>e.val.1) (fun e=>e.val.2)
        (H true) (Finset.univ\(A∪N.biUnion markedWheelArcs)) (S\(B∪N.biUnion markedWheelSpokePairs)) m I J z i|≤εI)→
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ' (markedPackingRimGraph M).edgeFinset)
    let HA:=fun j x u=>markedDeletePhysicalSpokes H' (markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)) j (f x) (g u)
    let EA₀:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false
    let EA₁:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) true
    let SA:=Finset.univ.filter (fun s:VA×UA=>HA false s.1 s.2∨HA true s.1 s.2);
    ∀ (z:VA⊕UA) (i:Fin 4),
    |markedFiniteBalance (fun e:EA₀=>e.val.1) (fun e=>e.val.2) (fun e:EA₁=>e.val.1) (fun e=>e.val.2)
      (HA true) Finset.univ SA m z i|≤εF∧
    |markedFiniteDomainBalance (fun e:EA₀=>e.val.1) (fun e=>e.val.2) (fun e:EA₁=>e.val.1) (fun e=>e.val.2)
      (HA true) Finset.univ SA m X Z z i|≤εI:=by
  intro E₀ E₁ S A B DR DS σ' H' E₀' E₁' M hM hcovA hcovS N εF εI hbound
  obtain ⟨hres,hN,hNA,hNS,hσeq,hHeq⟩:=marked_canonical_deleted_packing P π d m σ H A B M hM
  obtain ⟨hsa,hss⟩:=marked_star_cover_deleted_support P π d m σ' H' T W hT M hcovA hcovS
  have hfa:∀ v,f v∉T:=fun v=>(hfT (f v)).mp (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)
  have hga:∀ u,g u∉W:=fun u=>(hgW (g u)).mp (Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩)
  have hAs:∀ j,∀ e:MarkedSampleArc P π (3*d)
      (fun e=>rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ (A∪N.biUnion markedWheelArcs)).edgeFinset (Sum.inl e)) j,
      e.val.1∈Finset.univ.image f∧e.val.2∈Finset.univ.image f:=by
    rw [←hσeq]
    intro j e
    exact ⟨(hfT _).mpr (hsa j e).1,(hfT _).mpr (hsa j e).2⟩
  have hSs:∀ v u,
      markedDeletePhysicalSpokes H (markedFiniteSpokeGraph (B∪N.biUnion markedWheelSpokePairs)) false v u∨
      markedDeletePhysicalSpokes H (markedFiniteSpokeGraph (B∪N.biUnion markedWheelSpokePairs)) true v u→
      v∈Finset.univ.image f∧u∈Finset.univ.image g:=by
    rw [←hHeq]
    intro v u h
    exact ⟨(hfT _).mpr (hss v u h).1,(hgW _).mpr (hss v u h).2⟩
  have hh:=marked_canonical_active_balance_bounds f g π ρ hf P d m σ H T W hfa hga
    X Z I J hX hZ (A∪N.biUnion markedWheelArcs) (B∪N.biUnion markedWheelSpokePairs) εF εI hbound hAs hSs
  dsimp only
  dsimp only at hh
  rw [hσeq,hHeq]
  exact hh

end Oberwolfach
