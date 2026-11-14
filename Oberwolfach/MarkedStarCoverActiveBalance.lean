module

public import Oberwolfach.MarkedSamplePackingOutsideBalance
public import Oberwolfach.MarkedStarCoverDeletedSupport
public import Oberwolfach.MarkedRestrictedSampleOutsideBalance

@[expose] public section

/-! The balance input to the active cover-down theorem is derived after
covering the entire protected star. Restriction is to the exact complements
of its row and hub sets, using the same physically deleted outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V A U B Γ Color:Type} [Fintype V] [Fintype A] [Fintype U] [Fintype B]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder A] [DecidableEq U] [DecidableEq B]

theorem marked_star_cover_active_balance
    (f:A↪oV) (g:B↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm A)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hH:∀ x u,¬(H false x u∧H true x u))
    (X:Finset A) (Z:Finset B) (I T:Finset V) (J W:Finset U)
    (hX:∀ x,f x∈I↔x∈X) (hZ:∀ u,g u∈J↔u∈Z)
    (hfT:∀ x,x∈Finset.univ.image f↔x∉T) (hgW:∀ u,u∈Finset.univ.image g↔u∉W)
    (hT:∀ x,π x∈T↔x∈T):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    MarkedOutsideBalance tail head ktail khead (H true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)) m I J→
    ∀ M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
    (∀ Y∈M,∀ Y'∈M,Y≠Y'→Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Y'))→
    (∀ a:E₀⊕E₁,markedStarResource T W (Sum.inl (markedPhysicalEdge tail head ktail khead π a))→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources)→
    (∀ x u,H false x u∨H true x u→markedStarResource T W (Sum.inr (x,u))→
      Sum.inr (x,u)∈M.biUnion markedWheelPhysicalResources)→
    let σ':=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ (markedPackingRimGraph M).edgeFinset)
    let H':=fun b x u=>markedDeletePhysicalSpokes H (markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)) b (f x) (g u)
    let E₀':=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁':=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σ' (Sum.inl e)) true
    MarkedOutsideBalance (fun e:E₀'=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
      (Finset.univ.filter (fun z:A×B=>H' false z.1 z.2∨H' true z.1 z.2)) m X Z:=by
  intro E₀ E₁ tail head ktail khead hbal M hM hA hS
  have hb:=marked_sample_packing_deletion_outside_balance P π d m σ H hH I J hbal M hM
  obtain ⟨ha,hs⟩:=marked_star_cover_deleted_support P π d m σ H T W hT M hA hS
  apply marked_restricted_sample_outside_balance f g π ρ hf P d m
    (rawMarkedDeleteRims σ (markedPackingRimGraph M).edgeFinset)
    (markedDeletePhysicalSpokes H (markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)))
    X Z I J hX hZ
  · intro j e
    exact ⟨(hfT _).mpr (ha j e).1,(hfT _).mpr (ha j e).2⟩
  · intro x u hh
    exact ⟨(hfT _).mpr (hs x u hh).1,(hgW _).mpr (hs x u hh).2⟩
  · exact hb

end Oberwolfach
