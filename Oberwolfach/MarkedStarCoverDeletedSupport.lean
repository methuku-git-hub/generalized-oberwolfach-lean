module

public import Oberwolfach.MarkedFiniteDeletionDegrees

@[expose] public section

/-! Covering every physical resource incident with protected rows or hubs
leaves all surviving auxiliary arc endpoints and spoke endpoints outside
those sets. The permutation invariance is used for marked rim endpoints. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_star_cover_deleted_support
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (T:Finset V) (W:Finset U) (hT:∀ x,π x∈T↔x∈T):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    ∀ M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
    (∀ a:E₀⊕E₁,markedStarResource T W (Sum.inl (markedPhysicalEdge tail head ktail khead π a))→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources)→
    (∀ x u,H false x u∨H true x u→markedStarResource T W (Sum.inr (x,u))→
      Sum.inr (x,u)∈M.biUnion markedWheelPhysicalResources)→
    let σ':=rawMarkedDeleteRims σ (markedPackingRimGraph M).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs))
    (∀ j,∀ e:MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) j,e.val.1∉T∧e.val.2∉T)∧
    (∀ x u,H' false x u∨H' true x u→x∉T∧u∉W):=by
  intro E₀ E₁ tail head ktail khead M hA hS
  have hp:Function.Injective (markedPhysicalEdge tail head ktail khead π):=
    markedSampleArc_physical_injective P π (3*d) _
  have ha (a:E₀⊕E₁) (hn:a∉M.biUnion markedWheelArcs):
      Sum.elim tail ktail a∉T∧Sum.elim head khead a∉T:=by
    have hx:¬(Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T):=by
      intro hx
      have he:=hA a ((marked_physical_rim_star_iff tail head ktail khead π T W hT a).mpr hx)
      rw [←markedPackingResources_eq_finite] at he
      exact hn ((markedFiniteResources_rim tail head ktail khead π hp _ _ a).mp he)
    exact not_or.mp hx
  have hnot (a:E₀⊕E₁) (hn:Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉
      (markedPackingRimGraph M).edgeFinset):a∉M.biUnion markedWheelArcs:=by
    rw [←markedSampleArcSetGraph_packing P π d m σ H M,markedSampleArcSetGraph_coordinate] at hn
    exact hn
  constructor
  · intro j e
    have he:=(markedPhysicalRim_delete_iff P π d σ (markedPackingRimGraph M).edgeFinset j _ _).mp e.property
    cases j with
    | false=>exact ha (Sum.inl ⟨e.val,he.1⟩) (hnot _ he.2)
    | true=>exact ha (Sum.inr ⟨e.val,he.1⟩) (hnot _ he.2)
  · intro x u hu
    have ho:H false x u∨H true x u:=hu.imp And.left And.left
    have hn:¬(markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)).Adj (Sum.inl x) (Sum.inr u):=
      hu.elim And.right And.right
    have hx:¬(x∈T∨u∈W):=by
      intro hx
      have he:=hS x u ho hx
      rw [←markedPackingResources_eq_finite] at he
      have hh:=(markedFiniteResources_spoke tail head ktail khead π _ _ (x,u)).mp he
      exact hn ((markedFiniteSpokeGraph_adj _ x u).mpr hh)
    exact not_or.mp hx

end Oberwolfach
