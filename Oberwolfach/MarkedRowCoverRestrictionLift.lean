module

public import Oberwolfach.MarkedRowCoverPackings
public import Oberwolfach.MarkedRestrictedFamilyIdentities

@[expose] public section

/-! Lift a whole row cover from a restricted host, preserving its exact
resource union, free degrees, row support and permitted hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head : E→V} {ktail khead : T→V} {H₀ HK H₀' HK' : V→U→Prop}
    {π : Equiv.Perm V} {m b : ℕ}

theorem marked_packing_lift_rim
    (PE : E→Prop) (PT : T→Prop)
    (hH₀ : ∀ x u,H₀' x u→H₀ x u) (hHK : ∀ x u,HK' x u→HK x u)
    (M : Finset (MarkedWheel (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e//PT e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' HK')) :
    markedPackingRimGraph (M.image (markedWheelToLarger PE PT hH₀ hHK))=markedPackingRimGraph M := by
  unfold markedPackingRimGraph markedPackingRims
  congr 1
  rw [Finset.image_biUnion]
  apply Finset.biUnion_congr rfl
  intro W hW
  exact markedCycleToLarger_physical PE PT W.1

theorem marked_packing_lift_spokes
    (PE : E→Prop) (PT : T→Prop)
    (hH₀ : ∀ x u,H₀' x u→H₀ x u) (hHK : ∀ x u,HK' x u→HK x u)
    (M : Finset (MarkedWheel (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e//PT e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' HK')) :
    markedPackingSpokes (M.image (markedWheelToLarger PE PT hH₀ hHK))=markedPackingSpokes M := by
  funext x u
  apply propext
  simp only [markedPackingSpokes,Finset.mem_image]
  constructor
  · rintro ⟨W,⟨Z,hZ,rfl⟩,hu,hx⟩
    exact ⟨Z,hZ,hu,hx⟩
  · rintro ⟨W,hW,hu,hx⟩
    exact ⟨markedWheelToLarger PE PT hH₀ hHK W,⟨W,hW,rfl⟩,hu,hx⟩

theorem marked_row_cover_lift
    (PE : E→Prop) (PT : T→Prop)
    (hH₀ : ∀ x u,H₀' x u→H₀ x u) (hHK : ∀ x u,HK' x u→HK x u)
    (M : Finset (MarkedWheel (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e//PT e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' HK'))
    (v : V) (F : Finset V) (required : Finset (Finset V⊕(V×U))) (Y : Finset U) (K : ℕ)
    (hM : MarkedRowCover M v F required Y K) :
    MarkedRowCover (M.image (markedWheelToLarger PE PT hH₀ hHK)) v F required Y K := by
  refine ⟨markedWheelToLarger_matching PE PT hH₀ hHK M hM.disjoint,?_,?_,?_,?_,?_,?_,?_⟩
  · intro W hW
    obtain ⟨Z,hZ,rfl⟩ := Finset.mem_image.mp hW
    exact hM.rows Z hZ
  · intro W hW
    obtain ⟨Z,hZ,rfl⟩ := Finset.mem_image.mp hW
    exact hM.hubs Z hZ
  · intro W hW
    obtain ⟨Z,hZ,rfl⟩ := Finset.mem_image.mp hW
    exact hM.root Z hZ
  · rw [markedWheelToLarger_cover]
    exact hM.covers
  · intro x
    have he := congrArg (fun G:SimpleGraph V=>(spanningRestriction G F).degree x)
      (marked_packing_lift_rim PE PT hH₀ hHK M)
    exact he.le.trans (by convert hM.rimDegree x using 1 <;> congr!)
  · simpa only [marked_packing_lift_spokes] using hM.rowDegree
  · simpa only [marked_packing_lift_spokes] using hM.columnDegree

end Oberwolfach
