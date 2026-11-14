module

public import Oberwolfach.MarkedPrescribedSpokeExtension
public import Oberwolfach.MarkedPhysicalDeletionExtensions
public import Oberwolfach.MarkedWheelFamilyLoads
public import Oberwolfach.MarkedPackingRimGraphs

@[expose] public section

/-! Complete one prescribed spoke after deleting actual physical rim edges.
The free rows avoid W; the prescribed row need not avoid W. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_spoke_wheel_after_deletion
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (D:SimpleGraph V) (δ:ℝ) (hδ:0≤δ) (hD:∀ a,(D.degree a:ℝ)≤δ)
    (j:Bool) (v:V) (u:U) (hroot:if j then HK v u else H₀ v u) (W:Finset V)
    (hbudget:(W.card:ℝ)+(l+5)*(2*b+1)+2*δ<c):
    ∃ C:MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      C.2.val=u ∧ v∈markedWheelRows C ∧ Disjoint (markedWheelRimGraph C) D ∧
      ∀ x∈markedWheelRows C,x=v∨x∉W:=by
  let PE:=fun e:E=>¬D.Adj (tail e) (head e)
  let PK:=fun e:K=>¬D.Adj (ktail e) (π (khead e))
  have Q':=marked_host_extensions_after_rim_deletion Q D δ hδ hD
  have hb':(W.card:ℝ)+(({v}:Finset V).card+l+4)*(2*b+1)<c-2*δ:=by
    simp only [Finset.card_singleton,Nat.cast_one]
    linarith only [hbudget]
  obtain ⟨C,hCu,hr,hav⟩:=marked_prescribed_spoke_extension Q' hl j v u hroot W {v} (by simp) hb'
  let C':=markedWheelToLarger PE PK (fun _ _ h=>h) (fun _ _ h=>h) C
  have hrows:markedWheelRows C'=markedWheelRows C:=rfl
  refine ⟨C',hCu,?_,?_,?_⟩
  · rw [hrows]
    exact (markedWheelPhysicalResources_spoke C v u).mp hr |>.2
  · apply disjoint_iff_inf_le.mpr
    intro x y hxy
    have he:({x,y}:Finset V)∈markedCyclePhysicalEdges tail head ktail khead (l+3) π b C'.1:=hxy.1.2
    change _∈markedCyclePhysicalEdges tail head ktail khead (l+3) π b (markedCycleToLarger PE PK C.1) at he
    rw [markedCycleToLarger_physical] at he
    exact (marked_cycle_rim_avoids_deleted_graph D C.1 x y he hxy.2).elim
  · intro x hx
    by_cases he:x=v
    · exact Or.inl he
    · rw [hrows] at hx
      exact Or.inr (hav x hx he).1

end Oberwolfach
