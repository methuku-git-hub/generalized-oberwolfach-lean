module

public import Oberwolfach.MarkedAssignedRowWheel
public import Oberwolfach.MarkedPhysicalDeletionExtensions
public import Oberwolfach.MarkedPackingRimGraphs
public import Oberwolfach.MarkedWheelFamilyLoads

@[expose] public section

/-! Complete assigned root data after a realized physical rim deletion,
then lift the wheel without changing any physical resource. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {H₀ HK : V → U → Prop}
    {π : Equiv.Perm V} {b l : ℕ} {c ch : ℝ}

theorem marked_assigned_row_after_deletion
    (Q : MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl : 2≤l) (D : SimpleGraph V) (δ : ℝ) (hδ : 0≤δ) (hD : ∀ x, (D.degree x:ℝ)≤δ)
    (v a z : V) (u : U) (jin jout : Bool) (htypes : ¬(jin=true ∧ jout=true))
    (W Z : Finset V) (hv : v∈Z)
    (haW : a∉W) (hzW : z∉W) (haZ : a∉Z) (hzZ : z∉Z)
    (haz : ¬PermutationClose π b a z)
    (haF : ∀ x∈Z, ¬PermutationClose π b a x) (hzF : ∀ x∈Z, ¬PermutationClose π b z x)
    (haH : if jout then HK a u else H₀ a u) (hzH : H₀ z u)
    (hroot : if jin then HK v u else H₀ v u)
    (hopen : markedArcPresent tail head ktail khead jout v a)
    (hclose : markedArcPresent tail head ktail khead jin z v)
    (hopenD : ¬D.Adj v (if jout then π a else a))
    (hcloseD : ¬D.Adj z (if jin then π v else v))
    (hbudget : W.card+((Z.card:ℝ)+l+4)*(2*b+1)+2*δ<c) :
    ∃ p : Fin (l+3) ↪ V, ∃ C : MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      p 0=a ∧ p (Fin.last (l+2))=z ∧ C.2.val=u ∧
      (∀ i, C.1.val i=Fin.cons (α:=fun _=>V) v p (markedAssignedRowOrder (l+3) jin jout i)) ∧
      (∀ i, p i∉W ∧ p i∉Z ∧ ∀ x∈Z, ¬PermutationClose π b (p i) x) ∧
      PermutationSeparated π b p ∧ Disjoint (markedWheelRimGraph C) D := by
  let PE := fun e:E => ¬D.Adj (tail e) (head e)
  let PK := fun e:K => ¬D.Adj (ktail e) (π (khead e))
  have Q' := marked_host_extensions_after_rim_deletion Q D δ hδ hD
  have ho := (marked_arc_physical_restriction (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) D jout v a).mpr ⟨hopen,hopenD⟩
  have hc := (marked_arc_physical_restriction (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) D jin z v).mpr ⟨hclose,hcloseD⟩
  obtain ⟨p,C,hp0,hplast,hCu,hC,hav,hsep⟩ := marked_assigned_row_wheel Q' hl v a z u jin jout htypes
    W Z hv haW hzW haZ hzZ haz haF hzF haH hzH hroot ho hc (by linarith only [hbudget])
  let C' := markedWheelToLarger PE PK (fun _ _ h=>h) (fun _ _ h=>h) C
  refine ⟨p,C',hp0,hplast,hCu,hC,hav,hsep,?_⟩
  apply disjoint_iff_inf_le.mpr
  intro x y hxy
  have he : ({x,y}:Finset V)∈markedCyclePhysicalEdges tail head ktail khead (l+3) π b C'.1 := hxy.1.2
  change _∈markedCyclePhysicalEdges tail head ktail khead (l+3) π b (markedCycleToLarger PE PK C.1) at he
  rw [markedCycleToLarger_physical] at he
  exact (marked_cycle_rim_avoids_deleted_graph D C.1 x y he hxy.2).elim

end Oberwolfach
