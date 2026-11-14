module

public import Oberwolfach.MarkedFiniteTerminalAbsorberAvoidance
public import Oberwolfach.MarkedTerminalRemainderCounts

@[expose] public section

/-! One fixed marked terminal absorber works for every later divisible
subgraph of the terminal host. At most 2^(2s²) alternatives occur on at
most s auxiliary vertices, so the reservation size is independent of the
ambient order. No remainder is chosen before the reservoir is fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_universal_terminal_absorber_avoiding
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (H₀ HK:V→U→Prop)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (b l s a₀ b₀ f:ℕ) (ε:ℝ)
    (habs:MarkedFiniteAbsorberProperty tail head ktail khead H₀ HK π b l ε s a₀ b₀ f)
    (X:Finset V) (Z:Finset U) (F₀:Finset (Finset V⊕(V×U)))
    (W:Finset V) (B:Finset U) (hXW:X⊆W) (hZB:Z⊆B)
    (hW:(W.card:ℝ)≤ε*Fintype.card V+f) (hB:(B.card:ℝ)≤ε*Fintype.card V+f)
    (hsize:X.card+Z.card≤s)
    (hbudget:F₀.card+2^(2*s^2)*(2*a₀^2+a₀*b₀)≤f)
    (A₀:Finset (E⊕K)) (S₀:Finset (V×U))
    (hr:markedRemainderRows tail head ktail khead A₀ S₀⊆X)
    (hu:markedRemainderHubs S₀⊆Z)
    (hsp:∀ z∈S₀,H₀ z.1 z.2∨HK z.1 z.2):
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      Disjoint C.edges F₀∧C.edges.card≤2^(2*s^2)*(2*a₀^2+a₀*b₀)∧
      C.rows.card≤2^(2*s^2)*a₀∧C.hubs.card≤2^(2*s^2)*b₀∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π W B e)∧
      HasResourceDecomposition
        (fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W) C.edges∧
      ∀ A⊆A₀,∀ S⊆S₀,MarkedRemainderDivisible tail head ktail khead HK A S (l+4)→
        IsResourceAbsorber
          (fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W)
          (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr) C.edges := by
  let I:Type:={z:A₀.powerset×S₀.powerset //
    MarkedRemainderDivisible tail head ktail khead HK z.1.val z.2.val (l+4)}
  let A:I→Finset (E⊕K):=fun i=>i.val.1.val
  let S:I→Finset (V×U):=fun i=>i.val.2.val
  have hA (i:I):A i⊆A₀:=Finset.mem_powerset.mp i.val.1.property
  have hS (i:I):S i⊆S₀:=Finset.mem_powerset.mp i.val.2.property
  have hI:Fintype.card I≤2^(2*s^2):=by
    have hbase:Fintype.card I≤Fintype.card (A₀.powerset×S₀.powerset):=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    have he:Fintype.card (A₀.powerset×S₀.powerset)=2^(A₀.card+S₀.card):=by
      simp only [Fintype.card_prod,Fintype.card_coe,Finset.card_powerset,pow_add]
    rw [he] at hbase
    exact hbase.trans (Nat.pow_le_pow_right (by omega:0<2)
      (marked_terminal_resource_count tail head ktail khead π hp A₀ S₀ X Z s hr hu hsize))
  have hf:F₀.card+Fintype.card I*(2*a₀^2+a₀*b₀)≤f:=
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ hI) _).trans hbudget
  obtain ⟨C,hC,hcard,hrows,hhubs,hOld,hdec,hall⟩:=marked_finite_terminal_absorber_avoiding
    tail head ktail khead π H₀ HK b l s a₀ b₀ f ε habs W B F₀ hW hB hf A S
    (fun i=>(Nat.add_le_add
      (Finset.card_le_card ((marked_remainder_rows_mono tail head ktail khead (hA i) (hS i)).trans hr))
      (Finset.card_le_card ((Finset.image_subset_image (hS i)).trans hu))).trans hsize)
    (fun i=>i.property)
    (fun i=>(marked_remainder_rows_mono tail head ktail khead (hA i) (hS i)).trans (hr.trans hXW))
    (fun i=>(Finset.image_subset_image (hS i)).trans (hu.trans hZB))
    (fun i z hz=>hsp z (hS i hz))
  refine ⟨C,hC,hcard.trans (Nat.mul_le_mul_right _ hI),hrows.trans (Nat.mul_le_mul_right _ hI),
    hhubs.trans (Nat.mul_le_mul_right _ hI),hOld,hdec,?_⟩
  intro A' hA' S' hS' hdiv
  let i:I:=⟨(⟨A',Finset.mem_powerset.mpr hA'⟩,⟨S',Finset.mem_powerset.mpr hS'⟩),hdiv⟩
  exact hall i

end Oberwolfach
