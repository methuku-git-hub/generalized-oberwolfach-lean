module

public import Oberwolfach.MarkedAssignedRowWheel
public import Oberwolfach.MarkedSpokePairIdentity
public import Oberwolfach.MarkedWheelFamilyLoads

@[expose] public section

/-! Locate the prescribed row and its two incident arcs in the resulting
wheel, retaining the physical permutation on a marked head. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {H₀ HK : V → U → Prop}
    {π : Equiv.Perm V} {b n : ℕ}

theorem markedAssignedRowOrder_canonical (m : ℕ) (jin jout : Bool) :
    markedAssignedRowOrder m jin jout=
      canonicalMarkedRotation (if jout then 0 else if jin then Fin.last m else 2) := by
  cases jout <;> simp [markedAssignedRowOrder,markedRootOrder_eq_canonical]

theorem markedAssignedRowOrder_rotate (m : ℕ) (jin jout : Bool) (i : Fin (m+1)) :
    markedAssignedRowOrder m jin jout (finRotate (m+1) i)=
      finRotate (m+1) (markedAssignedRowOrder m jin jout i) := by
  rw [markedAssignedRowOrder_canonical]
  exact canonicalMarkedRotation_rotate _ _

theorem marked_one_root_rows (p : Fin (n+1) → V) (v : V) (ρ : Equiv.Perm (Fin (n+2)))
    (C : MarkedWheel tail head ktail khead (n+1) π b H₀ HK)
    (hC : ∀ i, C.1.val i=Fin.cons (α:=fun _=>V) v p (ρ i)) :
    markedWheelRows C=insert v (Finset.univ.image p) := by
  ext x
  simp only [markedWheelRows,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨i,hi⟩
    rw [hC] at hi
    generalize ρ i=j at hi
    revert hi
    refine Fin.cases (fun h => Or.inl h.symm) (fun j h => Or.inr ⟨j,h⟩) j
  · rintro (rfl|⟨i,hi⟩)
    · exact ⟨ρ.symm 0,by rw [hC,Equiv.apply_symm_apply]; rfl⟩
    · exact ⟨ρ.symm i.succ,by rw [hC,Equiv.apply_symm_apply]; exact hi⟩

theorem marked_assigned_row_root_resources (hn : 2≤n) (p : Fin (n+1) → V)
    (v : V) (jin jout : Bool) (htypes : ¬(jin=true ∧ jout=true))
    (C : MarkedWheel tail head ktail khead (n+1) π b H₀ HK)
    (hC : ∀ i, C.1.val i=Fin.cons (α:=fun _=>V) v p (markedAssignedRowOrder (n+1) jin jout i)) :
    Sum.inl (if jout then ({v,π (p 0)}:Finset V) else {v,p 0})∈markedWheelPhysicalResources C ∧
    Sum.inl (if jin then ({p (Fin.last n),π v}:Finset V) else {p (Fin.last n),v})∈markedWheelPhysicalResources C ∧
    Sum.inr (v,C.2.val)∈markedWheelPhysicalResources C := by
  let k : Fin (n+2) := if jout then 0 else if jin then Fin.last (n+1) else 2
  have hraw : ∀ i, C.1.val i=Fin.cons (α:=fun _=>V) v p (canonicalMarkedRotation k i) := by
    intro i; rw [hC,markedAssignedRowOrder_canonical]
  have hzero : (0 : Fin (n+2))=k ↔ jout=true := by
    have h02 : (0 : Fin (n+2))≠2 := by
      intro h; have hh := congrArg Fin.val h
      change 0=2%(n+2) at hh
      rw [Nat.mod_eq_of_lt (by omega)] at hh; omega
    have h0last : (0 : Fin (n+2))≠Fin.last (n+1) := by
      intro h; have hh := congrArg Fin.val h; simp only [Fin.val_zero,Fin.val_last] at hh; omega
    cases jout <;> cases jin <;> simp [k,h02,h0last]
  have hlast : (Fin.last (n+1) : Fin (n+2))=k ↔ jin=true := by
    have hl2 : (Fin.last (n+1) : Fin (n+2))≠2 := by
      intro h; have hh := congrArg Fin.val h
      change n+1=2%(n+2) at hh
      rw [Nat.mod_eq_of_lt (by omega)] at hh; omega
    have hl0 : (Fin.last (n+1) : Fin (n+2))≠0 := by
      intro h; have hh := congrArg Fin.val h; simp only [Fin.val_zero,Fin.val_last] at hh; omega
    cases jout <;> cases jin <;> simp_all [k]
  have hmem (i : Fin (n+2)) : markedRawRimResource (U:=U) π (Fin.cons v p) k i∈markedWheelPhysicalResources C := by
    rw [←marked_wheel_raw_rim_position C _ k hraw i,←markedWheelPositionResource_image]
    exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
  refine ⟨?_,?_,?_⟩
  · have hr0 : finRotate (n+2) (0 : Fin (n+2))=(0 : Fin (n+1)).succ :=
      finRotate_castSucc_eq_succ (n+1) 0
    simpa only [markedRawRimResource,hzero,hr0,Fin.cons_zero,Fin.cons_succ] using hmem 0
  · have hl : (Fin.last (n+1) : Fin (n+2))=(Fin.last n).succ := rfl
    have hh := hmem (Fin.last (n+1))
    unfold markedRawRimResource at hh
    simp only [hlast,finRotate_last] at hh
    simpa only [hl,Fin.cons_zero,Fin.cons_succ] using hh
  · rw [markedWheelPhysicalResources_spoke]
    refine ⟨rfl,?_⟩
    change v∈markedWheelRows C
    rw [marked_one_root_rows p v _ C hC]
    exact Finset.mem_insert_self _ _

end Oberwolfach
