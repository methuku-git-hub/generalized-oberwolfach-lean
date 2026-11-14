module

public import Oberwolfach.MarkedAssignedRowGeometry

@[expose] public section

/-! Every rim edge of a completed row wheel is either one of its two
prescribed root edges or has both physical endpoints in the free row set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {H₀ HK : V → U → Prop}
    {π : Equiv.Perm V} {b n : ℕ}

def markedRowRootRims (π : Equiv.Perm V) (v a z : V) (jin jout : Bool) : Finset (Finset V) :=
  {if jout then {v,π a} else {v,a},if jin then {z,π v} else {z,v}}

theorem marked_row_raw_rim_classification (hn : 2≤n) (p : Fin (n+1) → V)
    (v : V) (jin jout : Bool) (htypes : ¬(jin=true ∧ jout=true))
    (X : Finset V) (hX : ∀ x, x∈X → π x∈X) (hp : ∀ i, p i∈X)
    (i : Fin (n+2)) :
    let k : Fin (n+2) := if jout then 0 else if jin then Fin.last (n+1) else 2
    let f := Fin.cons (α:=fun _=>V) v p
    let e : Finset V := if i=k then {f i,π (f (finRotate (n+2) i))} else {f i,f (finRotate (n+2) i)}
    e⊆X ∨ e∈markedRowRootRims π v (p 0) (p (Fin.last n)) jin jout := by
  dsimp only
  have h02 : (0 : Fin (n+2))≠2 := by
    intro h; have hh := congrArg Fin.val h
    change 0=2%(n+2) at hh
    rw [Nat.mod_eq_of_lt (by omega)] at hh; omega
  have h0last : (0 : Fin (n+2))≠Fin.last (n+1) := by
    intro h; have hh := congrArg Fin.val h; simp only [Fin.val_zero,Fin.val_last] at hh; omega
  have hl2 : (Fin.last (n+1) : Fin (n+2))≠2 := by
    intro h; have hh := congrArg Fin.val h
    change n+1=2%(n+2) at hh
    rw [Nat.mod_eq_of_lt (by omega)] at hh; omega
  refine Fin.cases ?_ (fun j => ?_) i
  · right
    have hr : finRotate (n+2) (0 : Fin (n+2))=(0 : Fin (n+1)).succ := finRotate_castSucc_eq_succ (n+1) 0
    cases jout <;> cases jin <;>
      simp [hr,markedRowRootRims,h02,h0last]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · right
      have hl : (Fin.last n).succ=Fin.last (n+1) := rfl
      rw [hl,finRotate_last]
      have hh : Fin.cons (α:=fun _=>V) v p (Fin.last (n+1))=p (Fin.last n) := rfl
      cases jout <;> cases jin <;> simp_all [markedRowRootRims,hh]
    · left
      have hi : j.castSucc.succ=j.succ.castSucc := rfl
      rw [hi,finRotate_castSucc_eq_succ]
      have hv : Fin.cons (α:=fun _=>V) v p j.succ.castSucc=p j.castSucc := by rw [←hi,Fin.cons_succ]
      simp only [hv,Fin.cons_succ]
      split_ifs <;> simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      all_goals first | exact ⟨hp _,hX _ (hp _)⟩ | exact ⟨hp _,hp _⟩

theorem marked_assigned_row_rim_classification (hn : 2≤n) (p : Fin (n+1) → V)
    (v : V) (jin jout : Bool) (htypes : ¬(jin=true ∧ jout=true))
    (X : Finset V) (hX : ∀ x, x∈X → π x∈X) (hp : ∀ i, p i∈X)
    (C : MarkedWheel tail head ktail khead (n+1) π b H₀ HK)
    (hC : ∀ i, C.1.val i=Fin.cons (α:=fun _=>V) v p (markedAssignedRowOrder (n+1) jin jout i)) :
    ∀ e∈markedCyclePhysicalEdges tail head ktail khead (n+1) π b C.1,
      e⊆X ∨ e∈markedRowRootRims π v (p 0) (p (Fin.last n)) jin jout := by
  intro e he
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp he
  let k : Fin (n+2) := if jout then 0 else if jin then Fin.last (n+1) else 2
  let ρ := canonicalMarkedRotation k
  have hraw : ∀ i, C.1.val i=Fin.cons (α:=fun _=>V) v p (ρ i) := by
    intro i; rw [hC,markedAssignedRowOrder_canonical]
  have hr := marked_wheel_raw_rim_position C (Fin.cons v p) k hraw (ρ i)
  change markedWheelPositionResource C (Sum.inl (ρ.symm (ρ i))) = _ at hr
  rw [Equiv.symm_apply_apply] at hr
  have heq : e=(if ρ i=k then
      {Fin.cons (α:=fun _=>V) v p (ρ i),π (Fin.cons (α:=fun _=>V) v p (finRotate (n+2) (ρ i)))}
      else {Fin.cons (α:=fun _=>V) v p (ρ i),Fin.cons (α:=fun _=>V) v p (finRotate (n+2) (ρ i))}) := by
    apply Sum.inl_injective (β:=V×U)
    calc
      Sum.inl e = markedWheelPositionResource C (Sum.inl i) := congrArg Sum.inl he.symm
      _ = _ := hr
  rw [heq]
  exact marked_row_raw_rim_classification hn p v jin jout htypes X hX hp (ρ i)

theorem marked_row_root_rim_not_inside (X : Finset V) (hX : ∀ x, π x∈X ↔ x∈X)
    (v a z : V) (hv : v∉X) (jin jout : Bool) :
    ∀ e∈markedRowRootRims π v a z jin jout, ¬e⊆X := by
  intro e he
  rcases Finset.mem_insert.mp he with rfl|he
  · intro hh
    cases jout <;> exact hv (hh (by simp))
  · rw [Finset.mem_singleton.mp he]
    intro hh
    cases jin
    · exact hv (hh (by simp))
    · exact hv ((hX v).mp (hh (by simp)))

end Oberwolfach
