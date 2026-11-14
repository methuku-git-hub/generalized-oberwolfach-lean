module

public import Oberwolfach.MarkedFactorPhysical

@[expose] public section

/-! Pull a forbidden physical rim graph back to auxiliary cycle labels.
Both directions of a twisted edge are included; its degree costs at most
three times the physical degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def markedPhysicalConflictGraph (D:SimpleGraph V) (π:Equiv.Perm V) : SimpleGraph V where
  Adj x y:=x≠y ∧ (D.Adj x y ∨ D.Adj x (π y) ∨ D.Adj y (π x))
  symm:=⟨by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    rcases h.2 with h|h|h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless:=⟨by intro x h;exact h.1 rfl⟩

theorem marked_physical_conflict_degree (D:SimpleGraph V) (π:Equiv.Perm V) (x:V) :
    (markedPhysicalConflictGraph D π).degree x≤2*D.degree x+D.degree (π x) := by
  have hs : (markedPhysicalConflictGraph D π).neighborFinset x⊆
      (D.neighborFinset x)∪((D.neighborFinset x).image π.symm)∪D.neighborFinset (π x) := by
    intro y hy
    have hh:=(SimpleGraph.mem_neighborFinset _ _ _).mp hy
    rcases hh.2 with h|h|h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((SimpleGraph.mem_neighborFinset _ _ _).mpr h))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨π y,(SimpleGraph.mem_neighborFinset _ _ _).mpr h,π.symm_apply_apply y⟩))
    · exact Finset.mem_union_right _ ((SimpleGraph.mem_neighborFinset _ _ _).mpr h.symm)
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  calc
    _ ≤ _ := Finset.card_le_card hs
    _ ≤ ((D.neighborFinset x)∪((D.neighborFinset x).image π.symm)).card+(D.neighborFinset (π x)).card := Finset.card_union_le _ _
    _ ≤ (D.neighborFinset x).card+((D.neighborFinset x).image π.symm).card+(D.neighborFinset (π x)).card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 2*D.degree x+D.degree (π x) := by
      have hh : ((D.neighborFinset x).image π.symm).card≤(D.neighborFinset x).card:=Finset.card_image_le
      simp only [SimpleGraph.card_neighborFinset_eq_degree] at hh ⊢
      omega

theorem marked_physical_conflict_degree_bound (D:SimpleGraph V) (π:Equiv.Perm V) (δ:ℝ)
    (hD:∀ x,(D.degree x:ℝ)≤δ) (x:V) :
    ((markedPhysicalConflictGraph D π).degree x:ℝ)≤3*δ := by
  have hh:=Nat.cast_le (α:=ℝ).mpr (marked_physical_conflict_degree D π x)
  push_cast at hh
  linarith [hD x,hD (π x)]

theorem no_adjacency_of_pair_equality (D:SimpleGraph V) {a b x y:V}
    (hab:¬D.Adj a b) (he:({a,b}:Finset V)={x,y}) : ¬D.Adj x y := by
  intro hxy
  have hx:x=a∨x=b:=by
    have h:x∈({a,b}:Finset V):=by rw [he];simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using h
  have hy:y=a∨y=b:=by
    have h:y∈({a,b}:Finset V):=by rw [he];simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using h
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
  · exact D.irrefl hxy
  · exact hab hxy
  · exact hab hxy.symm
  · exact D.irrefl hxy

variable {U E K:Type} {tail head:E→V} {ktail khead:K→V}
    {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_factor_avoids_physical_rims (hm:0<m) (u:U)
    (M:Finset (HubMarkedCycle tail head ktail khead m π b H₀ HK u)) (D:SimpleGraph V)
    (havoid:∀ C∈M,∀ x∈hubMarkedCycleVertices u C,∀ y∈hubMarkedCycleVertices u C,
      ¬(markedPhysicalConflictGraph D π).Adj x y) :
    Disjoint (physicalEdgeGraph (M.biUnion (hubCyclePhysicalEdges u))) D := by
  apply disjoint_iff_inf_le.mpr
  intro x y hxy
  obtain ⟨C,hC,he⟩:=Finset.mem_biUnion.mp hxy.1.2
  obtain ⟨j,_,hj⟩:=Finset.mem_image.mp he
  dsimp only [Function.comp_apply] at hj
  rw [markedCycle_physical_pair] at hj
  have hv (i:Fin (m+1)):C.val i∈hubMarkedCycleVertices u C:=Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hnot:¬D.Adj (C.val j) (twistedTupleHead π C.val j):=by
    refine Fin.lastCases ?_ (fun k=>?_) j
    · simp only [twistedTupleHead,Fin.snoc_last]
      intro hh
      apply havoid C hC _ (hv (Fin.last m)) _ (hv 0)
      refine ⟨?_,Or.inr (Or.inl hh)⟩
      have hi:=permutationSeparated_injective π b C.val C.property.1.1
      intro h
      have hc:=congrArg Fin.val (hi h)
      simp only [Fin.val_last,Fin.val_zero] at hc
      omega
    · simp only [twistedTupleHead,Fin.snoc_castSucc]
      intro hh
      apply havoid C hC _ (hv k.castSucc) _ (hv k.succ)
      refine ⟨?_,Or.inl hh⟩
      have hi:=permutationSeparated_injective π b C.val C.property.1.1
      intro h
      have hc:=congrArg Fin.val (hi h)
      simp only [Fin.val_castSucc,Fin.val_succ] at hc
      omega
  exact (no_adjacency_of_pair_equality D hnot hj) hxy.2

end Oberwolfach
