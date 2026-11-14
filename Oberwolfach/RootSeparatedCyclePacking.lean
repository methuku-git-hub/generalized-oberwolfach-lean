module

public import Oberwolfach.FixedPathCycles
public import Oberwolfach.CycleVertexMatchingWeights

@[expose] public section
/-! Greedily choose pairwise vertex-disjoint cycles, each through exactly
one prescribed root, while avoiding all other roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem root_separated_cycle_packing (β:ℝ) (hβ:0<β) (r s:ℕ) (hr:3≤r):
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (G:SimpleGraph V),(∀ v,(1/2+β)*(Fintype.card V:ℝ)≤G.degree v)→
    ∀ T:Finset V,T.card≤s→∃ M:Finset (OrdinaryCycle G r),
      (∀ C∈M,∀ E∈M,C≠E→Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r E)) ∧
      T⊆M.biUnion (ordinaryCycleVertices G r) ∧
      (∀ C∈M,∃ x∈T,x∈ordinaryCycleVertices G r C ∧
        ∀ y∈T,y∈ordinaryCycleVertices G r C→y=x) ∧ M.card≤T.card:=by
  obtain ⟨N,hN⟩:=fixed_cycle_through_vertex β hβ r (s+r*s) hr
  refine ⟨N,?_⟩
  intro V _ _ hn G hdeg T hT
  have build:∀ P:Finset V,P⊆T→∃ M:Finset (OrdinaryCycle G r),
      (∀ C∈M,∀ E∈M,C≠E→Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r E)) ∧
      P⊆M.biUnion (ordinaryCycleVertices G r) ∧
      (∀ C∈M,∃ x∈P,x∈ordinaryCycleVertices G r C ∧
        ∀ y∈T,y∈ordinaryCycleVertices G r C→y=x) ∧ M.card≤P.card:=by
    intro P
    induction P using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨∅,?_,?_,?_,?_⟩ <;> simp
    | @insert x P hx ih =>
      intro hsub
      have hxT:x∈T:=hsub (Finset.mem_insert_self _ _)
      have hPT:P⊆T:=fun y hy=>hsub (Finset.mem_insert_of_mem hy)
      obtain ⟨M,hpack,hcover,hunique,hMcard⟩:=ih hPT
      let Used:=M.biUnion (ordinaryCycleVertices G r)
      have hUsed:Used.card≤r*P.card:=by
        have hh:=Finset.card_biUnion_le_card_mul M (ordinaryCycleVertices G r) r
          (by intro C hC;exact (ordinaryCycleVertices_card G r C).le)
        calc
          _ ≤ M.card*r := hh
          _ = r*M.card := Nat.mul_comm _ _
          _ ≤ r*P.card := Nat.mul_le_mul_left r hMcard
      have hxUsed:x∉Used:=by
        intro hxU
        obtain ⟨C,hCM,hxC⟩:=Finset.mem_biUnion.mp hxU
        obtain ⟨y,hyP,hyC,hyunique⟩:=hunique C hCM
        exact hx (by simpa [hyunique x hxT hxC] using hyP)
      let Forbidden:=(T.erase x)∪Used
      have hforbid:Forbidden.card≤s+r*s:=by
        change ((T.erase x)∪Used).card≤s+r*s
        have hh:=Finset.card_union_le (T.erase x) Used
        have he:(T.erase x).card≤s:=(Finset.card_erase_le (s:=T) (a:=x)).trans hT
        have hp:P.card≤s:=(Finset.card_le_card hPT).trans hT
        have hm:=Nat.mul_le_mul_left r hp
        omega
      have hxforbid:x∉Forbidden:=by simp [Forbidden,hxUsed]
      obtain ⟨C,hcycle,hCG,hxC,havoid⟩:=hN (Fintype.card V) hn V (le_refl _) G hdeg x Forbidden hforbid hxforbid
      let C':OrdinaryCycle G r:=⟨⟨C,hcycle⟩,hCG⟩
      have hxC':x∈ordinaryCycleVertices G r C':=by simpa only [ordinaryCycleVertices,Set.mem_toFinset] using hxC
      have hCavoid:∀ y∈ordinaryCycleVertices G r C',y∉Forbidden:=by
        intro y hy;apply havoid y;simpa only [ordinaryCycleVertices,Set.mem_toFinset] using hy
      have hCnew:C'∉M:=by
        intro hCM
        exact hxUsed (Finset.mem_biUnion.mpr ⟨C',hCM,hxC'⟩)
      refine ⟨insert C' M,?_,?_,?_,?_⟩
      · intro A hA E hE hne
        simp only [Finset.mem_insert] at hA hE
        rcases hA with rfl|hA <;> rcases hE with rfl|hE
        · exact (hne rfl).elim
        · apply Finset.disjoint_left.mpr
          intro y hyC hyE
          have hyU:y∈Used:=Finset.mem_biUnion.mpr ⟨E,hE,hyE⟩
          exact hCavoid y hyC (Finset.mem_union_right _ hyU)
        · apply Finset.disjoint_left.mpr
          intro y hyA hyC
          have hyU:y∈Used:=Finset.mem_biUnion.mpr ⟨A,hA,hyA⟩
          exact hCavoid y hyC (Finset.mem_union_right _ hyU)
        · exact hpack A hA E hE hne
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl|hy
        · exact Finset.mem_biUnion.mpr ⟨C',Finset.mem_insert_self _ _,hxC'⟩
        · obtain ⟨E,hE,hyE⟩:=Finset.mem_biUnion.mp (hcover hy)
          exact Finset.mem_biUnion.mpr ⟨E,Finset.mem_insert_of_mem hE,hyE⟩
      · intro E hE
        rcases Finset.mem_insert.mp hE with rfl|hE
        · refine ⟨x,Finset.mem_insert_self _ _,hxC',?_⟩
          intro y hyT hyC
          by_contra hne
          exact hCavoid y hyC (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne,hyT⟩))
        · obtain ⟨y,hyP,hyC,hyunique⟩:=hunique E hE
          exact ⟨y,Finset.mem_insert_of_mem hyP,hyC,hyunique⟩
      · rw [Finset.card_insert_of_notMem hCnew,Finset.card_insert_of_notMem hx]
        omega
  obtain ⟨M,hpack,hcover,hunique,hcard⟩:=build T (Finset.Subset.rfl)
  exact ⟨M,hpack,hcover,hunique,hcard⟩
end Oberwolfach
