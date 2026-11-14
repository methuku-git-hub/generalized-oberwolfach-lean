module

public import Oberwolfach.FiniteSeparatedRowHubChoices

@[expose] public section

/-! Finite row-and-hub choices whose candidate types depend on the index.
The uniform accumulated budgets are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V U:Type} [Fintype I] [DecidableEq I] [DecidableEq V] [DecidableEq U]

theorem finite_dependent_separated_choices
    (C:I→Type) (π:Equiv.Perm V) (b:ℕ) (rows:∀ i,C i→Finset V) (hubs:∀ i,C i→Finset U)
    (Good:∀ i,C i→Prop) (R:Finset V) (B:Finset U) (q t:ℕ)
    (hchoose:∀ R':Finset V,∀ B':Finset U,R⊆R'→B⊆B'→
      R'.card≤R.card+Fintype.card I*q→B'.card≤B.card+Fintype.card I*t→∀ i:I,
      ∃ c:C i,Good i c∧(rows i c).card≤q∧(hubs i c).card≤t∧Disjoint (rows i c) R'∧Disjoint (hubs i c) B'∧
        ∀ v∈rows i c,∀ w∈R',¬PermutationClose π b v w):
    ∃ f:∀ i,C i,
      (∀ i,Good i (f i)∧(rows i (f i)).card≤q∧(hubs i (f i)).card≤t∧
        Disjoint (rows i (f i)) R∧Disjoint (hubs i (f i)) B∧
        ∀ v∈rows i (f i),∀ w∈R,¬PermutationClose π b v w)∧
      ∀ i j,i≠j→Disjoint (rows i (f i)) (rows j (f j))∧Disjoint (hubs i (f i)) (hubs j (f j))∧
        ∀ v∈rows i (f i),∀ w∈rows j (f j),¬PermutationClose π b v w:=by
  have hinit:∀ i,Nonempty (C i):=by
    intro i
    obtain ⟨c,_⟩:=hchoose R B (by rfl) (by rfl) (by omega) (by omega) i
    exact ⟨c⟩
  let f₀:∀ i,C i:=fun i=>Classical.choice (hinit i)
  have hh:∀ R':Finset V,∀ B':Finset U,R⊆R'→B⊆B'→
      R'.card≤R.card+Fintype.card I*q→B'.card≤B.card+Fintype.card I*t→∀ i:I,
      ∃ f:∀ i,C i,Good i (f i)∧(rows i (f i)).card≤q∧(hubs i (f i)).card≤t∧
        Disjoint (rows i (f i)) R'∧Disjoint (hubs i (f i)) B'∧
        ∀ v∈rows i (f i),∀ w∈R',¬PermutationClose π b v w:=by
    intro R' B' hR hB hr hb i
    obtain ⟨c,hc⟩:=hchoose R' B' hR hB hr hb i
    exact ⟨Function.update f₀ i c,by simpa only [Function.update_self] using hc⟩
  obtain ⟨f,hf,hd⟩:=finite_separated_row_hub_choices π b
    (fun i (f:∀ i,C i)=>rows i (f i)) (fun i (f:∀ i,C i)=>hubs i (f i))
    (fun i (f:∀ i,C i)=>Good i (f i)) R B q t hh
  exact ⟨fun i=>f i i,hf,hd⟩

end Oberwolfach
