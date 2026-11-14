module

public import Oberwolfach.EdgeAssignmentAvailableIndex
public import Oberwolfach.EdgeAssignmentUpdate

@[expose] public section
/-! Greedily assign each edge an allowed index, respecting pairwise
conflicts and per-index capacities. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E W:Type} [Fintype W] [Nonempty W] [DecidableEq E] [DecidableEq W]

theorem edge_assignment_greedy (S:Finset E) (L Bad:E→Finset W) (C:E→E→Prop)
    (hsym:∀x y,C x y→C y x) (K:ℕ) (hK:0<K)
    (hbudget:∀ e∈S,(Bad e).card+((S.filter (C e)).card:ℝ)+(S.card:ℝ)/K<((L e).card:ℝ)):
    ∃f:E→W,
      (∀e∈S,f e∈L e ∧ f e∉Bad e) ∧
      (∀e∈S,∀e'∈S,e≠e'→C e e'→f e≠f e') ∧
      (∀w,(S.filter (fun e=>f e=w)).card≤K) := by
  have hconstruct:∀T:Finset E,T⊆S→∃f:E→W,
      (∀e∈T,f e∈L e ∧ f e∉Bad e) ∧
      (∀e∈T,∀e'∈T,e≠e'→C e e'→f e≠f e') ∧
      (∀w,(T.filter (fun e=>f e=w)).card≤K) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro hsub
      refine ⟨fun _=>Classical.choice inferInstance,?_,?_,?_⟩
      · simp
      · simp
      · simp
    | @insert e T he ih =>
      intro hsub
      have heS:e∈S:=hsub (Finset.mem_insert_self _ _)
      have hTS:T⊆S:=fun x hx=>hsub (Finset.mem_insert_of_mem hx)
      obtain ⟨f,hallowed,hconf,hcap⟩:=ih hTS
      obtain ⟨w,hw,hwb,hwconf,hwcap⟩:=edge_assignment_available_index S T hTS f e (L e) (Bad e) (C e) K hK (hbudget e heS)
      obtain ⟨ha,hc,hcapa,_⟩:=edge_assignment_update T f e he L Bad C hsym K hallowed hconf hcap w hw hwb hwconf hwcap
      exact ⟨Function.update f e w,ha,hc,hcapa⟩
  exact hconstruct S (Finset.Subset.refl _)
end Oberwolfach
