module

public import Oberwolfach.ResourceDecompositions

@[expose] public section

/-! Finite iteration with a different state type at each level. All
resource sets are compared in one ambient ground set; no identification of
local vertex types or of local coefficient functions is made. The step
constructor is an explicit premise of this algebraic lemma and must be
supplied by the graph-specific cover-down theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E W:Type} [DecidableEq E] [DecidableEq W]

theorem reindexed_resource_iteration
    (R:W → Finset E) (State:ℕ → Type) (B:∀ i,State i → Finset E)
    (Good:∀ i,State i → Prop) (L:ℕ)
    (step:∀ i<L,∀ s:State i,Good i s →
      ∃ t:State (i+1),Good (i+1) t ∧ B (i+1) t⊆B i s ∧
        HasResourceDecomposition R (B i s\B (i+1) t))
    (s:State 0) (hs:Good 0 s) :
    ∃ t:State L,Good L t ∧ B L t⊆B 0 s ∧
      HasResourceDecomposition R (B 0 s\B L t) := by
  induction L with
  | zero=>
    exact ⟨s,hs,Finset.Subset.refl _,by simpa using resource_decomposition_empty R⟩
  | succ L ih=>
    obtain ⟨t,ht,htB,hdec⟩:=ih (fun i hi=>step i (by omega))
    obtain ⟨u,hu,huB,hnext⟩:=step L (by omega) t ht
    refine ⟨u,hu,huB.trans htB,?_⟩
    have hd:Disjoint (B 0 s\B L t) (B L t\B (L+1) u):=
      Finset.disjoint_left.mpr (fun _ h h'=> (Finset.mem_sdiff.mp h).2 (Finset.mem_sdiff.mp h').1)
    have hwhole:=resource_decomposition_union R _ _ hdec hnext hd
    have heq:(B 0 s\B L t)∪(B L t\B (L+1) u)=B 0 s\B (L+1) u:=by
      ext a
      have hbt:=fun ha=>htB (x:=a) ha
      have hbu:=fun ha=>huB (x:=a) ha
      simp only [Finset.mem_union,Finset.mem_sdiff]
      tauto
    rwa [heq] at hwhole

theorem reindexed_resource_iteration_absorption
    (R:W → Finset E) (State:ℕ → Type) (B:∀ i,State i → Finset E)
    (Good:∀ i,State i → Prop) (L:ℕ)
    (step:∀ i<L,∀ s:State i,Good i s →
      ∃ t:State (i+1),Good (i+1) t ∧ B (i+1) t⊆B i s ∧
        HasResourceDecomposition R (B i s\B (i+1) t))
    (s:State 0) (hs:Good 0 s) (A:Finset E) (hA:Disjoint A (B 0 s))
    (finish:∀ t:State L,Good L t → B L t⊆B 0 s → HasResourceDecomposition R (A∪B L t)) :
    HasResourceDecomposition R (A∪B 0 s) := by
  obtain ⟨t,ht,hB,hdec⟩:=reindexed_resource_iteration R State B Good L step s hs
  have hdis:Disjoint (B 0 s\B L t) (A∪B L t):=by
    apply Finset.disjoint_union_right.mpr
    exact ⟨hA.symm.mono_left Finset.sdiff_subset,
      Finset.disjoint_left.mpr (fun _ he hf=> (Finset.mem_sdiff.mp he).2 hf)⟩
  have hwhole:=resource_decomposition_union R _ _ hdec (finish t ht hB) hdis
  have heq:(B 0 s\B L t)∪(A∪B L t)=A∪B 0 s:=by
    ext a
    have hh:=fun ha=>hB (x:=a) ha
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  rwa [heq] at hwhole

end Oberwolfach
