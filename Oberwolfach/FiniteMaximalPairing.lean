module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Order.Preorder.Finite

@[expose] public section

/-! A finite maximal matching, represented by a partial involution.
Its unmatched vertices form an independent set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_maximal_matching_on
    {V : Type*} [Fintype V] (G : SimpleGraph V) (D : Finset V) :
    ∃ M : G.Subgraph,M.IsMatching ∧ M.verts⊆(D : Set V) ∧
      ∀ u∈D,∀ v∈D,u∉M.verts → v∉M.verts → ¬G.Adj u v := by
  classical
  let P : G.Subgraph → Prop := fun M=>M.IsMatching ∧ M.verts⊆(D : Set V)
  have hbot : P ⊥ := by
    constructor
    · intro v hv
      exact False.elim hv
    · intro v hv
      exact False.elim hv
  obtain ⟨M,_,hmax⟩ := Finite.exists_le_maximal hbot
  refine ⟨M,hmax.1.1,hmax.1.2,?_⟩
  intro u hu v hv hmu hmv huv
  let E := G.subgraphOfAdj huv
  have hE : E.IsMatching := SimpleGraph.Subgraph.IsMatching.subgraphOfAdj huv
  have hdis : Disjoint M.support E.support := by
    apply Set.disjoint_left.mpr
    intro w hw hwe
    have hwM := M.support_subset_verts hw
    have hwE := E.support_subset_verts hwe
    change w∈({u,v} : Set V) at hwE
    rcases hwE with rfl|rfl
    · exact hmu hwM
    · exact hmv hwM
  have hnew : P (M⊔E) := by
    refine ⟨hmax.1.1.sup hE hdis,?_⟩
    intro w hw
    change w∈M.verts∪({u,v} : Set V) at hw
    rcases hw with hw|hw
    · exact hmax.1.2 hw
    · rcases hw with rfl|rfl
      · exact hu
      · exact hv
  have hle : M⊔E≤M := hmax.2 hnew le_sup_left
  have huE : u∈E.verts := by change u∈({u,v} : Set V);simp
  have huNew : u∈(M⊔E).verts := Or.inr huE
  exact hmu (hle.1 huNew)

theorem finite_maximal_pairing
    {V : Type*} [Fintype V] (G : SimpleGraph V) (D : Finset V) :
    ∃ m : V → Option V,
      (∀ u v,m u=some v → u∈D ∧ v∈D ∧ G.Adj u v ∧ m v=some u) ∧
      (∀ u∈D,∀ v∈D,m u=none → m v=none → ¬G.Adj u v) := by
  classical
  obtain ⟨M,hM,hD,hind⟩ := finite_maximal_matching_on G D
  let m : V → Option V := fun v=>if hv : v∈M.verts then some ((hM hv).choose) else none
  have hnone (v : V) (hv : m v=none) : v∉M.verts := by
    intro hvm
    simp [m,hvm] at hv
  refine ⟨m,?_,fun u hu v hv hmu hmv=>hind u hu v hv (hnone u hmu) (hnone v hmv)⟩
  intro u v huv
  by_cases hu : u∈M.verts
  · have hvchoice : (hM hu).choose=v := by simpa [m,hu] using huv
    have hadj : M.Adj u v := hvchoice ▸ (hM hu).choose_spec.1
    have hv : v∈M.verts := hadj.snd_mem
    refine ⟨hD hu,hD hv,M.adj_sub hadj,?_⟩
    have huchoice : (hM hv).choose=u :=
      hM.eq_of_adj_left (hM hv).choose_spec.1 hadj.symm
    simp [m,hv,huchoice]
  · simp [m,hu] at huv

end Oberwolfach
