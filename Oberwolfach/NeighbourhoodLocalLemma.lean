module

public import Oberwolfach.NibbleCoordinateSupports
public import Oberwolfach.CoordinateLocalLemmaDegree

@[expose] public section

/-! A common event for quantities determined within two graph steps of
fixed finite sets. Both support size and coordinate incidence are computed
from the graph degree and the original family of sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem closedSetNeighbours_mem_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (v : V) :
    v∈closedSetNeighbours G S ↔ ∃ u∈S,u=v ∨ G.Adj u v := by
  simp only [closedSetNeighbours,Finset.mem_union,setNeighbours,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro (hv|⟨u,hu,huv⟩)
    · exact ⟨v,hv,Or.inl rfl⟩
    · exact ⟨u,hu,Or.inr huv⟩
  · rintro ⟨u,hu,h⟩
    rcases h with rfl|h
    · exact Or.inl hu
    · exact Or.inr ⟨u,hu,h⟩

theorem closedSetNeighbours_incidence
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) (S : I → Finset V) {d b : ℕ}
    (hdegree : ∀ v,(Finset.univ.filter (fun u=>G.Adj v u)).card≤d)
    (hinc : ∀ v,(Finset.univ.filter (fun i=>v∈S i)).card≤b) (v : V) :
    (Finset.univ.filter (fun i=>v∈closedSetNeighbours G (S i))).card≤b*(d+1) := by
  classical
  have hsub : Finset.univ.filter (fun i=>v∈closedSetNeighbours G (S i))⊆
      (closedSetNeighbours G {v}).biUnion (fun u=>Finset.univ.filter (fun i=>u∈S i)) := by
    intro i hi
    obtain ⟨u,hu,huv⟩ := (closedSetNeighbours_mem_iff G (S i) v).mp (Finset.mem_filter.mp hi).2
    apply Finset.mem_biUnion.mpr
    refine ⟨u,(closedSetNeighbours_mem_iff G {v} u).mpr ⟨v,by simp,?_⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩⟩
    exact huv.elim (fun h=>Or.inl h.symm) (fun h=>Or.inr h.symm)
  calc
    _ ≤ ((closedSetNeighbours G {v}).biUnion (fun u=>Finset.univ.filter (fun i=>u∈S i))).card :=
      Finset.card_le_card hsub
    _ ≤ (closedSetNeighbours G {v}).card*b :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun u _=>hinc u)
    _ ≤ (d+1)*b := Nat.mul_le_mul_right _ (by
      simpa only [Finset.card_singleton,one_mul] using closedSetNeighbours_card_le G hdegree {v})
    _ = _ := Nat.mul_comm _ _

theorem finiteLaw_neighbourhood_localLemma
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    {X : V → Type*} [∀ v,Fintype (X v)]
    (G : SimpleGraph V) (μ : ∀ v,FiniteLaw (X v))
    (A : I → (∀ v,X v) → Prop) (S : I → Finset V)
    {d a b : ℕ} (ha : 0<a) (hb : 0<b)
    (hdegree : ∀ v,(Finset.univ.filter (fun u=>G.Adj v u)).card≤d)
    (hsize : ∀ i,(S i).card≤a)
    (hinc : ∀ v,(Finset.univ.filter (fun i=>v∈S i)).card≤b)
    (hs : ∀ i σ τ,(∀ v∈closedSetNeighbours G (closedSetNeighbours G (S i)),σ v=τ v) →
      (A i σ ↔ A i τ))
    (hp : ∀ i,(FiniteLaw.pi μ).probability (A i)≤1/(4*((a*b*(d+1)^4 : ℕ) : ℝ))) :
    ∃ σ,0<(FiniteLaw.pi μ).mass σ ∧ ∀ i,¬A i σ := by
  have hsize' (i : I) : (closedSetNeighbours G (closedSetNeighbours G (S i))).card≤a*(d+1)^2 := by
    calc
      _ ≤ (closedSetNeighbours G (S i)).card*(d+1) := closedSetNeighbours_card_le G hdegree _
      _ ≤ ((S i).card*(d+1))*(d+1) := Nat.mul_le_mul_right _ (closedSetNeighbours_card_le G hdegree _)
      _ ≤ (a*(d+1))*(d+1) := by gcongr;exact hsize i
      _ = _ := by ring
  have hinc' (v : V) :
      (Finset.univ.filter (fun i=>v∈closedSetNeighbours G (closedSetNeighbours G (S i)))).card≤b*(d+1)^2 := by
    have h := closedSetNeighbours_incidence G (fun i=>closedSetNeighbours G (S i)) hdegree
      (closedSetNeighbours_incidence G S hdegree hinc) v
    convert h using 1 <;> ring
  apply finiteLaw_coordinate_localLemma_degree μ A
    (fun i=>closedSetNeighbours G (closedSetNeighbours G (S i))) hs
    (by positivity : 0<a*(d+1)^2) (by positivity : 0<b*(d+1)^2) hsize' hinc'
  intro i
  convert hp i using 1 <;> push_cast <;> ring

end Oberwolfach
