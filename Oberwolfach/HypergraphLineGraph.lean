module

public import Oberwolfach.JointColourRetention
public import Oberwolfach.HypergraphWeightMoments

@[expose] public section

/-! The line graph retains hyperedge identifiers, including parallel
hyperedges. Cliques and overlap bounds are derived from resource sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def hypergraphLineGraph {V E : Type*} (R : E → Finset V) : SimpleGraph E where
  Adj e f := e≠f ∧ ¬Disjoint (R e) (R f)
  symm := ⟨fun e f h=>⟨Ne.symm h.1,fun hd=>h.2 hd.symm⟩⟩
  loopless := ⟨fun e h=>h.1 rfl⟩

def hypergraphVertexClique {V E : Type*} [Fintype E]
    (R : E → Finset V) (v : V) : Finset E :=
  Finset.univ.filter (fun e=>v∈R e)

theorem hypergraphVertexClique_isClique {V E : Type*} [Fintype E]
    (R : E → Finset V) (v : V) :
    ∀ e∈hypergraphVertexClique R v,∀ f∈hypergraphVertexClique R v,
      e≠f → (hypergraphLineGraph R).Adj e f := by
  intro e he f hf hne
  refine ⟨hne,?_⟩
  intro hd
  exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2

theorem hypergraphLineGraph_degree_bound
    {V E : Type*} [Fintype E] [DecidableEq E] (R : E → Finset V)
    {k D : ℕ} (hsize : ∀ e,(R e).card≤k)
    (hdegree : ∀ v,(hypergraphVertexClique R v).card≤D) (e : E) :
    (Finset.univ.filter (fun f=>(hypergraphLineGraph R).Adj e f)).card≤k*D := by
  classical
  have hsub : Finset.univ.filter (fun f=>(hypergraphLineGraph R).Adj e f)⊆
      (R e).biUnion (hypergraphVertexClique R) := by
    intro f hf
    obtain ⟨_,hdis⟩ := (Finset.mem_filter.mp hf).2
    obtain ⟨v,hve,hvf⟩ := Finset.not_disjoint_iff.mp hdis
    exact Finset.mem_biUnion.mpr ⟨v,hve,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvf⟩⟩
  calc
    _ ≤ ((R e).biUnion (hypergraphVertexClique R)).card := Finset.card_le_card hsub
    _ ≤ (R e).card*D := Finset.card_biUnion_le_card_mul _ _ _ (fun v _=>hdegree v)
    _ ≤ _ := Nat.mul_le_mul_right _ (hsize e)

theorem hypergraphLineGraph_common_neighbours
    {V E : Type*} [Fintype E] [DecidableEq E] (R : E → Finset V)
    {k B : ℕ} (hsize : ∀ e,(R e).card≤k)
    (hcodeg : ∀ v w,v≠w →
      (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (e f : E) (hdis : Disjoint (R e) (R f)) :
    (Finset.univ.filter (fun g=>(hypergraphLineGraph R).Adj e g ∧
      (hypergraphLineGraph R).Adj f g)).card≤k^2*B := by
  classical
  let A : V×V → Finset E := fun p=>Finset.univ.filter (fun g=>p.1∈R g ∧ p.2∈R g)
  have hsub : Finset.univ.filter (fun g=>(hypergraphLineGraph R).Adj e g ∧
      (hypergraphLineGraph R).Adj f g)⊆((R e)×ˢ(R f)).biUnion A := by
    intro g hg
    obtain ⟨hg₁,hg₂⟩ := (Finset.mem_filter.mp hg).2
    obtain ⟨v,hve,hvg⟩ := Finset.not_disjoint_iff.mp hg₁.2
    obtain ⟨w,hwf,hwg⟩ := Finset.not_disjoint_iff.mp hg₂.2
    exact Finset.mem_biUnion.mpr ⟨(v,w),Finset.mem_product.mpr ⟨hve,hwf⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvg,hwg⟩⟩
  have hA (p : V×V) (hp : p∈(R e)×ˢ(R f)) : (A p).card≤B := by
    apply hcodeg
    intro he
    exact Finset.disjoint_left.mp hdis (Finset.mem_product.mp hp).1
      (he ▸ (Finset.mem_product.mp hp).2)
  calc
    _ ≤ (((R e)×ˢ(R f)).biUnion A).card := Finset.card_le_card hsub
    _ ≤ ((R e)×ˢ(R f)).card*B := Finset.card_biUnion_le_card_mul _ _ _ hA
    _ = ((R e).card*(R f).card)*B := by rw [Finset.card_product]
    _ ≤ (k*k)*B := Nat.mul_le_mul_right _ (Nat.mul_le_mul (hsize e) (hsize f))
    _ = _ := by ring

theorem hypergraphVertexClique_intersection
    {V E : Type*} [Fintype E] [DecidableEq E] (R : E → Finset V) (v w : V) :
    hypergraphVertexClique R v∩hypergraphVertexClique R w=
      Finset.univ.filter (fun e=>v∈R e ∧ w∈R e) := by
  ext e
  simp [hypergraphVertexClique]

end Oberwolfach
