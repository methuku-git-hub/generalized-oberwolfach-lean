module

public import Oberwolfach.NeighbourColourWitnesses
public import Oberwolfach.FilteredConflictCertificates
public import Oberwolfach.HypergraphLocalIndependence

@[expose] public section

/-! Certificates for uncoloured roots with assignment/rejection conditions
in neighbouring cliques, including the actual hypergraph codegree bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def neighbourColourPredicate {V C J : Type*} (G : SimpleGraph V)
    (Q : V → Finset J) (T : J → Finset V) (c : C) (a b : ℕ)
    (v : V) (σ : V → C×Bool) : Prop :=
  a≤(assignedSetIndices (Q v) T σ c).card ∧
    b≤(rejectedSetIndices G (Q v) T σ c).card

def neighbourColourCount {V C J : Type*} (G : SimpleGraph V)
    (U : Finset V) (Q : V → Finset J) (T : J → Finset V) (c : C) (a b : ℕ)
    (σ : V → C×Bool) : ℝ :=
  (filteredCoinConflictSet G U (neighbourColourPredicate G Q T c a b) σ).card

theorem neighbourColourCount_certificate
    {V C J : Type*} [Fintype V] (G : SimpleGraph V) (U : Finset V)
    (hU : ∀ u∈U,∀ v∈U,u≠v → G.Adj u v)
    (Q : V → Finset J) (T : J → Finset V) {k d : ℕ}
    (hQ : ∀ v∈U,(Q v).card≤k)
    (hlocal : ∀ (w : V) (S : Finset V),(∀ v∈S,G.Adj w v) →
      (∀ u∈S,∀ v∈S,u≠v → ¬G.Adj u v) → S.card≤k)
    (hinc : ∀ w,(U.filter (fun v=>∃ j∈Q v,w∈T j)).card≤d)
    (c : C) (a b : ℕ) :
    HasCoordinateCertificateBound (neighbourColourCount G U Q T c a b)
      (2+(((k+3)*d : ℕ) : ℝ)) ((3+((3*k : ℕ) : ℝ))*(U.card : ℝ)) := by
  classical
  have hex (σ : V → C×Bool) := neighbour_colour_witnesses G U Q T hQ hlocal hinc σ c
  let W : (V → C×Bool) → V → Finset V := fun σ=>Classical.choose (hex σ)
  have hW (σ : V → C×Bool) := Classical.choose_spec (hex σ)
  apply filteredCoinConflict_certificate G U hU (neighbourColourPredicate G Q T c a b) W
    (k:=3*k) (c:=(((k+3)*d : ℕ) : ℝ))
  · intro σ v hv _hp
    exact (hW σ).1 v hv
  · intro σ i
    have hsub : U.filter (fun v=>neighbourColourPredicate G Q T c a b v σ ∧ i∈W σ v)⊆
        U.filter (fun v=>i∈W σ v) := by
      intro v hv
      obtain ⟨hvU,_hp,hi⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨hvU,hi⟩
    exact_mod_cast (Finset.card_le_card hsub).trans ((hW σ).2.1 i)
  · intro σ v hv hp τ he
    have hmono := (hW σ).2.2 v hv τ he
    exact ⟨hp.1.trans hmono.1,hp.2.trans hmono.2⟩

theorem hypergraph_neighbourColourCount_certificate
    {V E C : Type*} [Fintype E] [DecidableEq V] (R : E → Finset V)
    {k B : ℕ} (hsize : ∀ e,(R e).card≤k)
    (hcodeg : ∀ v w,v≠w →
      (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (z : V) (U : Finset E) (hU : ∀ e∈U,z∈R e)
    (c : C) (a b : ℕ) :
    HasCoordinateCertificateBound
      (neighbourColourCount (hypergraphLineGraph R) U (fun e=>(R e).erase z)
        (hypergraphVertexClique R) c a b)
      (2+(((k+3)*(k*B) : ℕ) : ℝ)) ((3+((3*k : ℕ) : ℝ))*(U.card : ℝ)) := by
  classical
  apply neighbourColourCount_certificate (k:=k) (d:=k*B)
  · intro e he f hf hne
    apply hypergraphVertexClique_isClique R z e ?_ f ?_ hne
    · simpa only [hypergraphVertexClique,Finset.mem_filter,Finset.mem_univ,true_and]
        using hU e he
    · simpa only [hypergraphVertexClique,Finset.mem_filter,Finset.mem_univ,true_and]
        using hU f hf
  · intro e _he
    exact (Finset.card_le_card (Finset.erase_subset _ _)).trans (hsize e)
  · intro w S hN hI
    exact (hypergraphLineGraph_independent_neighbours R w S hN hI).trans (hsize w)
  · intro w
    have hsub : U.filter (fun e=>∃ v∈(R e).erase z,w∈hypergraphVertexClique R v)⊆
        U.filter (fun e=>∃ v∈R e,v≠z ∧ v∈R w) := by
      intro e he
      obtain ⟨heU,v,hv,hvw⟩ := Finset.mem_filter.mp he
      have hvw' : v∈R w := by
        simpa only [hypergraphVertexClique,Finset.mem_filter,Finset.mem_univ,true_and] using hvw
      exact Finset.mem_filter.mpr ⟨heU,v,(Finset.mem_erase.mp hv).2,
        (Finset.mem_erase.mp hv).1,hvw'⟩
    exact (Finset.card_le_card hsub).trans
      (hypergraph_outside_clique_incidence R hsize hcodeg z U hU w)

end Oberwolfach
