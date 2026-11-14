module

public import Oberwolfach.VortexSamplingDomainSizes
public import Oberwolfach.InvariantPermutation

@[expose] public section
/-! Fixed nondeeper vertex and hub domains and their restricted permutation.
They are selected before the sample and shrink at a geometric rate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {P:SimpleGraph V} {D vsize:ℕ} {β ε:ℝ} (Q:Vortex U P D β ε vsize)

def ordinaryVortexNondeeperVertexSet (i:ℕ):Finset V:=
  Q.extendedVertices i\Q.extendedVertices (i+2)

def ordinaryVortexNondeeperHubSet (i:ℕ):Finset U:=
  Q.extendedIndices i\Q.extendedIndices (i+2)

abbrev ordinaryVortexNondeeperVertexType (i:ℕ):Type:=↥(ordinaryVortexNondeeperVertexSet Q i)
abbrev ordinaryVortexNondeeperHubType (i:ℕ):Type:=↥(ordinaryVortexNondeeperHubSet Q i)

def ordinaryVortexNondeeperVertexEmbedding (i:ℕ):ordinaryVortexNondeeperVertexType Q i↪V:=
  Function.Embedding.subtype _

def ordinaryVortexNondeeperHubEmbedding (i:ℕ):ordinaryVortexNondeeperHubType Q i↪U:=
  Function.Embedding.subtype _

theorem ordinary_vortex_nondeeper_invariant (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (i:ℕ):
    ∀x,π x∈(ordinaryVortexNondeeperVertexSet Q i:Set V)↔x∈(ordinaryVortexNondeeperVertexSet Q i:Set V) :=by
  intro x
  simp only [ordinaryVortexNondeeperVertexSet,Finset.mem_coe,Finset.mem_sdiff]
  exact and_congr (hpres i x) (not_congr (hpres (i+2) x))

def ordinaryVortexNondeeperPermutation (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (i:ℕ):
    Equiv.Perm (ordinaryVortexNondeeperVertexType Q i):=
  invariantSetPermutation π (ordinaryVortexNondeeperVertexSet Q i:Set V) (ordinary_vortex_nondeeper_invariant Q π hpres i)

theorem ordinary_vortex_nondeeper_permutation_apply (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (i:ℕ)
    (x:ordinaryVortexNondeeperVertexType Q i):
    (ordinaryVortexNondeeperPermutation Q π hpres i x).val=π x.val :=rfl

theorem ordinary_vortex_nondeeper_domain_sizes (ρ₀:ℝ)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D) (hβ:0≤β) (hβ1:β≤1/4)
    (hε:0<ε) (hε1:ε≤1/4) (i:ℕ) (hi:i≤Q.length):
    3*ε*vsize/8≤((ordinaryVortexNondeeperVertexSet Q i).card:ℝ) ∧
    3*ρ₀*ε*vsize/64≤((ordinaryVortexNondeeperHubSet Q i).card:ℝ) ∧
    ((ordinaryVortexNondeeperVertexSet Q (i+1)).card:ℝ)≤(2*ε)*(ordinaryVortexNondeeperVertexSet Q i).card ∧
    ((ordinaryVortexNondeeperHubSet Q (i+1)).card:ℝ)≤(2*ε)*(ordinaryVortexNondeeperHubSet Q i).card :=by
  have h:=Q.sampling_difference_sizes hreg hn hD hρ hρlo hβ hβ1 hε hε1 i 2 (by omega) hi
  refine ⟨h.1,?_,h.2.2.1,?_⟩
  · dsimp only [ordinaryVortexNondeeperHubSet]
    convert h.2.1 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · dsimp only [ordinaryVortexNondeeperHubSet]
    convert h.2.2.2.1 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
