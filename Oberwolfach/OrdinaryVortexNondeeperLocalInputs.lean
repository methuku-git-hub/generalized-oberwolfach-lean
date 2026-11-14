module

public import Oberwolfach.OrdinaryVortexNondeeperHostGeometry
public import Oberwolfach.OrdinaryFixedVortexConflict
public import Oberwolfach.InvariantPermutation
public import Oberwolfach.PermutationConflictDegree

@[expose] public section
/-! The local nondeeper host retains the fixed permutation and all degree,
size, mean and conflict inputs needed by the triangle event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_nondeeper_local_inputs
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D vsize d:ℕ) (β ε ρ₀ θ α:ℝ) (Q:Vortex U P D β ε vsize)
    (π:Equiv.Perm V) (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V) (hDlo:(Fintype.card V:ℝ)/2≤D)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hβα:β≤3*α/20) (hε:0<ε) (hε1:ε≤1/4)
    (hv:0<vsize) (hθ:1/2≤θ) (hα:0<α) (hdegree:(θ+α)*Fintype.card V≤D)
    (hshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (i:ℕ) (hi:i+2≤Q.length):
    let A:=Q.vertices i\Q.vertices (i+2)
    let B:=Q.indices i\Q.indices (i+2)
    let ρ:=initialIndexDensity U D
    let Dlocal:=2*(B.card:ℝ)/ρ;
    ∃πA:Equiv.Perm A,
      (∀x:A,(πA x).val=π x.val) ∧
      (∀x:A,(θ+α/2)*Fintype.card A≤((P.induce (A:Set V)).degree x:ℝ)) ∧
      (∀x:A,|((P.induce (A:Set V)).degree x:ℝ)-Dlocal|≤(5/3:ℝ)*β*Fintype.card A) ∧
      (Fintype.card A:ℝ)/2≤Dlocal ∧ (ρ₀/4)*Fintype.card A≤(Fintype.card B:ℝ) ∧
      Fintype.card B≤Fintype.card A ∧
      (∀pR pH:ℝ,pR=ρ*pH→pR*Dlocal=2*Fintype.card B*pH) ∧
      ((permutationConflictGraph π (3*d)).comap (Function.Embedding.subtype (·∈(A:Set V)))=permutationConflictGraph πA (3*d)) ∧
      (∀x:A,(permutationConflictGraph πA (3*d)).degree x≤2*(3*d)) ∧
      ∀x:A,∀l,0<l→l<2*d+1→(πA^l) x≠x :=by
  intro A B ρ Dlocal
  have hA:∀x,π x∈(A:Set V)↔x∈(A:Set V):=by
    intro x
    have h₁:=hpres i x
    have h₂:=hpres (i+2) x
    rw [Q.extendedVertices_eq (by omega)] at h₁
    rw [Q.extendedVertices_eq hi] at h₂
    simp only [A,Finset.mem_coe,Finset.mem_sdiff]
    exact and_congr h₁ (not_congr h₂)
  let πA:=invariantSetPermutation π (A:Set V) hA
  have hgeom:=ordinary_vortex_nondeeper_host_geometry P D vsize β ε ρ₀ θ α Q hreg hn hDlo hρ₀ hρlo hρhi
    hβ hβ1 hβα hε hε1 hv hθ hα hdegree i hi
  have hconf:(permutationConflictGraph π (3*d)).comap (Function.Embedding.subtype (·∈(A:Set V)))=permutationConflictGraph πA (3*d):=by
    let f:A↪V:=Function.Embedding.subtype (·∈(A:Set V))
    have hcomm:∀x,f (πA x)=π (f x):=fun _=>rfl
    ext x y
    change (f x≠f y ∧ PermutationClose π (3*d) (f x) (f y)) ↔
      (x≠y ∧ PermutationClose πA (3*d) x y)
    rw [f.injective.ne_iff,permutationClose_embedding f π πA hcomm f.injective]
  refine ⟨πA,(fun _=>rfl),hgeom.1,hgeom.2.1,hgeom.2.2.1,hgeom.2.2.2.1,hgeom.2.2.2.2.1,hgeom.2.2.2.2.2,hconf,?_,?_⟩
  · intro x
    exact permutationConflictGraph_degree_le πA (3*d) x
  · intro x l hl hl'
    exact invariantSetPermutation_noshort π (A:Set V) hA (2*d+1) hshort x l hl hl'
end Oberwolfach
