module

public import Oberwolfach.OrdinaryVortexNamedNondeeperLocalInputs

@[expose] public section
/-! Assemble the fixed all-level nondeeper host inputs before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

structure OrdinaryNondeeperTriangleLocalInputs
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D vsize d:ℕ) (β ε ρ₀ θ α εTri pR pH:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V) (i:ℕ)
    (πA:Equiv.Perm (ordinaryVortexNondeeperVertexType Q i)):Prop where
  perm_commutes:∀x,(πA x).val=π x.val
  min_degree:∀x,(θ+α)*Fintype.card (ordinaryVortexNondeeperVertexType Q i)≤
    ((P.induce ((ordinaryVortexNondeeperVertexSet Q i):Set V)).degree x:ℝ)
  approximate_regular:∀x,|((P.induce ((ordinaryVortexNondeeperVertexSet Q i):Set V)).degree x:ℝ)-
    2*((ordinaryVortexNondeeperHubSet Q i).card:ℝ)/initialIndexDensity U D|≤
      εTri*Fintype.card (ordinaryVortexNondeeperVertexType Q i)
  mean_lower:(Fintype.card (ordinaryVortexNondeeperVertexType Q i):ℝ)/2≤
    2*((ordinaryVortexNondeeperHubSet Q i).card:ℝ)/initialIndexDensity U D
  hub_lower:(ρ₀/4)*Fintype.card (ordinaryVortexNondeeperVertexType Q i)≤
    (Fintype.card (ordinaryVortexNondeeperHubType Q i):ℝ)
  hub_upper:Fintype.card (ordinaryVortexNondeeperHubType Q i)≤Fintype.card (ordinaryVortexNondeeperVertexType Q i)
  balance_mean:pR*(2*((ordinaryVortexNondeeperHubSet Q i).card:ℝ)/initialIndexDensity U D)=
    2*(Fintype.card (ordinaryVortexNondeeperHubType Q i):ℝ)*pH
  conflict_restriction:(permutationConflictGraph π (3*d)).comap (ordinaryVortexNondeeperVertexEmbedding Q i)=
    permutationConflictGraph πA (3*d)
  conflict_degree:∀x,(permutationConflictGraph πA (3*d)).degree x≤2*(3*d)
  no_short:∀x l,0<l→l<2*d+1→(πA^l) x≠x

theorem ordinary_vortex_nondeeper_triangle_inputs
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D vsize d:ℕ) (β ε ρ₀ θ α εTri pR pH:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V) (hDlo:(Fintype.card V:ℝ)/2≤D)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hβα:β≤3*(2*α)/20) (hβε:(5/3)*β≤εTri)
    (hε:0<ε) (hε1:ε≤1/4) (hv:0<vsize) (hθ:1/2≤θ) (hα:0<α)
    (hdegree:(θ+2*α)*Fintype.card V≤D) (hp:pR=initialIndexDensity U D*pH)
    (hshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (L M:ℕ) (hL:L+2≤Q.length) (hM:(M:ℝ)≤3*ε*vsize/8):
    ∃πA:∀i,Equiv.Perm (ordinaryVortexNondeeperVertexType Q i),
      (∀i≤L,OrdinaryNondeeperTriangleLocalInputs P D vsize d β ε ρ₀ θ α εTri pR pH Q π i (πA i)) ∧
      (∀i≤L,M≤Fintype.card (ordinaryVortexNondeeperVertexType Q i)) ∧
      (∀i<L,(Fintype.card (ordinaryVortexNondeeperVertexType Q (i+1)):ℝ)≤
        (2*ε)*Fintype.card (ordinaryVortexNondeeperVertexType Q i)) :=by
  have hlocal:∀i≤L,∃πA:Equiv.Perm (ordinaryVortexNondeeperVertexType Q i),
      OrdinaryNondeeperTriangleLocalInputs P D vsize d β ε ρ₀ θ α εTri pR pH Q π i πA:=by
    intro i hi
    have h:=ordinary_vortex_named_nondeeper_local_inputs P D vsize d β ε ρ₀ θ (2*α) Q π hpres hreg hn hDlo
      hρ₀ hρlo hρhi hβ hβ1 hβα hε hε1 hv hθ (by positivity) hdegree hshort i (by omega)
    obtain ⟨πA,hperm,hmin,hnear,hmean,hUlo,hUhi,hbal,hconf,hcdeg,hshortA⟩:=h
    refine ⟨πA,⟨hperm,?_,?_,hmean,hUlo,hUhi,hbal pR pH hp,?_,hcdeg,hshortA⟩⟩
    · intro x
      have hh:=hmin x
      nlinarith only [hh]
    · intro x
      have hh:=mul_le_mul_of_nonneg_right hβε (show (0:ℝ)≤Fintype.card (ordinaryVortexNondeeperVertexType Q i) by positivity)
      exact (hnear x).trans hh
    · exact hconf
  let πA:∀i,Equiv.Perm (ordinaryVortexNondeeperVertexType Q i):=
    fun i=>if hi:i≤L then Classical.choose (hlocal i hi) else Equiv.refl _
  refine ⟨πA,?_,?_,?_⟩
  · intro i hi
    simpa only [πA,dif_pos hi] using Classical.choose_spec (hlocal i hi)
  · intro i hi
    have hh:=(ordinary_vortex_nondeeper_domain_sizes Q ρ₀ hreg hn hDlo hρ₀ hρlo hβ hβ1 hε hε1 i (by omega)).1
    have hreal:(M:ℝ)≤Fintype.card (ordinaryVortexNondeeperVertexType Q i):=by
      simpa only [ordinaryVortexNondeeperVertexType,Fintype.card_coe] using hM.trans hh
    exact_mod_cast hreal
  · intro i hi
    have hh:=(ordinary_vortex_nondeeper_domain_sizes Q ρ₀ hreg hn hDlo hρ₀ hρlo hβ hβ1 hε hε1 i (by omega)).2.2.1
    simpa only [ordinaryVortexNondeeperVertexType,Fintype.card_coe] using hh
end Oberwolfach
