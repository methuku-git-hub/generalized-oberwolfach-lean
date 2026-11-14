module

public import Oberwolfach.MarkedVortexActivePermutation
public import Oberwolfach.VortexMarkedParentDegrees
public import Oberwolfach.MarkedPhysicalDeletionRestriction

@[expose] public section
/-! The vortex's external-root degree estimates, expressed on the nested
active types used in cover-down. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [du:DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε α:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_active_degree_fields
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(1/2+α)*Fintype.card V≤(D:ℝ)) (hα:0<α)
    (hρ:0 < initialIndexDensity U D) (hb:0≤β) (hbα:β≤3*α/40) (hb1:β≤3/20)
    (he:0≤ε) (he1:ε≤1/4) (i:ℕ):
    let A:Finset (markedVortexVertexType Q i):=Finset.univ\markedVortexInnerVertices Q i
    let B:Finset (markedVortexHubType Q i):=Finset.univ\markedVortexInnerHubs Q i
    let Dactive:=2*(B.card:ℝ)/initialIndexDensity U D;
    ∀ x:↥A, ((A.card:ℝ)/2≤Dactive) ∧ (Dactive≤2*A.card) ∧
    ((1/2+α/2)*A.card≤((G.comap (markedVortexActiveVertexEmbedding Q i)).degree x:ℝ)) ∧
    (|((G.comap (markedVortexActiveVertexEmbedding Q i)).degree x:ℝ)-Dactive|≤(5/3)*β*A.card):=by
  intro ALocal BLocal Dactive x
  let W:=↥ALocal
  let Z:=↥BLocal
  let A:=Q.extendedVertices i\Q.extendedVertices (i+1)
  let B:=Q.extendedIndices i\Q.extendedIndices (i+1)
  let f:=markedVortexActiveVertexEquiv Q i
  let g:=markedVortexActiveHubEquiv Q i
  have hW:Fintype.card W=A.card:=by
    have hh:=Fintype.card_congr f
    change Fintype.card W=Fintype.card ↥A at hh
    simpa only [Fintype.card_coe] using hh
  have hZ:Fintype.card Z=B.card:=by
    have hh:=Fintype.card_congr g
    change Fintype.card Z=Fintype.card ↥B at hh
    simpa only [Fintype.card_coe] using hh
  letI : DecidableEq U:=Classical.decEq U
  have hx:x.val.val∈Q.extendedVertices (i+1-2):=by
    apply Q.extendedVertices_subset (show i+1-2 ≤ i by omega)
    exact x.val.property
  have hh:=Q.marked_difference_parent_degrees hreg hn hD hα hρ hb hbα hb1 he he1 (show i < i+1 by omega) x.val.val hx
  let e:W↪V:=(markedVortexActiveVertexEmbedding Q i).toEmbedding
  have he:Finset.univ.image e=A:=by
    ext v
    constructor
    · intro hv
      obtain ⟨y,_,rfl⟩:=Finset.mem_image.mp hv
      exact (f y).property
    · intro hv
      let y:W:=f.symm ⟨v,hv⟩
      refine Finset.mem_image.mpr ⟨y,Finset.mem_univ _,?_⟩
      have hy:=congrArg Subtype.val (f.apply_symm_apply ⟨v,hv⟩)
      exact hy
  have hcount:((G.comap (markedVortexActiveVertexEmbedding Q i)).degree x:ℝ)=
      ((G.neighborFinset x.val.val∩A).card:ℝ):=by
    have hc:=graph_comap_degree_into_image G e x
    rw [he] at hc
    exact_mod_cast hc
  have hAc:ALocal.card=A.card:=by simpa only [W,Fintype.card_coe] using hW
  have hBc:BLocal.card=B.card:=by simpa only [Z,Fintype.card_coe] using hZ
  dsimp [Dactive]
  rw [hAc,hBc]
  dsimp only at hh
  have hAe:(Q.extendedVertices i\Q.extendedVertices (i+1))=A:=by ext v;simp [A]
  have hBe:(Q.extendedIndices i\Q.extendedIndices (i+1))=B:=by ext v;simp [B]
  rw [hAe,hBe] at hh
  obtain ⟨h1,h2,h3,h4⟩:=hh
  rw [←hcount] at h3 h4
  exact ⟨h1,h2,h3,h4⟩
end Oberwolfach
