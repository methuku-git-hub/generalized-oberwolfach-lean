module

public import Oberwolfach.MarkedFixedVortexParentDegrees

@[expose] public section
/-! Full-parent degree fields for the actual fixed vortex subtypes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε α:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_fixed_parent_degree_fields_including_terminal
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(1/2+α)*Fintype.card V≤(D:ℝ)) (hα:0<α)
    (hρ:0 < initialIndexDensity U D) (hb:0≤β) (hbα:β≤α/8) (hb1:β≤1/4) (he:0<ε) (hm:0<m)
    (i:ℕ) (hi:i≤Q.length):
    let W:=markedVortexVertexType Q i
    let Z:=markedVortexHubType Q i
    let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D
    (∀ x:W,(1/2+α/2)*(Fintype.card W:ℝ)≤
      ((G.comap (markedVortexVertexEmbedding Q i)).degree x:ℝ)) ∧
    (∀ x:W,|((G.comap (markedVortexVertexEmbedding Q i)).degree x:ℝ)-Dload|≤β*Fintype.card W) ∧
    ((Fintype.card W:ℝ)/2≤Dload) ∧ (Dload≤2*Fintype.card W):=by
  intro W Z Dload
  have hW:Fintype.card W=(Q.vertices i).card:=by
    change Fintype.card (Q.extendedVertices i)=(Q.vertices i).card
    rw [Fintype.card_coe,Q.extendedVertices_eq hi]
  have hZ:Fintype.card Z=(Q.indices i).card:=by
    change Fintype.card (Q.extendedIndices i)=(Q.indices i).card
    rw [Fintype.card_coe,Q.extendedIndices_eq hi]
  let e:W↪V:=(markedVortexVertexEmbedding Q i).toEmbedding
  have he:Finset.univ.image e=Q.vertices i:=by
    rw [←Q.extendedVertices_eq hi]
    ext v
    constructor
    · intro hv
      obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hv
      exact x.property
    · intro hv
      exact Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩
  have hcount (x:W):((G.comap (markedVortexVertexEmbedding Q i)).degree x:ℝ)=
      ((G.neighborFinset x.val∩Q.vertices i).card:ℝ):=by
    have hh:=graph_comap_degree_into_image G e x
    rw [he] at hh
    exact_mod_cast hh
  have hfields (x:W):=Q.marked_parent_degrees hreg hn hD hα hρ hb hbα hb1 hi x.val (by
    have hx:=Q.extendedVertices_subset (show i-2 ≤ i by omega) x.property
    rw [Q.extendedVertices_eq (by omega : i-2≤Q.length)] at hx
    exact hx)
  constructor
  · intro x
    rw [hcount x,hW]
    exact (hfields x).2.2.1
  constructor
  · intro x
    dsimp [Dload]
    rw [hcount x,hW,hZ]
    exact (hfields x).2.2.2
  have hex:Nonempty W:=by
    have hpos:0<(Q.vertices i).card:=by
      have hp:=Q.vertices_lower (i:=i) hi
      have hmR:(0:ℝ)<m:=by exact_mod_cast hm
      have hεm:0<ε*(m:ℝ)/2:=by positivity
      exact_mod_cast hεm.trans_le hp
    exact Fintype.card_pos_iff.mp (by rw [hW];exact hpos)
  let x:W:=Classical.choice hex
  dsimp [Dload]
  rw [hW,hZ]
  exact ⟨(hfields x).1,(hfields x).2.1⟩
end Oberwolfach
