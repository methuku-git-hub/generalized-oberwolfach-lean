module

public import Oberwolfach.MarkedFixedVortexNeighbourTransport
public import Oberwolfach.MarkedFixedVortexSizes
public import Oberwolfach.VortexMarkedParentDegrees

@[expose] public section
/-! The original vortex estimates supply the exact minimum-degree and
near-regularity inputs into each fixed inner domain, including external roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε α:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_fixed_inner_degree_fields
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(1/2+α)*Fintype.card V≤(D:ℝ)) (hα:0<α)
    (hρ:0 < initialIndexDensity U D) (hb:0≤β) (hbα:β≤α/8) (hb1:β≤1/4) (he:0<ε) (hm:0<m)
    (i:ℕ) (hi:i<Q.length):
    let W:=markedVortexVertexType Q i
    let I:=markedVortexInnerVertices Q i
    let J:=markedVortexInnerHubs Q i
    let Dbal:=2*(J.card:ℝ)/initialIndexDensity U D
    (∀ x:W,(1/2+α/2)*(I.card:ℝ)≤
      (((G.comap (markedVortexVertexEmbedding Q i)).neighborFinset x∩I).card:ℝ)) ∧
    (∀ x:W,|(((G.comap (markedVortexVertexEmbedding Q i)).neighborFinset x∩I).card:ℝ)-Dbal|≤β*I.card) ∧
    ((I.card:ℝ)/2≤Dbal) ∧ (Dbal≤2*I.card):=by
  intro W I J Dbal
  obtain ⟨hI,_,hJ,_⟩:=marked_vortex_inner_cardinalities Q i
  have hI':I.card=(Q.vertices (i+1)).card:=by
    rw [hI,Q.extendedVertices_eq (by omega : i+1≤Q.length)]
  have hJ':J.card=(Q.indices (i+1)).card:=by
    rw [hJ,Q.extendedIndices_eq (by omega : i+1≤Q.length)]
  have hfields (x:W):=(Q.marked_parent_degrees hreg hn hD hα hρ hb hbα hb1
    (by omega : i+1≤Q.length) x.val (by
      have hx:=Q.extendedVertices_subset (show (i+1)-2 ≤ i by omega) x.property
      rw [Q.extendedVertices_eq (by omega : (i+1)-2≤Q.length)] at hx
      exact hx))
  have hcount (x:W):(((G.comap (markedVortexVertexEmbedding Q i)).neighborFinset x∩I).card:ℝ)=
      ((G.neighborFinset x.val∩Q.vertices (i+1)).card:ℝ):=by
    rw [marked_vortex_inner_neighbour_card,Q.extendedVertices_eq (by omega : i+1≤Q.length)]
  constructor
  · intro x
    rw [hcount x,hI']
    exact (hfields x).2.2.1
  constructor
  · intro x
    dsimp [Dbal]
    rw [hcount x,hI',hJ']
    exact (hfields x).2.2.2
  have hex:Nonempty W:=by
    have hpos:0<(Q.vertices i).card:=by
      have hp:=Q.vertices_lower (i:=i) hi.le
      have hmpos:(0:ℝ)<(Q.vertices i).card:=by
        have hmR:(0:ℝ)<m:=by exact_mod_cast hm
        have hεm:0<ε*(m:ℝ)/2:=by positivity
        exact hεm.trans_le hp
      exact_mod_cast hmpos
    exact Fintype.card_pos_iff.mp (by simpa [W,markedVortexVertexType,Q.extendedVertices_eq hi.le,Fintype.card_coe] using hpos)
  let x:W:=Classical.choice hex
  dsimp [Dbal]
  rw [hI',hJ']
  exact ⟨(hfields x).1,(hfields x).2.1⟩
end Oberwolfach
