module

public import Oberwolfach.MarkedVortexNonDeeperGeometry
public import Oberwolfach.MarkedFixedVortexSizes

@[expose] public section
/-! Lower bounds on the inner and next-active vertex domains in terms of the
parent vertex count, using the vortex's actual consecutive-size bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_inner_active_size_inputs
    (he:0<ε) (hehalf:ε≤1/2) (hm:0<m) (iota:ℝ) (hiota:0 ≤ iota)
    (hiotacap:iota≤ε/2) (L:ℕ) (hL:L<Q.length):
    ∀ i≤L,
      let W:=markedVortexVertexType Q i
      let I:=markedVortexInnerVertices Q i
      let A:=↥((Finset.univ\markedVortexInnerVertices Q (i+1)):
        Finset (markedVortexVertexType Q (i+1)))
      iota*Fintype.card W≤(I.card:ℝ) ∧ iota*Fintype.card W/4≤(Fintype.card A:ℝ):=by
  intro i hi W I A
  have hinner:=marked_vortex_inner_cardinalities Q i
  have hI:I.card=(Q.vertices (i+1)).card:=by
    rw [hinner.1,Q.extendedVertices_eq (by omega:i+1≤Q.length)]
  have hW:Fintype.card W=(Q.vertices i).card:=by
    change Fintype.card ↥(Q.extendedVertices i)=(Q.vertices i).card
    rw [Fintype.card_coe,Q.extendedVertices_eq (by omega:i≤Q.length)]
  have hstep:= (Q.consecutive_size_bounds he hm (i:=i) (by omega:i<Q.length)).1
  have hIlo:(ε/2)*Fintype.card W≤(I.card:ℝ):=by rw [hI,hW];linarith
  have hlo:iota*Fintype.card W≤(I.card:ℝ):=
    (mul_le_mul_of_nonneg_right hiotacap (Nat.cast_nonneg _)).trans hIlo
  let T:=markedVortexDeeperVertices Q i
  have hTi:T⊆I:=(marked_vortex_fixed_active_geometry Q he.le i).1
  have hT:(T.card:ℝ)≤ε*I.card:=(marked_vortex_fixed_active_geometry Q he.le i).2.2.1
  have hA:Fintype.card A=(I\T).card:=by
    have himage:=marked_vortex_next_active_parent_image Q i
    rw [←himage,Finset.card_image_of_injective _ (by
      intro x y hxy
      exact (markedVortexNextActiveInNonDeeper Q i).injective
        ((markedVortexNonDeeperVertexEmbedding Q i).injective hxy))]
    simp only [Finset.card_univ]
    rfl
  have hAreal:(Fintype.card A:ℝ)=(I.card:ℝ)-T.card:=by
    rw [hA,Finset.card_sdiff,Finset.inter_eq_left.mpr hTi,Nat.cast_sub (Finset.card_le_card hTi)]
  refine ⟨hlo,?_⟩
  rw [hAreal]
  have hI0:(0:ℝ)≤I.card:=Nat.cast_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.mpr hehalf) hI0]
end Oberwolfach
