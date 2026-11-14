module

public import Oberwolfach.OrdinaryVortexBufferedDomains
public import Oberwolfach.VortexSizeBounds

@[expose] public section
/-! A diagnostic for a particular conservative two-step parameter route.
The conclusion rules out the displayed sufficient inequalities, not the
underlying wheel construction or the theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_two_step_root_card_lower
    (P:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (hε:0<ε) (hm:0<m) (i:ℕ) (hi:i+2≤Q.length):
    (ε^2/4)*Fintype.card (markedVortexVertexType Q i)≤
      ((ordinaryVortexBufferedVertices Q i 2).card:ℝ):=by
  have h1:=(Q.consecutive_size_bounds hε hm (i:=i) (by omega)).1
  have h2:=(Q.consecutive_size_bounds hε hm (i:=i+1) (by omega)).1
  have hs:=mul_le_mul_of_nonneg_left h1 (show 0≤ε/2 by positivity)
  have ht:(ordinaryVortexBufferedVertices Q i 2).card=(Q.vertices (i+2)).card:=by
    have himg:=(ordinary_vortex_buffered_images Q i 2).1
    rw [←Q.extendedVertices_eq hi,←himg,Finset.card_image_of_injective _ (markedVortexVertexEmbedding Q i).injective]
  have hn:Fintype.card (markedVortexVertexType Q i)=(Q.vertices i).card:=by
    simp only [markedVortexVertexType,Fintype.card_coe,Q.extendedVertices_eq (by omega : i≤Q.length)]
  rw [ht,hn]
  nlinarith only [hs,h2]

theorem ordinary_two_step_conservative_rate_obstruction
    (ε root ell N p rate:ℝ) (hε:0<ε) (hN:0<N)
    (hroot:(ε^2/8)*N≤root) (hell:3*root≤ell)
    (hmatching:ell/N≤p/4) (hcost:4*p≤rate) (hrate:rate≤ε^2/384):False:=by
  have hmul:ell≤(p/4)*N:=(div_le_iff₀ hN).mp hmatching
  have hrateN:=mul_le_mul_of_nonneg_right hrate hN.le
  have hcostN:=mul_le_mul_of_nonneg_right hcost hN.le
  have hsquare:0<ε^2*N:=mul_pos (sq_pos_of_pos hε) hN
  nlinarith only [hroot,hell,hmul,hrateN,hcostN,hsquare]
end Oberwolfach
