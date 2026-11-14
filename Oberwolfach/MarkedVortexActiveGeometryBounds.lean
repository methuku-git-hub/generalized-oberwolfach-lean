module

public import Oberwolfach.VortexSizeBounds
public import Oberwolfach.DifferenceDomains
public import Oberwolfach.VortexProtectedGeometry

@[expose] public section
/-! Size, index density and successive-scale bounds on the physical active
rings of the actual vortex, with no rounding approximation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_active_geometry_bounds
    (ρ₀:ℝ) (hρ₀:0<ρ₀) (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρlo:ρ₀≤ initialIndexDensity U D)
    (hρhi:initialIndexDensity U D≤1) (hb:0≤β) (hb1:β≤1/4)
    (he:0≤ε) (he1:ε≤1/4) (i:ℕ) (hi:i≤Q.length):
    let A:=Q.extendedVertices i\Q.extendedVertices (i+1)
    let B:=Q.extendedIndices i\Q.extendedIndices (i+1)
    let Anext:=Q.extendedVertices (i+1)\Q.extendedVertices (i+2);
    ((3/4:ℝ)*(Q.extendedVertices i).card≤A.card) ∧
    ((3/4:ℝ)*(Q.extendedIndices i).card≤B.card) ∧
    ((3*ρ₀/32)*(A.card:ℝ)≤B.card) ∧
    ((B.card:ℝ)≤(2/3)*(A.card:ℝ)) ∧
    ((Anext.card:ℝ)≤(4*ε/3)*A.card) ∧
    ((3*ε*(m:ℝ)/8)≤A.card) ∧ ((9*ρ₀*ε*(m:ℝ)/256)≤B.card):=by
  intro A B Anext
  have hv:=Q.extendedVertices_subset (show i ≤ i+1 by omega)
  have hu:=Q.extendedIndices_subset (show i ≤ i+1 by omega)
  have hAv:((A.card:ℝ))=(Q.extendedVertices i).card-(Q.extendedVertices (i+1)).card:=real_card_sdiff hv
  have hBu:((B.card:ℝ))=(Q.extendedIndices i).card-(Q.extendedIndices (i+1)).card:=real_card_sdiff hu
  have hstep:=Q.extended_successor_size_bounds he i
  have hV0:(0:ℝ)≤(Q.extendedVertices i).card:=Nat.cast_nonneg _
  have hU0:(0:ℝ)≤(Q.extendedIndices i).card:=Nat.cast_nonneg _
  have hA0:(0:ℝ)≤A.card:=Nat.cast_nonneg _
  have hAupper:((A.card:ℝ))≤(Q.extendedVertices i).card:=by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : A⊆_)
  have hAlower:(3/4:ℝ)*(Q.extendedVertices i).card≤A.card:=by nlinarith [hstep.1]
  have hBlower:(3/4:ℝ)*(Q.extendedIndices i).card≤B.card:=by nlinarith [hstep.2]
  have hDpos:0<D:=by
    have hnreal:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
    exact_mod_cast (lt_of_lt_of_le (by linarith : (0:ℝ)<(Fintype.card V:ℝ)/2) hD)
  have hUV:(2:ℝ)*(Q.extendedIndices i).card≤(Q.extendedVertices i).card:=by
    exact_mod_cast Q.extended_index_size_upper hreg hn hDpos he hρhi i
  have hUlower:(ρ₀/8)*(Q.extendedVertices i).card≤(Q.extendedIndices i).card:=by
    rw [Q.extendedVertices_eq hi,Q.extendedIndices_eq hi]
    exact Q.index_size_lower hreg hn hD hρ₀ hρlo hb hb1 hi
  have hBupper:((B.card:ℝ))≤(Q.extendedIndices i).card:=by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : B⊆_)
  have hBvsA:(3*ρ₀/32)*(A.card:ℝ)≤B.card:=by
    have h1:=mul_le_mul_of_nonneg_left hAupper (show 0≤3*ρ₀/32 by positivity)
    have h2:=mul_le_mul_of_nonneg_left hUlower (show (0:ℝ)≤3/4 by norm_num)
    nlinarith
  have hBupA:((B.card:ℝ))≤(2/3)*(A.card:ℝ):=by nlinarith
  have hAnext:((Anext.card:ℝ))≤(Q.extendedVertices (i+1)).card:=by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : Anext⊆_)
  have hdecay:((Anext.card:ℝ))≤(4*ε/3)*A.card:=by
    have hh:=mul_le_mul_of_nonneg_left hAlower he
    nlinarith [hstep.1]
  have hterminal:(3*ε*(m:ℝ)/8)≤A.card:=Q.difference_size_lower he he1 (by omega) (by omega)
  have hBterminal:(9*ρ₀*ε*(m:ℝ)/256)≤B.card:=by
    have hh:=mul_le_mul_of_nonneg_left hterminal (show 0≤3*ρ₀/32 by positivity)
    nlinarith
  exact ⟨hAlower,hBlower,hBvsA,hBupA,hdecay,hterminal,hBterminal⟩
end Oberwolfach
