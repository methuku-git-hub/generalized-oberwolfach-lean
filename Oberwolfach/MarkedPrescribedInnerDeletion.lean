module

public import Oberwolfach.MarkedActiveDeletionSeparateBounds

@[expose] public section

/-! The prescribed packing's ambient degree estimates imply the inner
factor deletion bounds, including at every retained outer hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z E K:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [LinearOrder V] [DecidableEq W] [DecidableEq U] [DecidableEq Z]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_prescribed_inner_deletion
    (ME:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (f:W↪V) (g:Z↪U) (r:ℕ) (iota etaE zeta:ℝ) (he:0≤etaE) (hz:0≤zeta)
    (hsize:iota*Fintype.card V≤(Fintype.card W:ℝ))
    (hRsmall:24*etaE≤zeta*iota) (hSsmall:3*(r+5:ℝ)*etaE≤zeta*iota)
    (hR:∀ x,((markedPackingRimGraph ME).degree x:ℝ)≤24*etaE*Fintype.card V)
    (hV:∀ x,((Finset.univ.filter (markedPackingSpokes ME x)).card:ℝ)≤6*etaE*Fintype.card V)
    (hU:∀ u,((Finset.univ.filter (fun x=>markedPackingSpokes ME x u)).card:ℝ)≤3*(r+5)*etaE*Fintype.card V):
    (∀ x,(((markedPackingRimGraph ME).comap f).degree x:ℝ)≤zeta*Fintype.card W)∧
    (∀ x,(((markedFiniteSpokeGraph (ME.biUnion markedWheelSpokePairs)).comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤zeta*Fintype.card W)∧
    (∀ u,(((markedFiniteSpokeGraph (ME.biUnion markedWheelSpokePairs)).comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤zeta*Fintype.card W):=by
  have hRbudget:=mul_le_mul_of_nonneg_right hRsmall (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  have hSbudget:=mul_le_mul_of_nonneg_right hSsmall (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  have hscale:=mul_le_mul_of_nonneg_left hsize hz
  have hRbound:24*etaE*Fintype.card V≤zeta*Fintype.card W:=by
    nlinarith only [hRbudget,hscale]
  have hUbound:3*(r+5:ℝ)*etaE*Fintype.card V≤zeta*Fintype.card W:=by
    nlinarith only [hSbudget,hscale]
  have hVbound:6*etaE*Fintype.card V≤zeta*Fintype.card W:=by
    have hn:=Nat.cast_nonneg (α:=ℝ) r
    have hprod:0≤etaE*Fintype.card V:=by positivity
    nlinarith only [hUbound,mul_nonneg hn hprod,hprod]
  have hsp:=markedFiniteSpokeGraph_packing_degrees ME
  refine ⟨?_,?_,?_⟩
  · intro x
    exact ((Nat.cast_le (α:=ℝ)).mpr (graph_comap_injective_degree_le (markedPackingRimGraph ME) f x)).trans
      ((hR (f x)).trans hRbound)
  · intro x
    have hh:(((markedFiniteSpokeGraph (ME.biUnion markedWheelSpokePairs)).comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤
      (markedFiniteSpokeGraph (ME.biUnion markedWheelSpokePairs)).degree (Sum.inl (f x)):=
      Nat.cast_le.mpr (graph_comap_injective_degree_le _ (f.sumMap g) (Sum.inl x))
    rw [hsp.1] at hh
    exact hh.trans ((hV (f x)).trans hVbound)
  · intro u
    have hh:(((markedFiniteSpokeGraph (ME.biUnion markedWheelSpokePairs)).comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤
      (markedFiniteSpokeGraph (ME.biUnion markedWheelSpokePairs)).degree (Sum.inr (g u)):=
      Nat.cast_le.mpr (graph_comap_injective_degree_le _ (f.sumMap g) (Sum.inr u))
    rw [hsp.2] at hh
    exact hh.trans ((hU (g u)).trans hUbound)

end Oberwolfach
