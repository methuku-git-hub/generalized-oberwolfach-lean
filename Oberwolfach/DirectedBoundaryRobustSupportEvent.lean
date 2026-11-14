module

public import Oberwolfach.DirectedBoundarySupportChanges
public import Oberwolfach.BoundarySupportChanges

@[expose] public section

/-! One boundary event remains valid for every later physical mask with
the stated actual changed-incidence bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem directed_boundary_robust_support_event (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ):
    ∃ N:ℕ,∀ (A W E T:Type) [Fintype A] [DecidableEq A] [Fintype W] [DecidableEq W]
      [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T],
    N≤Fintype.card W→Fintype.card T≤3→
    ∀ (tail head:A→W) (kind:A→T) (coin:A↪E) (X:Finset W) (π:Equiv.Perm W),
      Function.Injective (fun a=>(kind a,tail a,head a))→
      1-1/(Fintype.card W:ℝ)^q≤
        (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀ τ:E→Bool,
            (∀ x,((Finset.univ.filter (fun a:DirectedBoundaryEdge tail head X=>
              (tail a.val=x∨head a.val=x)∧σ (coin a.val)≠τ (coin a.val))).card:ℝ)≤
              p^2*Fintype.card W/2)→
            (∀ x,((directedBoundarySupport tail head coin X π τ x).card:ℝ)≤14*p*Fintype.card W)∧
            (∀ x y,x≠y→((directedBoundarySupport tail head coin X π τ x∩
              directedBoundarySupport tail head coin X π τ y).card:ℝ)≤(14*p)^2*Fintype.card W)∧
            (∀ v,((Finset.univ.filter (fun x=>v∈directedBoundarySupport tail head coin X π τ x)).card:ℝ)≤
              14*p*Fintype.card W)) := by
  obtain ⟨N,hN⟩:=directed_boundary_support_common_event p hp hp1 q
  refine ⟨N,?_⟩
  intro A W E T _ _ _ _ _ _ _ _ hn hT tail head kind coin X π hinj
  apply (hN A W E T hn hT tail head kind coin X π hinj).trans
  apply finiteLaw_probability_mono
  intro σ hσ τ hτ
  obtain ⟨hr,hc⟩:=directed_boundary_support_changes tail head coin X π σ τ
    (p^2*Fintype.card W/2) hτ
  apply support_selection_margins (directedBoundarySupport tail head coin X π σ)
    (directedBoundarySupport tail head coin X π τ) p (Fintype.card W)
    (2*(p^2*Fintype.card W/2)) (2*(p^2*Fintype.card W/2)) hp.le hp1 (Nat.cast_nonneg _)
    hσ.1 hσ.2.1 hσ.2.2 hr hc
  · linarith
  · have hh:=mul_le_mul_of_nonneg_right (by nlinarith : p^2≤p) (Nat.cast_nonneg (α:=ℝ) (Fintype.card W))
    linarith

end Oberwolfach
