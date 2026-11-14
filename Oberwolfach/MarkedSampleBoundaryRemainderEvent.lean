module

public import Oberwolfach.MarkedSampleBoundaryPhysicalGraph
public import Oberwolfach.MarkedBoundaryMaskAfterPacking

@[expose] public section

/-! One original boundary-sampling event controls every later packing and
covering whose actual leftover and covering degrees meet the displayed
bound. The new mask is the remaining boundary graph, not a new sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_boundary_remainder_common_event (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ):
    ∃ N:ℕ,∀ (V U Gamma Color:Type) [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
      [Fintype Gamma] [Fintype Color],
    N≤Fintype.card (V⊕U)→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ₀:RawMarkedOutcome V U Gamma Color)
      (H:Bool→V→U→Prop) (X:Finset V) (Z:Finset U),(∀ v,π v∈X↔v∈X)→
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ₀ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ₀ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let G:=ordinaryBoundaryGraph (markedSampleArcSetGraph P π d σ₀ Finset.univ)
      (fun v u=>H false v u∨H true v u) X Z;
      1-1/(Fintype.card (V⊕U):ℝ)^q≤
        (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀ (C D:SimpleGraph (V⊕U)),Disjoint C (retainedGraph G σ)→
            ∀ ℓ δ:ℝ,(∀ x,(((G\retainedGraph G σ)\C).degree x:ℝ)≤ℓ)→
            (∀ x,(D.degree x:ℝ)≤δ)→2*(ℓ+δ)≤p^2*Fintype.card (V⊕U)/2→
            let τ:=fun e:Sym2 (V⊕U)=>decide (e∈((G\C)\D).edgeSet);
            (∀ x,((markedBoundarySupport tail head ktail khead π (H false) (H true) X Z τ x).card:ℝ)≤14*p*Fintype.card (V⊕U))∧
            (∀ x y,x≠y→((markedBoundarySupport tail head ktail khead π (H false) (H true) X Z τ x∩
              markedBoundarySupport tail head ktail khead π (H false) (H true) X Z τ y).card:ℝ)≤(14*p)^2*Fintype.card (V⊕U))∧
            (∀ v,((Finset.univ.filter (fun x=>v∈markedBoundarySupport tail head ktail khead π (H false) (H true) X Z τ x)).card:ℝ)≤
              14*p*Fintype.card (V⊕U))) :=by
  obtain ⟨N,hN⟩:=marked_boundary_robust_support_event p hp hp1 q
  refine ⟨N,?_⟩
  intro V U Gamma Color _ _ _ _ _ _ hn P π d σ₀ H X Z hX E K tail head ktail khead G
  have hphys:Function.Injective (markedPhysicalEdge tail head ktail khead π):=
    markedSampleArc_physical_injective P π (3*d) _
  have hevent:=hN V U E K hn tail head ktail khead π (H false) (H true) X Z hphys
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ C D hCR ℓ δ hleft hcover hsmall τ
  apply hσ τ
  intro x
  exact (marked_boundary_mask_after_packing tail head ktail khead π (H false) (H true)
    hphys X Z G C D σ
    (marked_sample_boundary_physical_coin_mem P π d σ₀ H X Z hX)
    hCR ℓ δ hleft hcover x).trans hsmall

end Oberwolfach
