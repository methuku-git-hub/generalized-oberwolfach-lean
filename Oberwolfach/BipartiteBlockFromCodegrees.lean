module

public import Oberwolfach.BipartiteBlockMatching
public import Oberwolfach.DomainCodegreeCuts

@[expose] public section

/-! Degree and codegree estimates give the exact block inputs used in the
marked endpoint pairing. The row and column domains need not coincide. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem bipartite_block_bounds_of_codegrees
    (E : X → Y → Prop) (P : X → Prop) (Q : Y → Prop)
    (F : SimpleGraph X) (b : ℕ) (p err eta d tau lam : ℝ)
    (hp : 0<p) (hp1 : p≤1) (herr : 0≤err) (heta : 0<eta)
    (hQ : 0<(Finset.univ.filter Q).card)
    (hF : ∀ x,F.degree x≤b)
    (hrow : ∀ x,P x → (p-err)*(Finset.univ.filter Q).card≤
      ((Finset.univ.filter (fun y=>Q y ∧ E x y)).card:ℝ))
    (hcol : ∀ y,Q y → (p-err)*(Finset.univ.filter P).card≤
      ((Finset.univ.filter (fun x=>P x ∧ E x y)).card:ℝ))
    (hcodeg : ∀ x,P x → ∀ z,P z → x≠z → ¬F.Adj x z →
      ((Finset.univ.filter (fun y=>Q y ∧ E x y ∧ E z y)).card:ℝ)≤
        (p^2+err)*(Finset.univ.filter Q).card)
    (hsmall : err≤p^2*eta/24)
    (hlarge : (b+1:ℝ)≤p^2*eta^2*(Finset.univ.filter Q).card/8)
    (hdQ : d≤(p-err)*(Finset.univ.filter Q).card)
    (hdP : d≤(p-err)*(Finset.univ.filter P).card)
    (htau : eta*(Finset.univ.filter Q).card≤tau) (hlam : lam≤p/2) :
    BipartiteBlockBounds E P Q d tau lam := by
  refine ⟨fun x hx=>hdQ.trans (hrow x hx),fun y hy=>hdP.trans (hcol y hy),?_⟩
  intro S T hS hT hSt hTt
  have hh := degree_codegree_cuts_on_domains E F (Finset.univ.filter P) (Finset.univ.filter Q)
    p err eta b hp hp1 herr heta hQ hF
    (by
      intro x hx
      simpa only [Finset.filter_filter] using hrow x (Finset.mem_filter.mp hx).2)
    (by
      intro x hx z hz hne hbad
      simpa only [Finset.filter_filter] using hcodeg x (Finset.mem_filter.mp hx).2 z
        (Finset.mem_filter.mp hz).2 hne hbad)
    hsmall hlarge S (by intro x hx;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hS x hx⟩)
    T (by intro y hy;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hT y hy⟩)
    (htau.trans hSt) (htau.trans hTt)
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlam (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)).trans hh

end Oberwolfach
