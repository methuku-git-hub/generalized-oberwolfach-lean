module

public import Oberwolfach.VortexNextIndicesMargin

@[expose] public section
/-! The next vortex indices, viewed as a set of the current hubs, satisfy the
same contraction bound even after taking a subtype. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem Vortex.inner_hubs_margin {V U:Type*} [Fintype V] [Fintype U] [DecidableEq U]
    {G:SimpleGraph V} {D m:ℕ} {β ε κ:ℝ} (Q:Vortex U G D β ε m)
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (he:0<ε) (hm:0<m) (hρ:initialIndexDensity U D≤1)
    (hκ:ε≤2*κ) {i:ℕ} (hi:i<Q.length):
    let inner:Finset {u // u∈Q.indices i}:=Finset.univ.filter (fun u=>u.val∈Q.indices (i+1))
    (inner.card:ℝ)≤κ*(Q.vertices i).card:=by
  intro inner
  have hsub:inner.image Subtype.val⊆Q.indices (i+1):=by
    intro v hv
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hu).2
  have himage:(inner.image Subtype.val).card=inner.card:=Finset.card_image_iff.mpr (by intro a _ b _ h;exact Subtype.ext h)
  have hc:inner.card≤(Q.indices (i+1)).card:=by
    rw [←himage]
    exact Finset.card_le_card hsub
  have hcR:(inner.card:ℝ)≤(Q.indices (i+1)).card:=by exact_mod_cast hc
  exact hcR.trans (Q.next_indices_margin hreg hn hD he hm hρ hκ hi)
end Oberwolfach
