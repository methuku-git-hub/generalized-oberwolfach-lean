module

public import Oberwolfach.OrdinaryAsymmetricVortexCertificateFromSharpReference

@[expose] public section
/-! A fixed constant failure budget and the complement-size thresholds
follow from a large enough parent and a quarter-sized protected root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_complement_reserve_size_inputs
    (T:Finset V) (W:Finset U) (n₀ Nreserve Nclean:ℕ)
    (hroot:(T.card:ℝ)≤(1/4:ℝ)*Fintype.card V)
    (hn₀:4*n₀≤Fintype.card V) (hreserve:4*Nreserve≤Fintype.card V)
    (hclean:Nclean≤Fintype.card V) (hlarge:64≤Fintype.card V):
    let A:=↥(Finset.univ\T);let B:=↥(Finset.univ\W);
    n₀≤Fintype.card A ∧ Nreserve≤Fintype.card (A⊕B) ∧ Nclean≤Fintype.card (V⊕U) ∧
    1/(Fintype.card (A⊕B):ℝ)≤(1/16:ℝ) ∧
    (1/16:ℝ)+2/(Fintype.card (V⊕U):ℝ)≤1/8:=by
  intro A B
  have hpart:Fintype.card A+T.card=Fintype.card V:=by
    simpa only [A,Fintype.card_coe,Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  have hpartR:(Fintype.card A:ℝ)+T.card=Fintype.card V:=by exact_mod_cast hpart
  have hlargeR:(64:ℝ)≤Fintype.card V:=by exact_mod_cast hlarge
  have hAlarge:(48:ℝ)≤Fintype.card A:=by linarith
  have hA0:(0:ℝ)≤Fintype.card A:=by positivity
  have hB0:(0:ℝ)≤Fintype.card B:=by positivity
  have hU0:(0:ℝ)≤Fintype.card U:=by positivity
  have hAplus:(Fintype.card A:ℝ)≤Fintype.card (A⊕B):=by simp
  have hVplus:(Fintype.card V:ℝ)≤Fintype.card (V⊕U):=by simp
  have hsum:0<(Fintype.card (A⊕B):ℝ):=by linarith
  have hphys:0<(Fintype.card (V⊕U):ℝ):=by linarith
  have hn₀R:((n₀:ℕ):ℝ)≤Fintype.card A:=by
    have hh:((4*n₀:ℕ):ℝ)≤Fintype.card V:=by exact_mod_cast hn₀
    norm_num at hh
    linarith
  have hreserveR:((Nreserve:ℕ):ℝ)≤Fintype.card (A⊕B):=by
    have hh:((4*Nreserve:ℕ):ℝ)≤Fintype.card V:=by exact_mod_cast hreserve
    norm_num at hh
    linarith
  have hclean':Nclean≤Fintype.card (V⊕U):=by
    have hh:Fintype.card V≤Fintype.card (V⊕U):=
      Fintype.card_le_of_injective (Sum.inl:V→V⊕U) Sum.inl_injective
    exact hclean.trans hh
  have hinv:1/(Fintype.card (A⊕B):ℝ)≤(1/16:ℝ):=by
    apply (div_le_iff₀ hsum).2
    nlinarith
  have htwo:2/(Fintype.card (V⊕U):ℝ)≤(1/16:ℝ):=by
    apply (div_le_iff₀ hphys).2
    nlinarith
  refine ⟨?_,?_,hclean',hinv,?_⟩
  · exact_mod_cast hn₀R
  · exact_mod_cast hreserveR
  · linarith
end Oberwolfach
