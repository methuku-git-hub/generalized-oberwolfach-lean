module

public import Oberwolfach.MarkedPhysicalCutTransfer
public import Oberwolfach.MarkedReferenceFixedCuts
public import Oberwolfach.OccurrenceRestrictionCuts

@[expose] public section

/-! The ordinary-rim cut required in active cover-down follows from the
reference cut family, with a precise cutoff and a realized deletion loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem square_bipartiteLargeCut_iff {V:Type} [Fintype V] [DecidableEq V]
    (hn:0<Fintype.card V) (M:V→V→ℕ) (δ h:ℝ):
    BipartiteLargeCut M δ h↔∀ S T:Finset V,
      (1-2*δ)*Fintype.card V<(S.card:ℝ)+T.card→
      h*Fintype.card V*min (S.card:ℝ) T.card≤(matrixCut M S T:ℝ):=by
  have hn0:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hn1:(0:ℝ)≤Fintype.card V:=hn0.le
  unfold BipartiteLargeCut
  have he (S T:Finset V):
      (1-2*δ<(S.card:ℝ)/Fintype.card V+(T.card:ℝ)/Fintype.card V)↔
      (1-2*δ)*Fintype.card V<(S.card:ℝ)+T.card:=by
    rw [←add_div,lt_div_iff₀ hn0]
  simp only [he,bipartiteLargeCut_sum_restrict,bipartite_normalized_cut_scale hn hn,
    ←mul_min_of_nonneg _ _ hn1,←mul_assoc]
  rfl

variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_protected_active_ordinary_cut
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ) (hn:0<Fintype.card W)
    (σ:RawMarkedOutcome V U Γ Color) (DR:SimpleGraph V) (a:Γ) (c:Color)
    (γ p k tstar ζ:ℝ) (hγ:0≤γ) (hp:0≤p) (hp1:p≤1) (hζ:0≤ζ) (hζsmall:ζ≤γ*p/8)
    (hcut:MarkedReferenceCutFamilies P π d a c γ p k tstar σ)
    (hsize:(1-min ((γ/8)/16) (p/128))*Fintype.card V≤(Fintype.card W:ℝ))
    (hDR:∀ x,((DR.comap f).degree x:ℝ)≤ζ*Fintype.card W):
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset);
    ∀ S T:Finset W,(1-2*min ((γ/8)/16) (p/128))*Fintype.card W<(S.card:ℝ)+T.card→
      4*((γ/8)*p/16)*Fintype.card W*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e:MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false=>
        e.val.1∈S∧e.val.2∈T)).card:ℝ):=by
  intro σA
  let δ:=min ((γ/8)/16) (p/128)
  have hd0:0≤δ:=le_min (by positivity) (by positivity)
  have hd1:δ<1:=lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hdγ:2*δ≤γ/32:=by have h:=min_le_left ((γ/8)/16) (p/128);dsimp [δ];linarith
  have hdp:2*δ≤p/32:=by have h:=min_le_right ((γ/8)/16) (p/128);dsimp [δ];linarith
  have hV:0<Fintype.card V:=lt_of_lt_of_le hn (Fintype.card_le_of_injective f f.injective)
  have hparent:BipartiteLargeCut (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false) (2*δ) (γ*p/4):=by
    apply (square_bipartiteLargeCut_iff hV _ _ _).mpr
    exact hcut.2 false (2*δ) hdγ hdp
  have hemb:=bipartiteLargeCut_embedding f.toEmbedding f.toEmbedding _ hn hn (1-δ) (2*δ) δ (γ*p/4)
    (by linarith) (by positivity) hsize hsize (by nlinarith [sq_nonneg δ]) hparent
  have he:(fun x y=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false (f x) (f y))=
      markedPhysicalRim (P.comap f) ρ (3*d) (fun e=>rawMarkedRestrictPair f g σ (Sum.inl e)) false:=by
    funext x y
    exact (markedPhysicalRim_restrictPair_eq f g π ρ hf P d σ false x y).symm
  change BipartiteLargeCut (fun x y=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false (f x) (f y)) _ _ at hemb
  rw [he] at hemb
  have hdel:=marked_rim_largeCut_after_physical_deletion (P.comap f) ρ d hn
    (rawMarkedRestrictPair f g σ) false (DR.comap f) δ (γ*p/4) ζ hζ hDR hemb
  rw [←rawMarkedRestrictPair_deleteRims f g σ DR] at hdel
  have hfin:=bipartiteLargeCut_coefficient_mono _ δ (γ*p/4-ζ) (4*((γ/8)*p/16))
    (by have h:0≤γ*p:=mul_nonneg hγ hp;nlinarith) hdel
  have hmatrix:=(square_bipartiteLargeCut_iff hn _ _ _).mp hfin
  intro S T hST
  have hh:=hmatrix S T hST
  rw [←markedSampleArc_multiplicity,occurrence_matrix_cut] at hh
  exact hh

end Oberwolfach
