module

public import Oberwolfach.OrdinaryNonrootParentFromRelativeBounds
public import Oberwolfach.OrdinaryNonrootRootScaleChoice
public import Oberwolfach.OrdinaryEditedParentWeakenError

@[expose] public section
/-! Choose the nonroot loss scale once, then restrict all parent fields
for any root sets within that scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_nonroot_parent_small_roots
    (r:ℕ) (hr:3≤r) (k:ℕ) (hk:4≤k) (α β b B h δ ε ω gap:ℝ)
    (hβ:0<β) (hδ:0<δ) (hδ1:δ<1) (hω:0<ω) (hgap:0<gap) (hB:0≤B) (hb:0≤b) (hh:0≤h):
    ∃lam:ℝ,0<lam ∧
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop)
      (d:OrdinaryEditedParentFields r hr k α β b B h δ ε P Q F H)
      (T:Finset V) (W:Finset U) (hn:0<Fintype.card V) (hu0:0<Fintype.card U)
      (hu:Fintype.card U≤Fintype.card V) (hU:ω*Fintype.card V≤Fintype.card U),
    (T.card:ℝ)+W.card≤lam*Fintype.card V→
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    Nonempty (OrdinaryEditedParentFields r hr k α (β/2) (b*(1-δ)^(r-1)) B h (δ/2) (ε+gap)
      (P.induce (A:Set V)) (Q.induce (A:Set V)) (F.induce (A:Set V))
      (fun (v:A) (u:C)=>H v.val u.val)):=by
  obtain ⟨lam,hlam,hscale⟩:=ordinary_nonroot_root_scale_choice r β δ ω gap B hβ hδ hω hgap hB
  refine ⟨lam,hlam,?_⟩
  intro P Q F H d T W hn hu0 hu hU hsize A C
  have hn0:0≤(Fintype.card V:ℝ):=by positivity
  have hw0:0≤(W.card:ℝ):=by positivity
  have ht0:0≤(T.card:ℝ):=by positivity
  have hs:=hscale (Fintype.card V) (Fintype.card U) ((T.card:ℝ)+W.card) (W.card:ℝ)
    hn0 hw0 (by linarith) hsize hU
  have hT:(T.card:ℝ)≤δ*Fintype.card V:=by linarith only [hs.1,hw0]
  obtain ⟨d'⟩:=ordinary_nonroot_parent_from_relative_bounds r hr k hk α β b B h δ ε lam P Q F H d T W
    hn hu0 hu hδ.le hδ1 hβ.le hb hB hh hT hs.2.1 hs.2.2.1 hs.2.2.2.1 hsize
  exact ordinary_edited_parent_weaken_error r hr k α (β/2) (b*(1-δ)^(r-1)) B h (δ/2)
    (ε+lam*(r:ℝ)^4*B) (ε+gap) _ _ _ _ d' (by linarith only [hs.2.2.2.2])
end Oberwolfach
