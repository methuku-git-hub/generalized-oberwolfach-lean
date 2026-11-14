module

public import Oberwolfach.BipartiteLargeCutEquivRelabel
public import Oberwolfach.MarkedProtectedActiveFourCuts
public import Oberwolfach.MarkedRetainedArcRelabel
public import Oberwolfach.RawMarkedPairRestriction

@[expose] public section
/-! Transport the four reference cuts from a full-domain relabelling to
the original raw marked sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [Nonempty W]
  [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_reference_four_cuts_relabel
    (F:W↪oV) (f:W≃V) (hf:∀w,f w=F w) (g:Z≃U)
    (π:Equiv.Perm V) (ρ:Equiv.Perm W) (hc:∀w,f (ρ w)=π (f w))
    (P:SimpleGraph V) (d:ℕ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (α kstar tstar p k:ℝ) (hα:0<α) (hkstar:0<kstar) (htstar:0<tstar)
    (hpmin:kstar≤p) (hkmin:kstar≤k) (hZ:0<Fintype.card Z)
    (hcuts:MarkedReferenceCutFamilies (P.comap F) ρ d a j α p k tstar
      (markedRetainedPairRestriction f g π ρ hc d a z).1):
    let δ:=min (min α kstar) tstar/256
    let h:=min (α*kstar) tstar/128;
    (∀mark,BipartiteLargeCut (markedPhysicalRim P π (3*d) (fun e=>z.1 (Sum.inl e)) mark) δ (16*h)) ∧
    (∀mark,BipartiteLargeCut (relationMultiplicity (rawMarkedPairSpokes π d z.1 a j mark)) δ (16*h)):=by
  intro δ h
  have hW:0<Fintype.card W:=Fintype.card_pos
  have hV:0<Fintype.card V:=Fintype.card_pos
  have hU:0<Fintype.card U:=by rw [←Fintype.card_congr g];exact hZ
  have hnonneg:0≤16*h:=by dsimp [h];positivity
  obtain ⟨hR,hS⟩:=marked_reference_four_bipartite_cuts (P.comap F) ρ d a j α kstar tstar p k
    hα hkstar htstar hpmin hkmin hW hZ (markedRetainedPairRestriction f g π ρ hc d a z).1 hcuts
  have hcomm:∀x,F (ρ x)=π (F x):=by intro x;simpa only [←hf] using hc x
  have hsp (mark:Bool) (x:W) (u:Z):
      rawMarkedPairSpokes ρ d (markedRetainedPairRestriction f g π ρ hc d a z).1 a j mark x u ↔
        rawMarkedPairSpokes π d z.1 a j mark (f x) (g u):=by
    have hs:=rawMarkedRestrictPair_spokes F g π ρ hcomm d z.1 a j mark x u
    have heq:(f:W→V)=F:=funext hf
    rw [←heq] at hs
    simpa only [markedRetainedPairRestriction] using hs
  constructor
  · intro mark
    have hh:=bipartite_large_cut_equiv_relabel f.symm f.symm
      (markedPhysicalRim (P.comap F) ρ (3*d) (fun e=>(markedRetainedPairRestriction f g π ρ hc d a z).1 (Sum.inl e)) mark)
      hV hV δ (16*h) hnonneg (hR mark)
    have heq:(fun x y=>markedPhysicalRim (P.comap F) ρ (3*d)
      (fun e=>(markedRetainedPairRestriction f g π ρ hc d a z).1 (Sum.inl e)) mark (f.symm x) (f.symm y))=
        markedPhysicalRim P π (3*d) (fun e=>z.1 (Sum.inl e)) mark:=by
      funext x y
      have hs:=marked_retained_arc_predicate_relabel F f hf g π ρ hc P d a z mark (f.symm x) (f.symm y)
      rw [←markedPhysicalRim_indicator (P.comap F) ρ (3*d) _ mark (f.symm x) (f.symm y),
        ←markedPhysicalRim_indicator P π (3*d) _ mark x y]
      have hiff:markedPhysicalRim (P.comap F) ρ (3*d)
        (fun e=>(markedRetainedPairRestriction f g π ρ hc d a z).1 (Sum.inl e)) mark (f.symm x) (f.symm y)=1 ↔
        markedPhysicalRim P π (3*d) (fun e=>z.1 (Sum.inl e)) mark x y=1:=by
          simpa only [Equiv.apply_symm_apply] using hs
      by_cases h1:markedPhysicalRim (P.comap F) ρ (3*d)
        (fun e=>(markedRetainedPairRestriction f g π ρ hc d a z).1 (Sum.inl e)) mark (f.symm x) (f.symm y)=1
      · have h2:=hiff.mp h1; simp only [h1,h2,if_true]
      · have h2:¬markedPhysicalRim P π (3*d) (fun e=>z.1 (Sum.inl e)) mark x y=1:=fun hh=>h1 (hiff.mpr hh)
        simp only [h1,h2,if_false]
    simpa only [heq] using hh
  · intro mark
    have hh:=bipartite_large_cut_equiv_relabel f.symm g.symm
      (relationMultiplicity (rawMarkedPairSpokes ρ d (markedRetainedPairRestriction f g π ρ hc d a z).1 a j mark))
      hV hU δ (16*h) hnonneg (hS mark)
    have heq:(fun x u=>relationMultiplicity (rawMarkedPairSpokes ρ d
      (markedRetainedPairRestriction f g π ρ hc d a z).1 a j mark) (f.symm x) (g.symm u))=
        relationMultiplicity (rawMarkedPairSpokes π d z.1 a j mark):=by
      funext x u
      simp only [relationMultiplicity,hsp,Equiv.apply_symm_apply]
    simpa only [heq] using hh
end Oberwolfach
