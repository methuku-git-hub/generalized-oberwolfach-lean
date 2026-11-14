module

public import Oberwolfach.LongActualPhysicalGraphsInHost
public import Oberwolfach.RandomOrientation
public import Oberwolfach.ExpandedSampleOrientation

@[expose] public section
/-! Turn the balanced-orientation correction into a physical deletion. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def orientationDisagreementGraph {V:Type} [LinearOrder V]
    (G:SimpleGraph V) (bits:Sym2 V→Bool) (M:V→V→ℕ):SimpleGraph V where
  Adj x y:=G.Adj x y ∧ (M x y≠sampledOrientation G bits x y ∨ M y x≠sampledOrientation G bits y x)
  symm:=⟨by intro x y h;exact ⟨h.1.symm,Or.symm h.2⟩⟩
  loopless:=⟨by intro x h;exact G.loopless.irrefl x h.1⟩

theorem orientation_disagreement_degree_le
    {V:Type} [Fintype V] [LinearOrder V] (G:SimpleGraph V) (bits:Sym2 V→Bool) (M:V→V→ℕ) (v:V):
    (orientationDisagreementGraph G bits M).degree v≤
      (Finset.univ.filter (fun w=>M v w≠sampledOrientation G bits v w ∨ M w v≠sampledOrientation G bits w v)).card:=by
  apply Finset.card_le_card
  intro w hw
  have hh:=(SimpleGraph.mem_neighborFinset _ _ _).mp hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.2⟩

theorem selected_relation_in_balanced_host_after_correction
    {V:Type} [Fintype V] [LinearOrder V] (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:Sym2 V→Fin 6×Bool) (M:V→V→ℕ) (x y:V):
    rawSelectedPhysicalRelation G π d ω x y →
    ¬(orientationDisagreementGraph G (fun e=>(ω e).2) M).Adj x y → M x y=1:=by
  intro h hDel
  have hsample:=expanded_selected_relation_uses_sampled_orientation G π d ω x y h
  have hG:G.Adj x y:=raw_selected_physical_relation_in_host G π d ω x y h
  by_contra hn
  apply hDel
  refine ⟨hG,Or.inl ?_⟩
  simpa [hsample] using hn

theorem selected_relation_in_balanced_host_after_deletion
    {V:Type} [Fintype V] [LinearOrder V] (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:Sym2 V→Fin 6×Bool) (M:V→V→ℕ) (Del:SimpleGraph V)
    (hcorrection:orientationDisagreementGraph G (fun e=>(ω e).2) M≤Del):
    ∀x y,rawSelectedPhysicalRelation G π d ω x y→¬Del.Adj x y→M x y=1:=by
  intro x y h hDel
  exact selected_relation_in_balanced_host_after_correction G π d ω M x y h
    (fun hh=>hDel (hcorrection hh))

theorem approximate_arc_in_balanced_host_after_correction
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color] (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ) (Del:SimpleGraph V)
    (hcorrection:orientationDisagreementGraph G (fun e=>(ω (Sum.inl e)).2) M≤Del):
    ∀x y,rawMixedPhysicalArc G π d (fun e=>rawExpandedApproximateCollapse e (ω e)) x y→
      ¬Del.Adj x y→M x y=1:=by
  intro x y h hDel
  have hsample:=expanded_approximate_arc_uses_sampled_orientation G π d ω x y h
  have hG:G.Adj x y:=by
    by_contra hn
    simp [sampledOrientation,hn] at hsample
  by_contra hM
  apply hDel
  exact hcorrection ⟨hG,Or.inl (by simpa [hsample] using hM)⟩

theorem physical_edge_has_balanced_direction
    {V:Type} [LinearOrder V] (G:SimpleGraph V) (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if G.Adj x y then 1 else 0):
    ∀x y,G.Adj x y→M x y=1 ∨ M y x=1:=by
  intro x y h
  have hh:=hphysical x y
  simp only [h,if_true] at hh
  omega
theorem balanced_direction_is_host_edge
    {V:Type} [LinearOrder V] (G:SimpleGraph V) (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if G.Adj x y then 1 else 0):
    ∀x y,M x y=1→G.Adj x y:=by
  intro x y h
  by_contra hn
  have hh:=hphysical x y
  simp only [hn,if_false] at hh
  omega
end Oberwolfach
