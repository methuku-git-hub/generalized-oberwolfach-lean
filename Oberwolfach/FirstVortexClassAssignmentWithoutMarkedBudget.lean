module

public import Oberwolfach.FirstVortexClassPrescribedAssignmentNoMarkedBudget
public import Oberwolfach.ReservedAssignmentWithoutMarkedBudget

@[expose] public section
/-! The actual class assignment uses reserved-pair labels and does not need
an upper bound on the retained marked labels at each vertex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstClassNoMarkedBudgetFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_assignment_without_marked_budget
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P S Del Used Kbad:SimpleGraph (Fin n)) (I:Finset (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (H:Finset U) (α b ρ₀ θ ε lam:ℝ) (Old:U→Finset (Fin n)) (Pack:Finset (Sym2 (Fin n)))
    (hn:0<n) (hU:0<Fintype.card U) (hρ₀:0<ρ₀) (hb:0≤b) (hbsmall:b≤((ρ₀/4)/40000)/16) (hαb:α/16≤b):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let Jbad:=spanningRestriction (S\Used) I\Kbad
    let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d (fun e=>raw (Sum.inr e))) H
    let Bad:=fun v:Fin n=>Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)
    (∀v,(Kbad.degree v:ℝ)≤(α/16)*n)→
    (Kbad.edgeFinset.card:ℝ)≤(θ*ε^2+lam*ε)*(n:ℝ)^2+24*d*n→
    Disjoint Kbad.edgeFinset Pack→(∀v,(Jbad.degree v:ℝ)≤ε*n)→
    Disjoint Kbad.edgeFinset Jbad.edgeFinset→Disjoint Used.edgeFinset Jbad.edgeFinset→
    (∀w,Disjoint (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w) (Old w))→
    (∀e∈Kbad.edgeFinset,((ρ₀/4)/40000)*n≤((Lbad e).card:ℝ))→
    FirstVortexClassPrescribedAssignmentNoMarkedBudget P S Del Used Kbad I π d σE t Jret H α b ρ₀ θ ε lam Old Pack:=by
  intro raw Jbad Lbad Bad hdegree hecount hpack hJ hKJ hUsedJ hOld hLabels
  letI:Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σE (Sum.inl e)) x y ∧ ¬Del.Adj x y
  let Dstar:=fun x y=>Dfree x y ∨ Kbad.Adj x y
  have hDstar:∀x y,Kbad.Adj x y→Dstar x y∨Dstar y x:=by
    intro x y h
    exact Or.inl (Or.inr h)
  have hG:∀v,(Kbad.degree v:ℝ)≤b*n:=by
    intro v
    exact (hdegree v).trans (mul_le_mul_of_nonneg_right hαb (Nat.cast_nonneg n))
  have hcap:0<(ρ₀/4)/40000:=by positivity
  have hnV:0<Fintype.card (Fin n):=by simpa using hn
  obtain ⟨hOutside,hShield⟩:=protected_pair_edge_hubs_avoid_old_images
    (rawReservedSpokeList π d (fun e=>raw (Sum.inr e))) Old H hOld
  obtain ⟨assign,orient,horient,hallowed,hconf,hcap',hold,hinner,hmatching,hcard⟩:=
    prepare_reserved_edges_without_marked_budget Kbad Dstar hDstar π d (fun e=>raw (Sum.inr e)) t Jret
      Old H hOld ((ρ₀/4)/40000) b hcap hb hbsmall hnV
      (by simpa only [Fintype.card_fin] using hLabels)
      (by simpa only [Fintype.card_fin] using hG)
  unfold FirstVortexClassPrescribedAssignmentNoMarkedBudget
  refine ⟨hdegree,hecount,hpack,hJ,hKJ,hUsedJ,hOutside,?_,hLabels,assign,orient,horient,?_,?_,
    by simpa only [Fintype.card_fin] using hcap',hold,hinner,hmatching,by simpa only [Fintype.card_fin] using hcard⟩
  · intro w e v he hv ho hl
    exact False.elim (hShield w e v hv ho hl)
  · intro e he
    obtain ⟨hl,hsafe⟩:=hallowed e he
    refine ⟨hl,?_⟩
    intro v hv hvBad
    exact hsafe v hv ((Finset.mem_filter.mp hvBad).2)
  · intro e he e' he' hne heq
    exact hconf (assign e) e he e' he' rfl heq.symm hne
end Oberwolfach
