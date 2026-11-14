module

public import Oberwolfach.OrdinaryReservedPairLabels
public import Oberwolfach.AssignedEdgePreparationShielded
public import Oberwolfach.PrescribedBadEdgeAssignments
public import Oberwolfach.PrescribedMatchingOccurrenceBound

@[expose] public section
/-! Assign required edges on the selected reserved-spoke lists, avoiding the
absorber and protected hubs, and expose the matching inputs for placement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserved_assignment_placement_inputs
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n)
    (π:Equiv.Perm (Fin n)) (d:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (G:SimpleGraph (Fin n)) (Dstar:Fin n→Fin n→Prop)
    (hDstar:∀x y,G.Adj x y→Dstar x y∨Dstar y x)
    (Inner:Finset U) (Old Abs:U→Finset (Fin n))
    (hOld:∀u,Disjoint (rawReservedSpokeList π d σ u) (Old u))
    (ρ₀ smin b:ℝ) (hρ:0<ρ₀) (hs:0<smin) (hb:0≤b)
    (hU:ρ₀*n≤4*(Fintype.card U:ℝ))
    (hinner:(Inner.card:ℝ)≤(5*ρ₀*smin^2/128)*n)
    (herror:(n:ℝ)^(3/4:ℝ)≤(5*ρ₀*smin^2/128)*n)
    (hpair:∀x y,x≠y→(5/8:ℝ)*smin^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d σ (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d σ (y,w)=some (Sum.inr false))).card:ℝ))
    (hbsmall:b≤(5*ρ₀*smin^2/128)/16)
    (hAbs:∀v,((Finset.univ.filter (fun u=>v∈Abs u)).card:ℝ)≤b*n)
    (hdegree:∀v,(G.degree v:ℝ)≤b*n):
    let a:ℝ:=5*ρ₀*smin^2/128
    let Lists:=fun u=>rawReservedSpokeList π d σ u\Abs u;
    ∃M:U→Finset (Fin n×Fin n),
      (∀u,IsPrescribedOrientedMatching (M u)) ∧
      (∀u,Disjoint (Old u) (prescribedMatchingEndpoints (M u))) ∧
      (∀u,prescribedMatchingEndpoints (M u)⊆Lists u) ∧
      (∀u,u∈Inner→M u=∅) ∧
      (∀u,(M u).card≤⌈4*(G.edgeFinset.card:ℝ)/(a*n)⌉₊) ∧
      (∀u x y,(x,y)∈M u→Dstar x y) ∧
      (∀u,(M u).image prescribedArcPhysical⊆G.edgeFinset) ∧
      PairwisePhysicalDisjoint (fun u=>(M u).image prescribedArcPhysical) ∧
      (∀e∈G.edgeFinset,∃u,e∈(M u).image prescribedArcPhysical) ∧
      (∀v,(Finset.univ.filter (fun u=>v∈prescribedMatchingEndpoints (M u))).card≤G.degree v) :=by
  intro a Lists
  let Bad:Fin n→Finset U:=fun v=>Finset.univ.filter (fun u=>v∈Abs u)
  let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d σ) Inner
  obtain ⟨ha,hOutside,hShield,hLabels⟩:=ordinary_reserved_pair_matching_labels π d σ Inner Old hOld G Bad ρ₀ smin hρ hs hU hinner herror hpair
  letI:Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  have hUpos:0<Fintype.card U:=by
    have hh:0<(ρ₀:ℝ)*n:=mul_pos hρ (by exact_mod_cast hn)
    have hc:0<(Fintype.card U:ℝ):=by linarith
    exact_mod_cast hc
  letI:Nonempty U:=Fintype.card_pos_iff.mp hUpos
  obtain ⟨assign,orient,horient,hallowed,hmatching,hcap,hold,hinner,hmatch,hcard⟩:=
    prepare_assigned_bad_edges_with_shield G Dstar hDstar Lbad Bad Old Inner hShield
      (fun e _=>hOutside e) a b ha hb hbsmall (by simpa using hn)
      (by simpa only [Fintype.card_fin] using hLabels)
      (by simpa only [Fintype.card_fin,Bad] using hAbs)
      (by simpa only [Fintype.card_fin] using hdegree)
  let M:=prescribedAssignedArcs G assign orient
  have hphys:=prescribed_assigned_arcs_physical G assign orient (fun e he=>(horient e he).1)
  refine ⟨M,hmatch,hold,?_,hinner,?_,?_,?_,hphys.2.2,?_,?_⟩
  · intro u v hv
    obtain ⟨arc,harc,hv⟩:=Finset.mem_biUnion.mp hv
    obtain ⟨e,he,heq⟩:=Finset.mem_image.mp harc
    have heG:e∈G.edgeFinset:=(Finset.mem_filter.mp he).1
    have heU:assign e=u:=(Finset.mem_filter.mp he).2
    have hve:v∈e.toFinset:=by
      rw [←(horient e heG).1]
      simp only [prescribedArcPhysical,Sym2.toFinset_mk_eq,Finset.mem_insert,Finset.mem_singleton]
      simpa [heq] using hv
    have hl:=hallowed e heG
    rw [heU] at hl
    have hl' : ∀v∈e.toFinset,v∈rawReservedSpokeList π d σ u := by
      have hh : u∉Inner ∧ ∀v∈e.toFinset,v∈rawReservedSpokeList π d σ u := by
        simpa only [Lbad,protectedPairEdgeHubs,Finset.mem_filter,Finset.mem_univ,true_and] using hl.1
      exact hh.2
    have hnot:v∉Abs u:=by
      intro hvAbs
      have : u∈Bad v:=by simp [Bad,hvAbs]
      exact hl.2 v hve this
    exact Finset.mem_sdiff.mpr ⟨hl' v hve,hnot⟩
  · simpa only [a,Fintype.card_fin] using hcard
  · intro u x y hxy
    obtain ⟨e,he,heq⟩:=Finset.mem_image.mp hxy
    have hmem:e∈G.edgeFinset:=(Finset.mem_filter.mp he).1
    simpa only [heq] using (horient e hmem).2
  · intro u e he
    exact (hphys.1 u e he).1
  · intro e he
    exact ⟨assign e,hphys.2.1 e he⟩
  · intro v
    exact prescribed_matching_endpoint_occurrences M G (fun u e he=>(hphys.1 u e he).1) hphys.2.2 v
end Oberwolfach
