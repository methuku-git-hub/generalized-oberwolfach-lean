module

public import Oberwolfach.OrdinaryEditedCutsFromSample
public import Oberwolfach.OrdinaryEditedCountsFromSample
public import Oberwolfach.OrdinaryEditedSpokeDegree
public import Oberwolfach.OrdinaryEditedParentWeightFromPotential
public import Oberwolfach.OrdinaryConflictFreeEditBounds

@[expose] public section
/-! Original same-sample reference hypotheses and their edited-parent
structural consequences, named separately from reserve geometry. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

structure OrdinaryEditedParentFields (r:ℕ) (hr:3≤r) (k:ℕ) (α β b B h δ ε:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) where
  orientation:V→V→ℕ
  orientation_graph:∀x y,orientation x y+orientation y x=if Q.Adj x y then 1 else 0
  rim_cuts:BipartiteLargeCut orientation δ h
  spoke_cuts:BipartiteLargeCut (relationMultiplicity H) δ h
  spoke_degree:∀v,β*Fintype.card V≤((Finset.univ.filter (H v)).card:ℝ)
  isolators:∀x y,Q.Adj x y→β*(Fintype.card V:ℝ)^(k-1)≤
    (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k (max (1/2) (cycleThreshold r)) (α/4) x y):ℝ)
  transfers:∀v (i j:{u // H v u}),i.val≠j.val→β*(Fintype.card V:ℝ)^(r^2)≤
    (Fintype.card (OrdinaryTransferConfiguration hr Q F H v i.val j.val):ℝ)
  weight:OrdinaryWheel Q F H r→ℝ
  weight_bounds:∀W,b/(Fintype.card V:ℝ)^(r-1)≤weight W ∧ weight W≤B/(Fintype.card V:ℝ)^(r-1)
  rim_load:∀x y,Q.Adj x y→|ordinaryRimLoad weight x y-1|≤ε
  spoke_load:∀v u,H v u→|ordinarySpokeLoad weight v u-1|≤ε

structure OrdinaryEditedSampleReferenceData (r:ℕ) (hr:3≤r) (k:ℕ)
    (α βsource β b B h ζ δ εsource ε d:ℝ)
    (P Q F:SimpleGraph V) (H₀ H:V→U→Prop) (σ coins:Sym2 V→Bool) where
  positive_V:0<Fintype.card V
  positive_U:0<Fintype.card U
  hub_upper:Fintype.card U≤Fintype.card V
  k_lower:4≤k
  zeta_nonneg:0≤ζ
  bound_nonneg:0≤b
  upper_nonneg:0≤B
  edit_nonneg:0≤d
  graph_sub:Q≤P\F
  rim_edit:∀v,((changed ((retainedGraph P σ).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤d
  spoke_row_edit:∀v,((changed (Finset.univ.filter (H₀ v)) (Finset.univ.filter (H v))).card:ℝ)≤d
  spoke_column_edit:∀u,((changed (Finset.univ.filter (fun v=>H₀ v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤d
  rim_scale:d≤ζ*Fintype.card V
  spoke_scale:d≤ζ*Fintype.card U
  rim_cut:BipartiteLargeCut (sampledOrientation (retainedGraph P σ\F) coins) δ h
  spoke_cut:BipartiteLargeCut (relationMultiplicity H₀) δ h
  sampled_spoke_degree:∀v,βsource*Fintype.card V≤((Finset.univ.filter (H₀ v)).card:ℝ)
  degree_margin:β+ζ≤βsource
  isolator_potential:∀x y,x≠y→¬F.Adj x y→βsource≤
    ordinaryIsolatorPotential P F H₀ k (max (1/2) (cycleThreshold r)) (α/4) x y σ
  transfer_potential:∀v u u',u≠u'→βsource≤
    transferSurvivalSum r hr P F (transferRootCompletedSpokes H₀ v) v u u' σ
  isolator_margin:8*(d+1)≤(βsource-β)*Fintype.card V
  transfer_margin:5*(r:ℝ)^4*(d+1)≤(βsource-β)*Fintype.card V
  seed:OrdinaryWheel P F (fun _ _=>True) r→ℝ
  seed_bounds:∀W,b/(Fintype.card V:ℝ)^(r-1)≤seed W ∧ seed W≤B/(Fintype.card V:ℝ)^(r-1)
  rim_potential:∀x y,P.Adj x y→¬F.Adj x y→
    |ordinaryPotentialLoad seed (Sum.inl s(x,y)) (retainedGraph P σ\F) H₀-1|≤εsource
  spoke_potential:∀v u,|ordinaryPotentialLoad seed (Sum.inr (v,u)) (retainedGraph P σ\F) H₀-1|≤εsource
  weight_margin:εsource+8*(r:ℝ)^4*B*d/Fintype.card V≤ε
end Oberwolfach
