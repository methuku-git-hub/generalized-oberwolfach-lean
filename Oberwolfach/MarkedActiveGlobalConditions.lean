module

public import Oberwolfach.MarkedActiveCoverDownLocal

@[expose] public section

/-! Exact global inputs of the active cover-down constructor. This is a
predicate on the actual typed host; it asserts no construction by itself. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

structure MarkedActiveGlobalConditions {V U E K:Type}
    [Fintype V] [Fintype U] [Fintype E] [Fintype K] [DecidableEq V] [DecidableEq U]
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (d r:ℕ)
    (H₀ HK:V→U→Prop)
    (p D alpha beta Lsp bminus bplus omega eps eta0 delta0 deltaCut hCut:ℝ):Prop where
  degree_lower : (Fintype.card V:ℝ)/2≤D
  degree_upper : D≤2*Fintype.card V
  ordinary_out : ∀ x,|occurrenceDegree tail x-p*D|≤eps*Fintype.card V
  ordinary_in : ∀ x,|occurrenceDegree head x-p*D|≤eps*Fintype.card V
  marked_out : ∀ x,|occurrenceDegree ktail x-p*D/(r+4:ℝ)|≤eps*Fintype.card V
  marked_in : ∀ x,|occurrenceDegree khead x-p*D/(r+4:ℝ)|≤eps*Fintype.card V
  two_step : ∀ x y,x≠y→4*alpha*p^2*Fintype.card V≤
    ((Finset.univ.filter (fun z=>(∃ e,tail e=x∧head e=z)∧(∃ e,tail e=z∧head e=y))).card:ℝ)
  ordinary_cut : ∀ S T:Finset V,(1-2*min (alpha/16) (p/128))*Fintype.card V<(S.card:ℝ)+T.card→
    4*(alpha*p/16)*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e=>tail e∈S∧head e∈T)).card:ℝ)
  compatible_hubs : ∀ C:MarkedCycleTuple tail head ktail khead (r+4) π (3*d),
    4*beta*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible H₀ HK C.val u}:ℝ)
  hubs_lower : omega*Fintype.card V≤Fintype.card U
  hubs_upper : Fintype.card U≤Fintype.card V
  spoke_intersections : ∃ (ps qs:Bool→U→ℝ) (deltaSp Dexc:ℝ),
    (∀ j,SparseIntersectionData (if j then HK else H₀) (ps j) (qs j) Lsp deltaSp Dexc)∧
    deltaSp+Dexc/(Fintype.card V:ℝ)+1/(Fintype.card U:ℝ)≤delta0
  common_cycles : ∀ u u':U,u≠u'→4*beta*(Fintype.card V:ℝ)^(r+5)≤
    (Fintype.card (CommonMarkedCycle tail head ktail khead (r+4) π (3*d) H₀ HK u u'):ℝ)
  common_paths : ∀ j,∀ Q:BipartiteFourCycle (if j then HK else H₀),
    4*beta*(Fintype.card V:ℝ)^(r+4)≤
    (Fintype.card (CanonicalCommonMarkedPath tail head ktail khead (r+4) π (3*d) H₀ HK
      ((markedRootOrder (r+4) j).symm 0) Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ)
  seed_weights : ∃ ψ:MarkedWheel tail head ktail khead (r+4) π (3*d) H₀ HK→ℝ,
    (∀ e,|markedWheelRimLoad ψ e-1|≤eta0)∧
    (∀ j v u,|markedSpokeResidual ψ j v u|≤eta0)∧
    (∀ W,bminus/(Fintype.card V:ℝ)^(r+4)≤ψ W∧ψ W≤bplus/(Fintype.card V:ℝ)^(r+4))
  ordinary_correction_cut : BipartiteLargeCut (occurrenceMultiplicity tail head) deltaCut (2*hCut)
  marked_correction_cut : BipartiteLargeCut (occurrenceMultiplicity ktail khead) deltaCut (2*hCut)
  ordinary_spoke_cut : BipartiteLargeCut (relationMultiplicity H₀) deltaCut (2*hCut)
  marked_spoke_cut : BipartiteLargeCut (relationMultiplicity HK) deltaCut (2*hCut)

end Oberwolfach
