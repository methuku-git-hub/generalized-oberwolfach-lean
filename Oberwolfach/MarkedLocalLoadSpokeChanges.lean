module

public import Oberwolfach.MarkedLocalSpokeLoadVortex
public import Oberwolfach.TypedMarkedPotentialDegreeStability

@[expose] public section

/-! Local potential-load transfer with the actual normalized successor
weights. The normalization and parent coefficients stay fixed; all
spoke roots, including absent spokes, keep their root indicator omitted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def MarkedLocalSpokeLoadsWithSpokes (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ)
    (D p k s₀ : ℝ) (weight : (Fin (m+1)→V)→ℝ) (η : ℝ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop) : Prop :=
  let seed := fun W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
    (fun (_ : V) (_ : U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
  ∀ a : Bool×V×U,|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H (Sum.inr a)-1|≤η

theorem markedLocalSpokeLoads_spoke_changes (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ)
    (hm : 3≤m) (hn : 0<Fintype.card V) (D τ A B : ℝ)
    (hDlo : (Fintype.card V:ℝ)/2≤D) (hDhi : D≤2*Fintype.card V)
    (p k s₀ pstar : ℝ) (hpstar : 0<pstar) (hp : pstar≤p) (hk : pstar≤k) (hs : pstar≤s₀)
    (hp1 : p≤1) (hk1 : k≤1) (hs1 : s₀≤1) (hB : 0≤B)
    (weight : (Fin (m+1)→V)→ℝ) (hw : SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (a : Γ) (j : Color) (ε δ : ℝ) (hδ : 0≤δ) (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hraw : RawMarkedLocalSpokeLoads P π d m D p k s₀ weight a j ε σ)
    (hrow : ∀ b x,(∑ u,if ¬(rawMarkedPairSpokes π d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤δ)
    (hcol : ∀ b u,(∑ x,if ¬(rawMarkedPairSpokes π d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤δ) :
    MarkedLocalSpokeLoadsWithSpokes P π d m D p k s₀ weight
      (ε+5*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*δ/Fintype.card V) σ H := by
  let seed := fun W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
    (fun (_ : V) (_ : U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
  have hseed := fun W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_ : V) (_ : U)=>True) (fun _ _=>True)=>successor_seed_nonneg_upper hw (by omega) hn hDlo hDhi
    p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB W.1.val
  intro z
  have hc := typedMarkedPotentialLoad_spoke_degree_stability hm hn seed (2*B/pstar^(2*m+1))
    (by positivity) hseed (rawMarkedPairRims P π d σ) (rawMarkedPairRims P π d σ)
    (rawMarkedPairSpokes π d σ a j) H δ hδ
    (by intro x;simpa using hδ) (by intro x;simpa using hδ)
    (by intro b x;convert hrow b x using 1;apply Finset.sum_congr rfl;intro u hu;unfold bipAdj;split_ifs <;> rfl)
    (by intro b u;convert hcol b u using 1;apply Finset.sum_congr rfl;intro x hx;unfold bipAdj;split_ifs <;> rfl)
    z.1 z.2.1 z.2.2
  have hh := abs_sub_le (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H (Sum.inr z))
    (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ a j) (Sum.inr z)) 1
  exact hh.trans ((add_le_add hc (hraw z)).trans_eq (by ring))

end Oberwolfach
