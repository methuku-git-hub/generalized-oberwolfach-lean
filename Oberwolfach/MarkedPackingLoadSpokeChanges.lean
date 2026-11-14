module

public import Oberwolfach.MarkedLocalLoadSpokeChanges
public import Oberwolfach.MarkedPackingLoadVortex
public import Oberwolfach.TypedMarkedPotentialDeletion

@[expose] public section

/-! Packing-domain potential loads after arbitrary spoke changes. Inner
hub roots are explicitly embedded in the larger external-root domain.
Both use the same original successor weighting and normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option quotPrecheck false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Z Γ Color : Type} [Fintype V] [Fintype U] [Fintype Z] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U] [DecidableEq Z]

def MarkedPackingLoadsWithSpokes (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ)
    (D p k s₀ : ℝ) (weight : (Fin (m+1)→V)→ℝ) (a : Γ) (j : Color)
    (f : Z→U) (q : U→Γ→ℝ) (s : U→Color→ℝ) (η : ℝ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop) : Prop :=
  MarkedLocalSpokeLoadsWithSpokes P π d m D p k s₀ weight η σ H ∧
  let seed := fun W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
    (fun (_ : V) (_ : Z)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
  ∀ root : ((V×V)⊕(V×V))⊕(Bool×V×Z),
    rawMarkedWheelMarginal P π d p k (fun z=>q (f z)) (fun z=>s (f z)) a j root≠0 →
    |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d (rawMarkedRestrictHubs f σ))
      (fun b x z=>H b x (f z)) root-1|≤η

theorem markedPackingLoads_spoke_changes (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ)
    (hm : 3≤m) (hn : 0<Fintype.card V) (D τ A B : ℝ)
    (hDlo : (Fintype.card V:ℝ)/2≤D) (hDhi : D≤2*Fintype.card V)
    (p k s₀ pstar : ℝ) (hpstar : 0<pstar) (hp : pstar≤p) (hk : pstar≤k) (hs : pstar≤s₀)
    (hp1 : p≤1) (hk1 : k≤1) (hs1 : s₀≤1) (hB : 0≤B)
    (weight : (Fin (m+1)→V)→ℝ) (hw : SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (a : Γ) (j : Color) (f : Z↪U) (hz : Fintype.card Z≤Fintype.card V)
    (q : U→Γ→ℝ) (s : U→Color→ℝ) (ε δ : ℝ) (hδ : 0≤δ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hraw : RawMarkedPackingLoads P π d m D p k s₀ weight a j f q s ε σ)
    (hrow : ∀ b x,(∑ u,if ¬(rawMarkedPairSpokes π d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤δ)
    (hcol : ∀ b u,(∑ x,if ¬(rawMarkedPairSpokes π d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤δ) :
    MarkedPackingLoadsWithSpokes P π d m D p k s₀ weight a j f q s
      (ε+11*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*δ/Fintype.card V) σ H := by
  constructor
  · have hh := markedLocalSpokeLoads_spoke_changes P π d m hm hn D τ A B hDlo hDhi
      p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB weight hw a j ε δ hδ σ H hraw.1 hrow hcol
    intro z
    apply (hh z).trans
    have hnon : 0≤((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*δ/Fintype.card V := by positivity
    convert add_le_add_left (mul_le_mul_of_nonneg_right (show (5:ℝ)≤11 by norm_num) hnon) ε using 1 <;> ring
  · let seed := fun W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_ : V) (_ : Z)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
    have hseed := fun W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun (_ : V) (_ : Z)=>True) (fun _ _=>True)=>successor_seed_nonneg_upper hw (by omega) hn hDlo hDhi
      p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB W.1.val
    have hr (b : Bool) (x : V) :
        (∑ z,bipAdj (fun x z=>¬(rawMarkedPairSpokes π d (rawMarkedRestrictHubs f σ) a j b x z↔H b x (f z))) x z)≤δ := by
      apply le_trans _ (hrow b x)
      have hh := finite_injective_sum_le f f.injective
        (fun u=>if ¬(rawMarkedPairSpokes π d σ a j b x u↔H b x u) then (1:ℝ) else 0)
        (fun _=>by split_ifs <;> norm_num)
      convert hh using 1
      apply Finset.sum_congr rfl
      intro z hz
      simp only [bipAdj,rawMarkedRestrictHubs_spokes]
    have hc (b : Bool) (z : Z) :
        (∑ x,bipAdj (fun x z=>¬(rawMarkedPairSpokes π d (rawMarkedRestrictHubs f σ) a j b x z↔H b x (f z))) x z)≤δ := by
      convert hcol b (f z) using 1
      apply Finset.sum_congr rfl
      intro x hx
      simp only [bipAdj,rawMarkedRestrictHubs_spokes]
    dsimp only
    intro root hroot
    have hchange := typedMarkedPotentialLoad_degree_stability hm hn hz seed (2*B/pstar^(2*m+1))
      (by positivity) hseed (rawMarkedPairRims P π d (rawMarkedRestrictHubs f σ))
      (rawMarkedPairRims P π d (rawMarkedRestrictHubs f σ))
      (rawMarkedPairSpokes π d (rawMarkedRestrictHubs f σ) a j) (fun b x z=>H b x (f z)) δ hδ
      (by intro x;simpa using hδ) (by intro x;simpa using hδ) hr hc root
    have hh := abs_sub_le (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d (rawMarkedRestrictHubs f σ))
      (fun b x z=>H b x (f z)) root)
      (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d (rawMarkedRestrictHubs f σ))
        (rawMarkedPairSpokes π d (rawMarkedRestrictHubs f σ) a j) root) 1
    exact hh.trans ((add_le_add hchange (hraw.2 root hroot)).trans_eq (by ring))

end Oberwolfach
