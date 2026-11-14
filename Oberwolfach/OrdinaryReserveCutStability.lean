module

public import Oberwolfach.OrdinaryPhysicalSpokeDegree
public import Oberwolfach.BipartiteNormalizedCutDeletion

@[expose] public section
/-! Deleting a physical reserve reduces ordinary rim and spoke large-cut
coefficients by at most its normalized physical maximum degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_reserve_rim_cut_stability (P:V→V→Prop) (R:SimpleGraph (V⊕U)) (δ h ζ:ℝ)
    (hn:0<Fintype.card V) (hζ:0≤ζ)
    (hR:∀v,(R.degree (Sum.inl v):ℝ)≤ζ*Fintype.card V)
    (hcut:BipartiteLargeCut (relationMultiplicity P) δ h):
    BipartiteLargeCut (relationMultiplicity (fun v w=>P v w∧¬R.Adj (Sum.inl v) (Sum.inl w))) δ (h-ζ):=by
  apply bipartiteLargeCut_after_relation_changes hn hn P _ δ h ζ hζ _ _ hcut
  · intro v
    calc
      _≤∑w,if R.Adj (Sum.inl v) (Sum.inl w) then (1:ℝ) else 0:=by
        apply Finset.sum_le_sum;intro w _
        by_cases hp:P v w <;> by_cases hr:R.Adj (Sum.inl v) (Sum.inl w) <;> simp [hp,hr]
      _=((Finset.univ.filter (fun w=>R.Adj (Sum.inl v) (Sum.inl w))).card:ℝ):=by simp
      _≤R.degree (Sum.inl v):=by exact_mod_cast ordinary_physical_rim_row_le_degree R v
      _≤ζ*Fintype.card V:=hR v
  · intro w
    calc
      _≤∑v,if R.Adj (Sum.inl w) (Sum.inl v) then (1:ℝ) else 0:=by
        apply Finset.sum_le_sum;intro v _
        have he:R.Adj (Sum.inl v) (Sum.inl w)↔R.Adj (Sum.inl w) (Sum.inl v):=R.adj_comm _ _
        by_cases hp:P v w <;> by_cases hr:R.Adj (Sum.inl w) (Sum.inl v) <;> simp [hp,hr,he]
      _=((Finset.univ.filter (fun v=>R.Adj (Sum.inl w) (Sum.inl v))).card:ℝ):=by simp
      _≤R.degree (Sum.inl w):=by exact_mod_cast ordinary_physical_rim_row_le_degree R w
      _≤ζ*Fintype.card V:=hR w

theorem ordinary_reserve_spoke_cut_stability (H:V→U→Prop) (R:SimpleGraph (V⊕U)) (δ h ζ:ℝ)
    (hn:0<Fintype.card V) (hm:0<Fintype.card U) (hζ:0≤ζ)
    (hRrow:∀v,(R.degree (Sum.inl v):ℝ)≤ζ*Fintype.card U)
    (hRcol:∀u,(R.degree (Sum.inr u):ℝ)≤ζ*Fintype.card V)
    (hcut:BipartiteLargeCut (relationMultiplicity H) δ h):
    BipartiteLargeCut (relationMultiplicity (fun v u=>H v u∧¬R.Adj (Sum.inl v) (Sum.inr u))) δ (h-ζ):=by
  apply bipartiteLargeCut_after_relation_changes hn hm H _ δ h ζ hζ _ _ hcut
  · intro v
    calc
      _≤∑u,if R.Adj (Sum.inl v) (Sum.inr u) then (1:ℝ) else 0:=by
        apply Finset.sum_le_sum;intro u _
        by_cases hp:H v u <;> by_cases hr:R.Adj (Sum.inl v) (Sum.inr u) <;> simp [hp,hr]
      _=((Finset.univ.filter (fun u=>R.Adj (Sum.inl v) (Sum.inr u))).card:ℝ):=by simp
      _≤R.degree (Sum.inl v):=by exact_mod_cast ordinary_physical_spoke_row_le_degree R v
      _≤ζ*Fintype.card U:=hRrow v
  · intro u
    calc
      _≤∑v,if R.Adj (Sum.inl v) (Sum.inr u) then (1:ℝ) else 0:=by
        apply Finset.sum_le_sum;intro v _
        by_cases hp:H v u <;> by_cases hr:R.Adj (Sum.inl v) (Sum.inr u) <;> simp [hp,hr]
      _=((Finset.univ.filter (fun v=>R.Adj (Sum.inl v) (Sum.inr u))).card:ℝ):=by simp
      _≤R.degree (Sum.inr u):=by exact_mod_cast ordinary_physical_spoke_column_le_degree R u
      _≤ζ*Fintype.card V:=hRcol u
end Oberwolfach
