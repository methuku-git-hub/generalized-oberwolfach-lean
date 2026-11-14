module

public import Oberwolfach.OrdinaryCommonComponentReservation
public import Oberwolfach.FactorClassAssignment

@[expose] public section
/-! The common reserved components are selected before sampling using
only the original factor class and its abundant length. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_common_reservation (K:ℕ) (hK:0<K) (i₀:Fin K):
    ∃N:ℕ,∀n≥N,∀(U:Type) [Fintype U] [Nonempty U],
      ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
        (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
        (hclass:∀u,factorPreparationClass (F u) K=some i₀),
      let β:ℝ:=1/(2*(K:ℝ))
      let r:=i₀.val+1
      let s₀:=β/100
      let k:=⌊s₀*(n:ℝ)/(r:ℝ)⌋₊
      let s:ℝ:=(r:ℝ)*(k:ℝ)/(n:ℝ);
      s₀/2≤s ∧ s≤s₀ ∧
      ∃C:∀u,Finset (F u).ConnectedComponent,
        (∀u,(C u).card=k) ∧ (∀u c,c∈C u→Fintype.card c=r) ∧
        (∀u,(r:ℝ)*((C u).card:ℝ)=s*n) :=by
  have hK':0<(K:ℝ):=by exact_mod_cast hK
  let β:ℝ:=1/(2*(K:ℝ))
  have hβ:0<β:=by dsimp [β];positivity
  have hβ1:β≤1:=by
    have hK1:1≤(K:ℝ):=by exact_mod_cast hK
    dsimp [β]
    rw [div_le_iff₀ (by positivity : 0<2*(K:ℝ))]
    linarith
  by_cases hr:(3:ℕ) ≤ i₀.val+1
  · obtain ⟨N,hN⟩:=ordinary_common_component_reservation β hβ hβ1 (i₀.val+1) hr
    refine ⟨max N 1,?_⟩
    intro n hn U _ _ F hF Allowed hAllowed hclass β' r s₀ k s
    have hn0:0<n:=by omega
    have hnR:0<(n:ℝ):=by exact_mod_cast hn0
    have hfreq:∀u:U,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=i₀.val+1)).card:ℝ):=by
      intro u
      have hc:=((factor_preparation_class hn0 (F u) (hF u) Allowed (hAllowed u) K hK).2 i₀ (hclass u)).2.2.1
      have hh:β≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=i₀.val+1)).card:ℝ)/n:=
        (Finset.mem_filter.mp hc).2
      exact (le_div_iff₀ hnR).mp hh
    obtain ⟨hl,hu,C,hcard,hsize⟩:=hN n (by omega) U F hfreq
    refine ⟨hl,hu,C,hcard,hsize,?_⟩
    intro u
    have hc:(C u).card=k:=by convert hcard u using 1 <;> congr! 5
    rw [hc]
    change (r:ℝ)*(k:ℝ)=((r:ℝ)*(k:ℝ)/(n:ℝ))*(n:ℝ)
    field_simp
  · refine ⟨1,?_⟩
    intro n hn U _ _ F hF Allowed hAllowed hclass
    obtain ⟨u⟩:=‹Nonempty U›
    have hh:=((factor_preparation_class (by omega) (F u) (hF u) Allowed (hAllowed u) K hK).2 i₀ (hclass u)).1
    exact False.elim (hr hh)
end Oberwolfach
