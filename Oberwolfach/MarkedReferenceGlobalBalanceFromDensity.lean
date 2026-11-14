module

public import Oberwolfach.MarkedReferenceNeighbourhoodGlobalBalance
public import Oberwolfach.MarkedGlobalBalanceFromDegrees
public import Oberwolfach.MarkedReferenceStatisticsSampleDegrees
public import Oberwolfach.MarkedNeighbourhoodSingleSpokeDegrees

@[expose] public section
/-! Reference statistics and singleton retained-spoke tests imply all four
global near-balance estimates required by marked sparse correction. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_neighbourhood_balance_from_density
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h m:ℕ) (hh:1≤h)
    (g:Γ) (j:Color) (D ρ ε δ γ t₀ errR errI η:ℝ)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hq:∀u,q u g=t₀) (hs:∀u,s u j=(m:ℝ)*t₀)
    (hsize:ρ*D=2*Fintype.card U)
    (hstats:MarkedReferenceStatistics P π d g j D ε δ γ (ρ*((m:ℝ)*t₀)/2) (ρ*t₀/2) ((m:ℝ)*t₀) t₀ σ)
    (hrows:MarkedRowsWithSpokes P π d h Finset.univ (ρ*((m:ℝ)*t₀)/2) (ρ*t₀/2) q s g j errR σ H)
    (hindices:MarkedIndicesWithSpokes π d h Finset.univ q s g j errI σ H)
    (hbudget:2*(ε*Fintype.card V)+2*errI≤η*Fintype.card V)
    (hmarked:ε*Fintype.card V+errI≤η*Fintype.card V)
    (hcolumn:((m:ℝ)+1)*errR≤η*Fintype.card V):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    (∀v,|occurrenceDegree (Sum.elim tail ktail) v-
      (∑u,if H false v u then (1:ℝ) else 0)-(∑u,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card V) ∧
    (∀v,|occurrenceDegree (Sum.elim head khead) v-
      (∑u,if H false v u then (1:ℝ) else 0)-(∑u,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card V) ∧
    (∀v,|occurrenceDegree khead v-(∑u,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card V) ∧
    (∀u,|(∑v,if H false v u then (1:ℝ) else 0)-(m:ℝ)*(∑v,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card V) :=by
  have hp:(ρ*((m:ℝ)*t₀)/2)*D=((m:ℝ)*t₀)*Fintype.card U:=by
    calc
      _ = ((m:ℝ)*t₀)*(ρ*D)/2 := by ring
      _ = _ := by rw [hsize]; ring
  have hk:(ρ*t₀/2)*D=t₀*Fintype.card U:=by
    calc
      _ = t₀*(ρ*D)/2 := by ring
      _ = _ := by rw [hsize]; ring
  exact marked_reference_and_neighbourhood_global_balance P π d h m hh g j D ε δ γ
    (ρ*((m:ℝ)*t₀)/2) (ρ*t₀/2) ((m:ℝ)*t₀) t₀ errR errI η q s σ H hq hs hp hk rfl
    hstats hrows hindices hbudget hmarked hcolumn
end Oberwolfach
