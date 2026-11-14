module

public import Oberwolfach.OrdinaryEarlyContractionProportionalPlacement
public import Oberwolfach.OrdinaryExactSamplingUnassignedUpper

@[expose] public section

/-! Instantiate the early contraction's expression estimate with the exact
original assigned sampling law, without choosing a new contraction. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_sampling_early_expression
    (α ε:ℝ)
    (hlocal:∀(n:ℕ) (inner θ b a γ u t edit del LF aux:ℝ),
      0 ≤ inner → 0 ≤ θ → min (α/4096) (1/2:ℝ)*θ ≤ b →
      inner≤ε*n → a≤b/16 → γ≤θ → u≤2*θ → t≤θ*inner →
      edit≤b*n/16 → aux≤b*n/16 → del≤b*n/16 → 2*LF≤b*n/16 →
      edit+(max (a*n) (γ*inner)+u*inner+3*t+aux+del+LF)+LF≤b*n)
    {n q K D:ℕ} (hn:0<n) (hD:0<D)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (hK:0<K) (i₀:Fin K) (rsv θ ρ₀ smin:ℝ) (m d:ℕ)
    (hm:7≤m) (hd:2≤d) (hs0:0≤rsv) (hs1:rsv≤1/100)
    (hθ:0<θ) (hθ1:θ≤1/100) (hda:1/θ≤d)
    (hρ₀:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity (Fin q) D)
    (hρhi:initialIndexDensity (Fin q) D≤1)
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (F w) S)
    (hClass:OrdinaryClassReserveBound F hF i₀ rsv)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d)
    (Inner:Finset (Fin n)) (b a γ ζ edit LF:ℝ)
    (hb:min (α/4096) (1/2:ℝ)*θ≤b) (hinner:(Inner.card:ℝ)≤ε*n)
    (ha:a≤b/16) (hγ:γ≤θ) (hζ0:0≤ζ) (hζ:ζ≤θ)
    (hedit:edit≤b*n/16) (haux:((6*d+4:ℕ):ℝ)≤b*n/16) (hLF:2*LF≤b*n/16):
    edit+(max (a*n) (γ*Inner.card)+sampling.u*Inner.card+3*(ζ*Inner.card)+
      (6*d+4:ℕ)+edit+LF)+LF≤b*n :=by
  have hc:8≤(m:ℝ)+1:=by exact_mod_cast (show 8≤m+1 by omega)
  have hρ:0 < initialIndexDensity (Fin q) D:=hρ₀.trans_le hρlo
  have hu:=ordinary_exact_sampling_unassigned_upper hn hD F hF K hK i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρhi S hS hClass sampling
  have hI:0≤(Inner.card:ℝ):=by positivity
  have ht:ζ*Inner.card≤θ*Inner.card:=mul_le_mul_of_nonneg_right hζ hI
  exact hlocal n Inner.card θ b a γ sampling.u (ζ*Inner.card) edit edit LF ((6*d+4:ℕ):ℝ)
    hI hθ.le hb hinner ha hγ hu ht hedit haux hedit hLF
end Oberwolfach
