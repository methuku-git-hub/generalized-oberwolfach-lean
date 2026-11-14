module

public import Oberwolfach.RawMarkedSeedLoadEvent

@[expose] public section

/-! Explicit exponential failure estimates. The locality and coefficient
bounds are fixed before the graph order and the root domains are chosen. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach

def markedLoadExponent (m d : ℕ) (B η : ℝ) : ℝ :=
  2*η^2/((8*(d:ℝ)+6)^2*2*((m:ℝ)+1)^7*B^2)

theorem markedLoadExponent_pos (m d : ℕ) (B η : ℝ) (hB : 0<B) (hη : 0<η) :
    0<markedLoadExponent m d B η := by unfold markedLoadExponent;positivity

theorem marked_load_tail_exponential (m d : ℕ) (B η n : ℝ) (hn : 0<n) :
    2*Real.exp (-2*η^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^4*B/n)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B)))=
      2*Real.exp (-markedLoadExponent m d B η*n) := by
  congr 2
  unfold markedLoadExponent
  field_simp
  <;> ring

theorem marked_root_domain_card {V U : Type} [Fintype V] [Fintype U]
    (hu : Fintype.card U≤Fintype.card V) :
    Fintype.card (((V×V)⊕(V×V))⊕(Bool×V×U))≤4*(Fintype.card V)^2 := by
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool]
  nlinarith [Nat.mul_le_mul_left (Fintype.card V) hu]

theorem marked_external_spoke_domain_card {V U : Type} [Fintype V] [Fintype U]
    (K : ℝ) (hu : (Fintype.card U:ℝ)≤K*Fintype.card V) :
    (Fintype.card (Bool×V×U):ℝ)≤2*K*(Fintype.card V:ℝ)^2 := by
  simp only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith [mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))]

theorem marked_load_failure_bound (m d : ℕ) (B η n J K : ℝ) (hn : 0<n)
    (hJ : J≤K*n^2) :
    J*(2*Real.exp (-2*η^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^4*B/n)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))))≤
      2*K*n^2*Real.exp (-markedLoadExponent m d B η*n) := by
  rw [marked_load_tail_exponential m d B η n hn]
  nlinarith [mul_le_mul_of_nonneg_right hJ (by positivity : 0≤2*Real.exp (-markedLoadExponent m d B η*n))]

end Oberwolfach
