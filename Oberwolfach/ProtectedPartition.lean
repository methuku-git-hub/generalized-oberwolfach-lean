module

public import Oberwolfach.NormalizedDemands
public import Oberwolfach.RegularPartition

@[expose] public section

/-!
The deterministic prescribed-degree construction and redistribution in
`lem:family:partition`. `M a` is a colour class of directed edge
multiplicities. `L a ≤ M a` consists of the edges allowed to be deleted.
The cut inequalities concern `L`, not the larger graph `M`.
-/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- Correct all colour-class degrees while retaining every protected edge.
The last four inequalities control the numbers of removed and added arcs
separately, at both endpoints. The input cut inequalities are exactly those
needed for the integral prescribed-degree theorem. -/
theorem protectedBipartiteRegularPartition
    {V : Type*} [Fintype V] [DecidableEq V] (k q : ℕ) (m : Fin k → ℕ)
    (M L : Fin k → V → V → ℕ)
    (hq : ∀ a, q ≤ m a)
    (hL : ∀ a x y, L a x y ≤ M a x y)
    (hout : ∀ x, ∑ a, ∑ y, M a x y = ∑ a, m a)
    (hin : ∀ y, ∑ a, ∑ x, M a x y = ∑ a, m a)
    (hlowout : ∀ a x, m a - q ≤ ∑ y, M a x y)
    (hlowin : ∀ a y, m a - q ≤ ∑ x, M a x y)
    (hcut : ∀ a (S T : Finset V),
      (∑ x ∈ S, ((∑ y, M a x y) - (m a - q))) ≤
        (∑ y ∈ T, ((∑ x, M a x y) - (m a - q))) +
        ∑ x, ∑ y, if x ∈ S ∧ y ∉ T then L a x y else 0) :
    ∃ P : Fin k → V → V → ℕ,
      (∀ x y, ∑ a, P a x y = ∑ a, M a x y) ∧
      (∀ a x, ∑ y, P a x y = m a) ∧
      (∀ a y, ∑ x, P a x y = m a) ∧
      (∀ a x y, M a x y - L a x y ≤ P a x y) ∧
      (∀ a x, ∑ y, (M a x y - P a x y) ≤
        (∑ y, M a x y) - (m a - q)) ∧
      (∀ a y, ∑ x, (M a x y - P a x y) ≤
        (∑ x, M a x y) - (m a - q)) ∧
      (∀ a x, ∑ y, (P a x y - M a x y) ≤ q) ∧
      (∀ a y, ∑ x, (P a x y - M a x y) ≤ q) ∧
      (∀ x y, (∀ a, L a x y = 0) → ∀ a, P a x y = M a x y) := by
  classical
  let f a x := (∑ y, M a x y) - (m a - q)
  let g a y := (∑ x, M a x y) - (m a - q)
  have hfg (a : Fin k) : ∑ x, f a x = ∑ y, g a y := by
    dsimp [f, g]
    rw [Finset.sum_tsub_distrib _ (fun x _ => hlowout a x),
      Finset.sum_tsub_distrib _ (fun y _ => hlowin a y)]
    rw [Finset.sum_comm]
  have hex (a : Fin k) : ∃ T : V → V → ℕ,
      (∀ x y, T x y ≤ L a x y) ∧
      (∀ x, ∑ y, T x y = f a x) ∧
      (∀ y, ∑ x, T x y = g a y) :=
    bipartite_prescribedMultiplicity (L a) (f a) (g a) (hfg a) (hcut a)
  choose T hTcap hTout hTin using hex
  have hTM (a : Fin k) (x y : V) : T a x y ≤ M a x y :=
    (hTcap a x y).trans (hL a x y)
  let C a x y := M a x y - T a x y
  have hCout (a : Fin k) (x : V) : ∑ y, C a x y = m a - q := by
    dsimp [C]
    rw [Finset.sum_tsub_distrib _ (fun y _ => hTM a x y), hTout]
    dsimp [f]
    exact Nat.sub_sub_self (hlowout a x)
  have hCin (a : Fin k) (y : V) : ∑ x, C a x y = m a - q := by
    dsimp [C]
    rw [Finset.sum_tsub_distrib _ (fun x _ => hTM a x y), hTin]
    dsimp [g]
    exact Nat.sub_sub_self (hlowin a y)
  have hm : ∑ a, (m a - q) + k * q = ∑ a, m a := by
    calc
      _ = (∑ a, (m a - q)) + ∑ _ : Fin k, q := by simp
      _ = ∑ a, (m a - q + q) := (Finset.sum_add_distrib).symm
      _ = _ := by simp [Nat.sub_add_cancel (hq _)]
  have hfout (x : V) : ∑ a, f a x = k * q := by
    dsimp [f]
    rw [Finset.sum_tsub_distrib _ (fun a _ => hlowout a x), hout]
    omega
  have hgin (y : V) : ∑ a, g a y = k * q := by
    dsimp [g]
    rw [Finset.sum_tsub_distrib _ (fun a _ => hlowin a y), hin]
    omega
  let N x y := ∑ a, T a x y
  have hNout (x : V) : ∑ y, N x y = k * q := by
    dsimp [N]
    rw [Finset.sum_comm]
    simp only [hTout, hfout]
  have hNin (y : V) : ∑ x, N x y = k * q := by
    dsimp [N]
    rw [Finset.sum_comm]
    simp only [hTin, hgin]
  obtain ⟨Q, hQsum, hQout, hQin⟩ :=
    regularBipartite_groupedDecomposition k q N hNout hNin
  let P a x y := C a x y + Q a x y
  have hremove (a : Fin k) (x y : V) : M a x y - P a x y ≤ T a x y := by
    dsimp [P, C]
    omega
  have hadd (a : Fin k) (x y : V) : P a x y - M a x y ≤ Q a x y := by
    dsimp [P, C]
    omega
  refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [P, Finset.sum_add_distrib, hQsum, N]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    exact Nat.sub_add_cancel (hTM a x y)
  · intro a x
    simp only [P, Finset.sum_add_distrib, hCout, hQout]
    exact Nat.sub_add_cancel (hq a)
  · intro a y
    simp only [P, Finset.sum_add_distrib, hCin, hQin]
    exact Nat.sub_add_cancel (hq a)
  · intro a x y
    have ht := hTcap a x y
    dsimp [P, C]
    omega
  · intro a x
    calc
      _ ≤ ∑ y, T a x y := Finset.sum_le_sum (fun y _ => hremove a x y)
      _ = _ := hTout a x
  · intro a y
    calc
      _ ≤ ∑ x, T a x y := Finset.sum_le_sum (fun x _ => hremove a x y)
      _ = _ := hTin a y
  · intro a x
    calc
      _ ≤ ∑ y, Q a x y := Finset.sum_le_sum (fun y _ => hadd a x y)
      _ = _ := hQout a x
  · intro a y
    calc
      _ ≤ ∑ x, Q a x y := Finset.sum_le_sum (fun x _ => hadd a x y)
      _ = _ := hQin a y
  · intro x y hzero a
    have ht (b : Fin k) : T b x y = 0 := by
      have hb := hTcap b x y
      rw [hzero b] at hb
      omega
    have hqsum : ∑ b, Q b x y = 0 := by
      rw [hQsum]
      simp [N, ht]
    have hqa : Q a x y = 0 := by
      have hb := Finset.single_le_sum (fun b _ => Nat.zero_le (Q b x y))
        (Finset.mem_univ a)
      rw [hqsum] at hb
      omega
    simp [P, C, ht, hqa]

/-- The deterministic part of the protected regular partition, expressed
on the original simple graph. `Z` specifies pairs whose colour must remain
unchanged. All capacity cuts are imposed after excluding protected edges.
The discrepancy is the degree of the symmetric difference with the
original colour class. -/
theorem protectedRegularPartition
    {n k q : ℕ} {e : ℝ} (G : SimpleGraph (Fin n)) (m : Fin k → ℕ)
    (M L : Fin k → Fin n → Fin n → ℕ) (Z : Fin n → Fin n → Prop)
    (hq : ∀ a, q ≤ m a)
    (hL : ∀ a x y, L a x y ≤ M a x y)
    (hphysical : ∀ x y, (∑ a, M a x y) + (∑ a, M a y x) =
      if G.Adj x y then 1 else 0)
    (hout : ∀ x, ∑ a, ∑ y, M a x y = ∑ a, m a)
    (hin : ∀ y, ∑ a, ∑ x, M a x y = ∑ a, m a)
    (hlowout : ∀ a x, m a - q ≤ ∑ y, M a x y)
    (hlowin : ∀ a y, m a - q ≤ ∑ x, M a x y)
    (hupout : ∀ a x, ((∑ y, M a x y : ℕ) : ℝ) ≤ m a + e)
    (hupin : ∀ a y, ((∑ x, M a x y : ℕ) : ℝ) ≤ m a + e)
    (hcut : ∀ a (S T : Finset (Fin n)),
      (∑ x ∈ S, ((∑ y, M a x y) - (m a - q))) ≤
        (∑ y ∈ T, ((∑ x, M a x y) - (m a - q))) +
        ∑ x, ∑ y, if x ∈ S ∧ y ∉ T then L a x y else 0)
    (hZ : ∀ a x y, Z x y → L a x y = 0 ∧ L a y x = 0) :
    ∃ H : Fin k → SimpleGraph (Fin n),
      EdgePartition G H ∧ (∀ a, (H a).IsRegularOfDegree (2 * m a)) ∧
      (∀ a x y, Z x y → ((H a).Adj x y ↔ 0 < M a x y + M a y x)) ∧
      (∀ a x, ((Finset.univ.filter (fun y =>
        Xor ((H a).Adj x y) (0 < M a x y + M a y x))).card : ℝ) ≤ 4 * q + 2 * e) := by
  classical
  obtain ⟨P, hPsum, hPout, hPin, _, hremout, hremin, haddout, haddin, hfixed⟩ :=
    protectedBipartiteRegularPartition k q m M L hq hL hout hin hlowout hlowin hcut
  obtain ⟨H, hH, hHdeg, hHadj⟩ := regularPartition_of_orientedMultiplicities G P m
    (by simpa only [hPsum] using hphysical) hPout hPin
  refine ⟨H, hH, hHdeg, ?_, ?_⟩
  · intro a x y hz
    rw [hHadj, hfixed x y (fun b => (hZ b x y hz).1),
      hfixed y x (fun b => (hZ b x y hz).2)]
  · intro a x
    have hpoint (y : Fin n) :
        (if Xor ((H a).Adj x y) (0 < M a x y + M a y x) then 1 else 0 : ℕ) ≤
          (M a x y - P a x y) + (M a y x - P a y x) +
          (P a x y - M a x y) + (P a y x - M a y x) := by
      rw [hHadj]
      split_ifs with hh
      · rcases hh with ⟨hp, hm⟩ | ⟨hp, hm⟩ <;> omega
      · omega
    have hremovedout : ((∑ y, (M a x y - P a x y) : ℕ) : ℝ) ≤
        ((∑ y, M a x y : ℕ) : ℝ) - ((m a : ℝ) - q) := by
      have hh : ((∑ y, (M a x y - P a x y) : ℕ) : ℝ) ≤
          (((∑ y, M a x y) - (m a - q) : ℕ) : ℝ) := by
        exact_mod_cast hremout a x
      simpa only [Nat.cast_sub (hlowout a x), Nat.cast_sub (hq a)] using hh
    have hremovedin : ((∑ y, (M a y x - P a y x) : ℕ) : ℝ) ≤
        ((∑ y, M a y x : ℕ) : ℝ) - ((m a : ℝ) - q) := by
      have hh : ((∑ y, (M a y x - P a y x) : ℕ) : ℝ) ≤
          (((∑ y, M a y x) - (m a - q) : ℕ) : ℝ) := by
        exact_mod_cast hremin a x
      simpa only [Nat.cast_sub (hlowin a x), Nat.cast_sub (hq a)] using hh
    have haddedout : ((∑ y, (P a x y - M a x y) : ℕ) : ℝ) ≤ q := by
      exact_mod_cast haddout a x
    have haddedin : ((∑ y, (P a y x - M a y x) : ℕ) : ℝ) ≤ q := by
      exact_mod_cast haddin a x
    have hnat : (Finset.univ.filter (fun y =>
        Xor ((H a).Adj x y) (0 < M a x y + M a y x))).card ≤
        (∑ y, (M a x y - P a x y)) + (∑ y, (M a y x - P a y x)) +
        (∑ y, (P a x y - M a x y)) + (∑ y, (P a y x - M a y x)) := by
      rw [Finset.card_filter, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun y _ => hpoint y)
    have hreal : ((Finset.univ.filter (fun y =>
        Xor ((H a).Adj x y) (0 < M a x y + M a y x))).card : ℝ) ≤
        ((∑ y, (M a x y - P a x y) : ℕ) : ℝ) + ((∑ y, (M a y x - P a y x) : ℕ) : ℝ) +
        ((∑ y, (P a x y - M a x y) : ℕ) : ℝ) + ((∑ y, (P a y x - M a y x) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have huo := hupout a x
    have hui := hupin a x
    linarith

/-- Deterministic completion from the actual large-cut and near-degree
estimates in the protected-partition proof. This discharges the auxiliary
prescribed-degree cut inequalities, rather than assuming them. It does not
assert the probabilistic event producing the initial orientation and cuts. -/
theorem protectedRegularPartition_of_largeCuts
    {n k q : ℕ} {e : ℝ} (G : SimpleGraph (Fin n)) (m : Fin k → ℕ)
    (M L : Fin k → Fin n → Fin n → ℕ) (Z : Fin n → Fin n → Prop)
    (δ h : Fin k → ℝ)
    (hn : 0 < n) (he : 0 ≤ e) (heq : e < q)
    (hq : ∀ a, q ≤ m a)
    (hL : ∀ a x y, L a x y ≤ M a x y)
    (hphysical : ∀ x y, (∑ a, M a x y) + (∑ a, M a y x) =
      if G.Adj x y then 1 else 0)
    (hout : ∀ x, ∑ a, ∑ y, M a x y = ∑ a, m a)
    (hin : ∀ y, ∑ a, ∑ x, M a x y = ∑ a, m a)
    (hnearout : ∀ a x, (m a : ℝ) - e ≤ ((∑ y, M a x y : ℕ) : ℝ) ∧
      ((∑ y, M a x y : ℕ) : ℝ) ≤ m a + e)
    (hnearin : ∀ a y, (m a : ℝ) - e ≤ ((∑ x, M a x y : ℕ) : ℝ) ∧
      ((∑ x, M a x y : ℕ) : ℝ) ≤ m a + e)
    (hδ : ∀ a, 0 ≤ δ a ∧ δ a < 1 / 4)
    (hmargin : ∀ a, 2 * e / ((q : ℝ) - e) ≤ δ a)
    (hcapacity : ∀ a, (q : ℝ) + e ≤ h a * n / 2)
    (hlarge : ∀ a (S T : Finset (Fin n)),
      1 - 2 * δ a < (S.card : ℝ) / n + (T.card : ℝ) / n →
      h a * n * n * min ((S.card : ℝ) / n) ((T.card : ℝ) / n) ≤
        ((∑ x, ∑ y, if x ∈ S ∧ y ∈ T then L a x y else 0 : ℕ) : ℝ))
    (hZ : ∀ a x y, Z x y → L a x y = 0 ∧ L a y x = 0) :
    ∃ H : Fin k → SimpleGraph (Fin n),
      EdgePartition G H ∧ (∀ a, (H a).IsRegularOfDegree (2 * m a)) ∧
      (∀ a x y, Z x y → ((H a).Adj x y ↔ 0 < M a x y + M a y x)) ∧
      (∀ a x, ((Finset.univ.filter (fun y =>
        Xor ((H a).Adj x y) (0 < M a x y + M a y x))).card : ℝ) ≤ 4 * q + 2 * e) := by
  classical
  have hlowout (a : Fin k) (x : Fin n) : m a - q ≤ ∑ y, M a x y := by
    have hb := (hnearout a x).1
    have hc : ((m a - q : ℕ) : ℝ) ≤ ((∑ y, M a x y : ℕ) : ℝ) := by
      rw [Nat.cast_sub (hq a)]
      linarith
    exact_mod_cast hc
  have hlowin (a : Fin k) (y : Fin n) : m a - q ≤ ∑ x, M a x y := by
    have hb := (hnearin a y).1
    have hc : ((m a - q : ℕ) : ℝ) ≤ ((∑ x, M a x y : ℕ) : ℝ) := by
      rw [Nat.cast_sub (hq a)]
      linarith
    exact_mod_cast hc
  let f a x := (∑ y, M a x y) - (m a - q)
  let g a y := (∑ x, M a x y) - (m a - q)
  have hfg (a : Fin k) : ∑ x, f a x = ∑ y, g a y := by
    dsimp [f, g]
    rw [Finset.sum_tsub_distrib _ (fun x _ => hlowout a x),
      Finset.sum_tsub_distrib _ (fun y _ => hlowin a y), Finset.sum_comm]
  have hf (a : Fin k) (x : Fin n) :
      (q : ℝ) - e ≤ (f a x : ℝ) ∧ (f a x : ℝ) ≤ q + e := by
    dsimp [f]
    rw [Nat.cast_sub (hlowout a x), Nat.cast_sub (hq a)]
    have hb := hnearout a x
    constructor <;> linarith [hb.1, hb.2]
  have hg (a : Fin k) (y : Fin n) :
      (q : ℝ) - e ≤ (g a y : ℝ) ∧ (g a y : ℝ) ≤ q + e := by
    dsimp [g]
    rw [Nat.cast_sub (hlowin a y), Nat.cast_sub (hq a)]
    have hb := hnearin a y
    constructor <;> linarith [hb.1, hb.2]
  have hcut (a : Fin k) := intervalDemands_cut (L a) (f a) (g a)
    (by simpa using hn) he heq (hδ a).1 (hδ a).2 (hmargin a)
    (by simpa using hcapacity a) (hfg a) (hf a) (hg a)
    (by simpa using hlarge a)
  exact protectedRegularPartition G m M L Z hq hL hphysical hout hin hlowout hlowin
    (fun a x => (hnearout a x).2) (fun a y => (hnearin a y).2) hcut hZ

end Oberwolfach
