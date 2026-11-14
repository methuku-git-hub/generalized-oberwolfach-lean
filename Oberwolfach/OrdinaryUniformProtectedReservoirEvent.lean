module

public import Oberwolfach.OrdinaryAllTerminalSampleProtected

@[expose] public section
/-! A uniform absorber event implies a fixed reservoir for every admissible
terminal graph, with explicit budgets chosen before the host size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryUniformProtectedReservoirEvent (r m t f a b:ℕ) (ε:ℝ)
    (Q F:SimpleGraph V) (H:V→U→Prop):Prop :=
  ∀(A Z Wterm W:Finset V) (Bterm B:Finset U),
    A=Finset.univ\Z → (Z.card:ℝ)≤ε*Fintype.card V →
    Wterm.card+Bterm.card≤t → Wterm⊆W → Bterm⊆B →
    W.card≤f → (B.card:ℝ)≤ε*Fintype.card V+f →
    ∃C:Finset (Sym2 V⊕(V×U)),C⊆ordinaryHostResources Q H ∧
      Disjoint C (ordinaryRootResources Z B) ∧
      (ordinaryResourceRows C).card≤2^(t*t)*a ∧ (ordinaryResourceHubs C).card≤2^(t*t)*b ∧
      ordinaryResourceRows C⊆Wterm∪A ∧ HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) C ∧
      ∀(G:SimpleGraph V) (Hs:V→U→Prop),
        ordinaryHostResources G Hs⊆ordinaryRootResources Wterm Bterm →
        (ordinaryPhysicalGraph G Hs).support.toFinset.card≤m →
        (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) →
        (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card) →
        G≤Q → (∀v u,Hs v u→H v u) →
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources G Hs) C

theorem ordinary_uniform_absorbers_imply_protected_reservoir_event
    (r m t f a b:ℕ) (ε:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (hAbs:∀(G':SimpleGraph V) (H':V→U→Prop) (A' Z' W':Finset V) (B':Finset U),
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m →
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) →
      G'≤Q → (∀v u,H' v u→H v u) →
      (∀u,(∃v,H' v u)→u∈B') →
      A'=Finset.univ\Z' → (Z'.card:ℝ)≤ε*Fintype.card V →
      W'.card≤f+2^(t*t)*a+2^(t*t)*b →
      (B'.card:ℝ)≤ε*Fintype.card V+((f+2^(t*t)*a+2^(t*t)*b:ℕ):ℝ) →
      ∃C:Finset (Sym2 V⊕(V×U)),
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources G' H') C ∧
        C⊆ordinaryHostResources Q H ∧
        (ordinaryResourceRows C).card≤a ∧ (ordinaryResourceHubs C).card≤b ∧
        ordinaryResourceRows C⊆G'.support.toFinset∪A' ∧
        (∀v∈ordinaryResourceRows C,v∈W'→v∈G'.support.toFinset) ∧
        (∀u∈ordinaryResourceHubs C,u∈B'→u∈Finset.univ.filter (fun u=>∃v,H' v u)) ∧
        Disjoint C (ordinaryRootResources W' B')):
    OrdinaryUniformProtectedReservoirEvent r m t f a b ε Q F H:=by
  intro A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB
  let L:ℕ:=2^(t*t)
  let f₀:ℕ:=f+L*a+L*b
  let γ:ℝ:=ε*Fintype.card V+f
  have hWterm:Wterm.card≤t:=by omega
  have hExp:Wterm.card*Wterm.card+Wterm.card*Bterm.card≤t*t:=by
    have hh:=Nat.mul_le_mul hWterm hsize
    simpa only [Nat.mul_add] using hh
  have hL:2^(Wterm.card*Wterm.card+Wterm.card*Bterm.card)≤L:=
    Nat.pow_le_pow_right (by norm_num) hExp
  have hw:f+L*a≤f₀:=by dsimp [f₀];omega
  have hb:γ+L*b≤ε*Fintype.card V+f₀:=by
    have ha:(0:ℝ)≤(L:ℝ)*a:=by positivity
    dsimp [γ,f₀]
    push_cast
    linarith
  apply ordinary_all_terminal_reservoir_protecting_inner_pair r m f a b f₀ γ ε Q F H
    A Z Wterm W Bterm B hA hZ hWW hBB hW hB L hL hw hb
  simpa only [f₀,L] using hAbs
end Oberwolfach
