module

public import Oberwolfach.OrdinaryIsolatorConfigurations
public import Oberwolfach.TransferConfigurationCounts

@[expose] public section
/-! Isolator and transfer configurations inject into larger actual rim and
spoke hosts without changing their labels or forbidden-pair conditions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryIsolatorHostMonotone (P Q Q' F:SimpleGraph V) (H H':V→U→Prop) (k:ℕ) (θ α:ℝ) (x y:V)
    (hQ:Q≤Q') (hH:∀v u,H v u→H' v u)
    (C:OrdinaryIsolatorConfiguration P Q F H k θ α x y):OrdinaryIsolatorConfiguration P Q' F H' k θ α x y where
  hub:=C.hub
  vertices:=C.vertices
  endpoints:=C.endpoints
  rim_edges:=C.rim_edges.trans hQ
  spokes:=fun v hv=>hH v C.hub (C.spokes v hv)
  independent:=C.independent
  density:=C.density

theorem ordinary_isolator_host_count_mono (P Q Q' F:SimpleGraph V) (H H':V→U→Prop) (k:ℕ) (θ α:ℝ) (x y:V)
    (hQ:Q≤Q') (hH:∀v u,H v u→H' v u):
    Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y)≤
      Fintype.card (OrdinaryIsolatorConfiguration P Q' F H' k θ α x y):=by
  apply Fintype.card_le_of_injective (ordinaryIsolatorHostMonotone P Q Q' F H H' k θ α x y hQ hH)
  intro A B he
  apply OrdinaryIsolatorConfiguration.encoding_injective
  exact congrArg (fun C=>(C.hub,C.vertices)) he

def ordinaryTransferHostMonotone (Q Q' F:SimpleGraph V) (H H':V→U→Prop) (r:ℕ) (hr:3≤r) (v:V) (u u':U)
    (hQ:Q≤Q') (hH:∀x a,H x a→H' x a)
    (C:OrdinaryTransferConfiguration hr Q F H v u u'):OrdinaryTransferConfiguration hr Q' F H' v u u' where
  labels:=C.labels
  omitted:=C.omitted
  rim_edges:=fun j x y he=>hQ (C.rim_edges j he)
  spokes:=fun z hz=>⟨hH z u (C.spokes z hz).1,hH z u' (C.spokes z hz).2⟩
  independent:=C.independent

theorem ordinary_transfer_host_count_mono (Q Q' F:SimpleGraph V) (H H':V→U→Prop) (r:ℕ) (hr:3≤r) (v:V) (u u':U)
    (hQ:Q≤Q') (hH:∀x a,H x a→H' x a):
    Fintype.card (OrdinaryTransferConfiguration hr Q F H v u u')≤
      Fintype.card (OrdinaryTransferConfiguration hr Q' F H' v u u'):=by
  apply Fintype.card_le_of_injective (ordinaryTransferHostMonotone Q Q' F H H' r hr v u u' hQ hH)
  intro A B he
  apply OrdinaryTransferConfiguration.labels_injective
  exact congrArg (fun C=>(C.labels:Fin r×Fin r→V)) he
end Oberwolfach
