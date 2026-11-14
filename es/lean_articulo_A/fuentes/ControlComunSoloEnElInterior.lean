import RamaDesdeLasBandasDeOrdenCero
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
theorem control_espacial_en_la_rama_abierta {P : ℝ→TableroMedido} {p : ℝ→FactoresContinuos} {b : ℝ→ℝ}
    {κ M m lo hi : ℝ} (kp : 0<κ) (mp : 0<m) (mm : 1≤M) (lp : 0<lo)
    (eq : ∀ x∈Ioc (0:ℝ) (1/2),EulerFisica (P x) (p x) x.toNNReal (b x))
    (coef : ∀ x∈Ioc (0:ℝ) (1/2),b x∈Icc lo hi)
    (cp : ∀ x∈Ioc (0:ℝ) (1/2),∀ i,ContinuousOn (camposFisicos (p x) i) (rangoF i))
    (band : ∀ x∈Ioc (0:ℝ) (1/2),∀ i,∀ s∈rangoF i,
      if (i:Fin 4).val<2 then m≤camposFisicos (p x) i s ∧ camposFisicos (p x) i s≤M
      else κ≤camposFisicos (p x) i s ∧ camposFisicos (p x) i s≤1) :
    ∃ L : ℝ,0≤L ∧ ∀ x∈Ioc (0:ℝ) (1/2),ControlEspacial (p x) (min m κ) M L := by
  obtain ⟨L,Lp,ub⟩:=constante_comun_en_una_banda_del_normalizador (hi:=hi) (M:=M) lp kp mp
  refine ⟨L,Lp,?_⟩
  intro x hx
  have e:=eq x hx
  have xp:=Real.toNNReal_pos.mpr hx.1
  have data:=datos_de_traslacion_desde_marginales x.toNNReal (b:=b x) (κ:=κ) (M:=M) (cp x hx)
    (fun i di s hs=>by simpa [if_neg (not_lt.mpr di)] using band x hx i s hs)
    (fun s hs=>(band x hx 1 s hs).2) (masa_transversal_reescalada e xp 1 (by decide)) (ecuaciones_de_fibra_desde_euler_medida e (cp x hx))
  rw [Real.coe_toNNReal x hx.1.le] at data
  exact control_espacial_por_euler_y_bandas data hx.1.le e.coef kp mp mm (fun s hs=>(band x hx 1 s hs).1)
    (fun s hs=>band x hx 0 s hs) (masa_transversal_reescalada e xp 0 (by decide))
    (ub x ⟨hx.1.le,hx.2⟩ (b x) (coef x hx))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.control_espacial_en_la_rama_abierta
