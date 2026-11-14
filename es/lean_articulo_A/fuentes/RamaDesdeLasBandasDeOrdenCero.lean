import ControlEspacialFisicoDeLasCuatroFamilias
import ConstanteComunHastaElExtremo
import MarginalesDesdeElTableroSinLipschitz
import IdentidadesDeLaDensidadSeparada
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
private theorem normalizacion_como_integral_de_intervalo {p : FactoresContinuos} (g : NormalizacionR15 p)
    (i : Fin 4) (rc : i.val<2) : (∫ s in (0:ℝ)..1,camposFisicos p i s)=1 := by
  have dom : rangoF i=unidadCerrada := by rcases (show i=0 ∨ i=1 by omega) with rfl|rfl <;> rfl
  have ref : (∫ s,campoR15 p i s ∂unidad)=∫ s in (0:ℝ)..1,campoR15 p i s := by
    rw [intervalIntegral.integral_of_le zero_le_one]; exact integral_Icc_eq_integral_Ioc
  apply Eq.trans _ (ref.symm.trans (g i rc)); apply intervalIntegral.integral_congr; intro s hs
  exact (campo_dentro_de_su_intervalo p i (by rw [dom]; simpa only [unidadCerrada,uIcc_of_le (zero_le_one : (0:ℝ)≤1)] using hs)).symm

theorem control_comun_desde_una_rama_medida {P : ℝ→TableroMedido} {p : ℝ→FactoresContinuos} {b : ℝ→ℝ}
    {κ M m lo hi : ℝ} (kp : 0<κ) (mp : 0<m) (mm : 1≤M) (lp : 0<lo)
    (eq : ∀ x∈Icc (0:ℝ) (1/2),EulerFisica (P x) (p x) x.toNNReal (b x))
    (coef : ∀ x∈Icc (0:ℝ) (1/2),b x∈Icc lo hi)
    (cp : ∀ x∈Icc (0:ℝ) (1/2),∀ i,ContinuousOn (camposFisicos (p x) i) (rangoF i))
    (band : ∀ x∈Icc (0:ℝ) (1/2),∀ i,∀ s∈rangoF i,
      if (i:Fin 4).val<2 then m≤camposFisicos (p x) i s ∧ camposFisicos (p x) i s≤M
      else κ≤camposFisicos (p x) i s ∧ camposFisicos (p x) i s≤1)
    (g0 : NormalizacionR15 (p 0)) :
    ∃ L : ℝ,0≤L ∧ ∀ x∈Icc (0:ℝ) (1/2),ControlEspacial (p x) (min m κ) M L := by
  obtain ⟨L,Lp,ub⟩:=constante_comun_en_una_banda_del_normalizador (hi:=hi) (M:=M) lp kp mp
  refine ⟨L,Lp,?_⟩
  intro x hx
  have e:=eq x hx
  have norm : NormalizacionR15 (p x) := by
    rcases eq_or_lt_of_le hx.1 with zero|pos
    · simpa only [←zero] using g0
    · exact normalizacion_R15_en_masa_interior e (Real.toNNReal_pos.mpr pos)
  have row := normalizacion_como_integral_de_intervalo norm 0 (by decide)
  have col := normalizacion_como_integral_de_intervalo norm 1 (by decide)
  have data:=datos_de_traslacion_desde_marginales x.toNNReal (b:=b x) (κ:=κ) (M:=M) (cp x hx)
    (fun i di s hs=>by simpa [if_neg (not_lt.mpr di)] using band x hx i s hs)
    (fun s hs=>(band x hx 1 s hs).2) col (ecuaciones_de_fibra_desde_euler_medida e (cp x hx))
  rw [Real.coe_toNNReal x hx.1] at data
  exact control_espacial_por_euler_y_bandas data hx.1 e.coef kp mp mm (fun s hs=>(band x hx 1 s hs).1)
    (fun s hs=>band x hx 0 s hs) row (ub x hx (b x) (coef x hx))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.control_comun_desde_una_rama_medida
