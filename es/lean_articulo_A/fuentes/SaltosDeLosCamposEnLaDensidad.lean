import DensidadExtendidaDeEuler
import MonotoniaIntegralDelDualAnclado
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
def saltoLogB33 (F : ℝ→ℝ) (t s : ℝ) := Real.log (F (s+t))-Real.log (F s)
def trasladaFilaB33 (U : ℝ×ℝ→ℝ) (t : ℝ) (z : ℝ×ℝ) := U (z.1+t,z.2)
theorem continuidad_de_la_densidad_trasladada {U : ℝ×ℝ→ℝ} (uc : Continuous U) (t : ℝ) :
    Continuous (trasladaFilaB33 U t) := uc.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)

theorem continuidad_del_salto_de_log {F : ℝ→ℝ} (cf : Continuous F) (pf : ∀ s,0<F s) (t : ℝ) :
    Continuous (saltoLogB33 F t) :=
  ((cf.log (fun s=>(pf s).ne')).comp (continuous_id.add continuous_const)).sub (cf.log (fun s=>(pf s).ne'))

theorem signo_del_salto_de_log {F : ℝ→ℝ} (pf : ∀ s,0<F s) (s t : ℝ) :
    0≤(F (s+t)-F s)*saltoLogB33 F t s := by
  rcases le_total (F s) (F (s+t)) with le|ge
  · exact mul_nonneg (sub_nonneg.mpr le) (sub_nonneg.mpr (Real.log_le_log (pf s) le))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr ge) (sub_nonpos.mpr (Real.log_le_log (pf _) ge))

def cotaInferiorDensidadB33 (x b m κ : ℝ) := b*(1/(x+b))*m*κ*κ

theorem bandas_inferiores_de_los_factores {p x b κ M m} (h : DatosTraslacionFisica p x b κ M)
    (xn : 0≤x) (bp : 0<b) (kp : 0<κ) (mp : 0<m) (cm : ∀ s∈unidadCerrada,m≤(p.columna s:ℝ)) :
    (∀ s,0<filaExteriorB33 p x b s) ∧ (∀ s,m≤campoR15 p 1 s) ∧
    (∀ s,κ≤campoR15 p 2 s) ∧ (∀ s,κ≤campoR15 p 3 s) ∧
    0<cotaInferiorDensidadB33 x b m κ ∧ ∀ z,cotaInferiorDensidadB33 x b m κ≤densidadExteriorB33 p x b z := by
  have rr:=nucleo_y_fila_del_perfil h xn bp kp
  have rp : 0<1/(x+b) := one_div_pos.mpr (add_pos_of_nonneg_of_pos xn bp)
  have col s : m≤campoR15 p 1 s := cm _ (recorte_dentro 1 s)
  have dd s : κ≤campoR15 p 2 s := (h.diagonal 2 (by decide) _ (recorte_dentro 2 s)).1
  have aa s : κ≤campoR15 p 3 s := (h.diagonal 3 (by decide) _ (recorte_dentro 3 s)).1
  refine ⟨fun s=>rp.trans_le (rr.2 s).1,col,dd,aa,by unfold cotaInferiorDensidadB33; positivity,?_⟩
  intro z
  have one:=mul_le_mul_of_nonneg_left (rr.2 z.1).1 bp.le
  have two:=mul_le_mul one (col z.2) mp.le ((mul_pos bp rp).le.trans one)
  have three:=mul_le_mul two (dd (z.1-z.2)) kp.le ((mul_pos (mul_pos bp rp) mp).le.trans two)
  exact mul_le_mul three (aa (z.1+z.2)) kp.le ((mul_pos (mul_pos (mul_pos bp rp) mp) kp).le.trans three)

theorem identidad_logaritmica_de_la_densidad {p : FactoresContinuos} {x b : ℝ} (bp : 0<b)
    (rp : ∀ s,0<filaExteriorB33 p x b s) (cp : ∀ s,0<campoR15 p 1 s)
    (dp : ∀ s,0<campoR15 p 2 s) (ap : ∀ s,0<campoR15 p 3 s) (t : ℝ) (z : ℝ×ℝ) :
    Real.log (densidadExteriorB33 p x b z)+sumaLevantada false (saltoLogB33 (filaExteriorB33 p x b) t)
      (saltoLogB33 (campoR15 p 2) t) (saltoLogB33 (campoR15 p 3) t) z=
      Real.log (trasladaFilaB33 (densidadExteriorB33 p x b) t z) := by
  have expand (w : ℝ×ℝ) : Real.log (densidadExteriorB33 p x b w)=Real.log b+
      Real.log (filaExteriorB33 p x b w.1)+Real.log (campoR15 p 1 w.2)+Real.log (campoR15 p 2 (w.1-w.2))+
      Real.log (campoR15 p 3 (w.1+w.2)) := by
    unfold densidadExteriorB33
    have h1:=mul_pos bp (rp w.1)
    have h2:=mul_pos h1 (cp w.2)
    have h3:=mul_pos h2 (dp (w.1-w.2))
    rw [Real.log_mul h3.ne' (ap _).ne',Real.log_mul h2.ne' (dp _).ne',Real.log_mul h1.ne' (cp _).ne',
      Real.log_mul bp.ne' (rp _).ne']
  unfold trasladaFilaB33
  rw [expand,expand]
  dsimp [sumaLevantada,transversal,saltoLogB33]
  rw [show z.1+t-z.2=z.1-z.2+t by ring,show z.1+t+z.2=z.1+z.2+t by ring]
  ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.continuidad_de_la_densidad_trasladada
#print axioms ArticuloA.Historias.continuidad_del_salto_de_log
#print axioms ArticuloA.Historias.signo_del_salto_de_log
#print axioms ArticuloA.Historias.bandas_inferiores_de_los_factores
#print axioms ArticuloA.Historias.identidad_logaritmica_de_la_densidad
