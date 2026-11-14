import DesintegracionOblicuaDelTablero
open Set MeasureTheory Filter
open scoped Interval NNReal
namespace ArticuloA.Historias
open Perfil
noncomputable section
open Classical

def indiceDeLaSeccion (anti : Bool) : Fin 4 := if anti then 3 else 2
def ordenadaFisica (anti : Bool) (d : ℝ) := if anti then d+1 else d

private theorem al_parametro_fisico (anti : Bool) (f : ℝ→ℝ) :
    (∫ d in Icc (-1:ℝ) 1,f (ordenadaFisica anti d))=∫ t,f t ∂marginalRef (indiceDeLaSeccion anti) := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1)]
  cases anti
  · exact intervalIntegral.integral_of_le (by norm_num)
  · change (∫ d in (-1:ℝ)..1,f (d+1))=∫ t in Ioc (0:ℝ) 2,f t
    rw [intervalIntegral.integral_comp_add_right]; norm_num [intervalIntegral.integral_of_le]

private theorem seccion_sobre_tablero (anti : Bool) {r d : ℝ} (hw : d∈ventana r) :
    colOblicua anti r d∈unidadCerrada ∧
    coord (indiceDeLaSeccion anti) (r,colOblicua anti r d)=ordenadaFisica anti d := by
  have a:=hw.1; have b:=hw.2
  change r-1≤d at a; change d≤r at b
  cases anti <;> simp [colOblicua,indiceDeLaSeccion,coord,ordenadaFisica,unidadCerrada] <;>
    constructor <;> first | constructor <;> linarith | linarith

private theorem seccion_con_test {p : FactoresContinuos} (b : ℝ) (anti : Bool) (g : ℝ→ℝ)
    {d : ℝ} (hd : d∈Icc (-1) 1) :
    let i:=indiceDeLaSeccion anti
    let F:=fun z : ℝ×ℝ => b*pesoExtendido p z*g (coord i z)
    (∫ r in Icc (0:ℝ) 1,if d∈ventana r then F (r,colOblicua anti r d) else 0)=
      b*integralFisica p i (ordenadaFisica anti d)*g (ordenadaFisica anti d) := by
  intro i F
  let H:=fun r => if d∈ventana r then pesoContinuo p r (colOblicua anti r d) else 0
  have geom : integralFisica p i (ordenadaFisica anti d)=integralDesplazada p d anti := by
    cases anti <;> simp [i,indiceDeLaSeccion,ordenadaFisica,integralFisica]
  rw [geom,←integral_de_la_seccion p anti hd]
  change _=b*(∫ r in Icc (0:ℝ) 1,H r)*_
  rw [←integral_const_mul,←integral_mul_const]
  apply setIntegral_congr_fun measurableSet_Icc; intro r hr
  by_cases hw : d∈ventana r
  · obtain ⟨hc,co⟩:=seccion_sobre_tablero anti hw
    simp [F,H,i,hw,extension_coincide hr hc,co]
  · simp [H,hw]

theorem prueba_de_la_marginal_oblicua {P p x b κ M L} (e : EulerFisica P p x b)
    (sp : ControlEspacial p κ M L) (lp : 0≤L) (anti : Bool) {g : ℝ→ℝ} (gc : Continuous g) :
    let i:=indiceDeLaSeccion anti
    (∫ t,(P.m i t:ℝ)*g t ∂marginalRef i)=∫ t,b*integralFisica p i t*g t ∂marginalRef i := by
  intro i
  let F:=fun z : ℝ×ℝ => b*pesoExtendido p z*g (coord i z)
  have coordc : Continuous (coord i) := by
    cases anti
    · exact continuous_fst.sub continuous_snd
    · exact continuous_fst.add continuous_snd
  have fc : Continuous F := (continuous_const.mul (extension_continua_del_peso sp lp)).mul (gc.comp coordc)
  have support : ∀ᵐ z ∂cuadrado, z.1∈unidadCerrada ∧ z.2∈unidadCerrada := by
    exact tablero_en_dominio
  rw [←adjuncion P.ley i g gc.measurable]
  apply Eq.trans (show (∫ z,(P.ν z:ℝ)*g (coord i z) ∂cuadrado)=∫ z,F z ∂cuadrado from ?_) ?_
  · apply integral_congr_ae; filter_upwards [e.real,support] with z ez hz
    simp only [F,ez,extension_coincide hz.1 hz.2]
  · rw [desintegrar_el_tablero anti fc,←al_parametro_fisico anti (fun t => b*integralFisica p i t*g t)]
    apply setIntegral_congr_fun measurableSet_Icc
    intro d hd; exact seccion_con_test b anti g hd

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.prueba_de_la_marginal_oblicua
