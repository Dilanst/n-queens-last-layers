import BandasDeLasDiagonalesDelTestigoDEF
import AdjuncionDeLaDensidadTrasladada
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
open scoped Interval

def densidadTestigo (z : ℝ×ℝ) := testigoDEF34 z.1 z.2

theorem densidad_testigo_continua : Continuous densidadTestigo :=
  continuous_const.sub ((continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_fst))).mul
    (Real.continuous_cos.comp (continuous_const.mul continuous_snd)))

theorem seccion_fisica_del_testigo (a : Bool) {d : ℝ} (hd : d∈Icc (-1:ℝ) 1) :
    cargaDeFranja densidadTestigo (if a then 2 else 1) (if a then d+1 else d)=proyeccionDelTestigo a d := by
  let f:=fun r=>testigoDEF34 r (colOblicua a r d)
  obtain ⟨le,sub⟩:=extremos_de_la_seccion hd
  unfold cargaDeFranja
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc]
  calc _ = ∫ r in Icc (0:ℝ) 1,(Icc (inicioFibra d) (finFibra d)).indicator f r := by
             apply setIntegral_congr_fun measurableSet_Icc
             intro r hr
             have iff : r-d∈unidadCerrada ↔ d∈ventana r := by
               change (0≤r-d ∧ r-d≤1) ↔ r-1≤d ∧ d≤r
               constructor <;> rintro ⟨l,h⟩ <;> constructor <;> linarith
             have opp : d+1-r∈unidadCerrada ↔ d∈ventana r := by
               change (0≤d+1-r ∧ d+1-r≤1) ↔ r-1≤d ∧ d≤r
               constructor <;> rintro ⟨l,h⟩ <;> constructor <;> linarith
             cases a <;> simp [Set.indicator,enLaFranja,columnaEnFibra,iff,opp,pertenencia_de_la_seccion hr,
               f,colOblicua,densidadTestigo,show 1-(r-d)=d+1-r by ring]
       _ = ∫ r in inicioFibra d..finFibra d,f r := recorte_de_intervalos le sub f
       _ = ∫ t in (0:ℝ)..1-|d|,f (inicioFibra d+t) := by
             rw [intervalIntegral.integral_comp_add_left]; simp [finFibra,add_comm]
       _ = _ := by
             apply intervalIntegral.integral_congr; intro t _
             have c : inicioFibra d+t-d=t+max (-d) 0 := by
               by_cases pos : 0≤d
               · simp [inicioFibra,max_eq_left pos,max_eq_right (neg_nonpos.mpr pos)]
               · have neg:=le_of_not_ge pos
                 simp [inicioFibra,max_eq_right neg,max_eq_left (neg_nonneg.mpr neg)]; ring
             dsimp only [f,colOblicua]; rw [c,show inicioFibra d+t=t+max d 0 by unfold inicioFibra; ring]

def marginalDelTestigo : Fin 4→ℝ→ℝ
  | 0,_ => 1 | 1,_ => 1 | 2,s=>proyeccionDelTestigo false s | 3,s=>proyeccionDelTestigo true (s-1)

theorem pruebas_continuas_con_el_testigo (i : Fin 4) (w : ℝ→ℝ) (wc : Continuous w) :
    (∫ z,densidadTestigo z*w (coord i z) ∂cuadrado) = ∫ s,marginalDelTestigo i s*w s ∂marginalRef i := by
  have ref0 : marginalRef 0=unidad := Measure.restrict_congr_set Ioc_ae_eq_Icc
  have ref1 : marginalRef 1=unidad := Measure.restrict_congr_set Ioc_ae_eq_Icc
  have ob (a : Bool) : (∫ z,densidadTestigo z*w (coord (indiceDeLaSeccion a) z) ∂cuadrado)=
      ∫ s,marginalDelTestigo (indiceDeLaSeccion a) s*w s ∂marginalRef (indiceDeLaSeccion a) := by
    rw [adjuncion_de_diagonal_extendida _ _ densidad_testigo_continua wc a]
    have ref : marginalRef (indiceDeLaSeccion a)=(if a then anti else diag) := by
      cases a <;> exact Measure.restrict_congr_set Ioc_ae_eq_Icc
    rw [←ref]; apply integral_congr_ae
    filter_upwards [linea_en_dominio (indiceDeLaSeccion a)] with s hs
    apply congrArg (· * w s)
    cases a
    · exact seccion_fisica_del_testigo false hs
    · have hd : s-1∈Icc (-1:ℝ) 1 := by change 0≤s ∧ s≤2 at hs; constructor <;> linarith [hs.1,hs.2]
      simpa only [Bool.true_eq,if_true,sub_add_cancel,marginalDelTestigo,indiceDeLaSeccion] using seccion_fisica_del_testigo true hd
  fin_cases i
  · change (∫ z,densidadTestigo z*w z.1 ∂cuadrado)=∫ s,1*w s ∂marginalRef 0
    rw [adjuncion_de_fila_extendida _ _ densidad_testigo_continua wc,ref0]
    exact integral_congr_ae (Eventually.of_forall (fun s=>congrArg (·*w s) (transversales_unitarias_del_testigo s).1))
  · have rev:=integral_prod_swap (μ:=unidad) (ν:=unidad) (fun z : ℝ×ℝ=>densidadTestigo z*w z.2)
    change (∫ z,densidadTestigo z.swap*w z.1 ∂cuadrado)=(∫ z,densidadTestigo z*w z.2 ∂cuadrado) at rev
    change (∫ z,densidadTestigo z*w z.2 ∂cuadrado)=∫ s,1*w s ∂marginalRef 1
    rw [←rev,adjuncion_de_fila_extendida (fun z=>densidadTestigo z.swap) w (densidad_testigo_continua.comp continuous_swap) wc,ref1]
    exact integral_congr_ae (Eventually.of_forall (fun s=>congrArg (·*w s) (transversales_unitarias_del_testigo s).2))
  · exact ob false
  · exact ob true
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.densidad_testigo_continua
#print axioms ArticuloA.Historias.seccion_fisica_del_testigo
#print axioms ArticuloA.Historias.pruebas_continuas_con_el_testigo
