import CoordenadaContinuaDeLasLineas
import IdentificacionDelPerfilFisico
import UnaCotaParaTodasLasCapas
open Set
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Perfil Trayectoria Trayectoria.E2
noncomputable section

def holguraInicial (n h : ℕ) (p : FactoresContinuos) (i : Fin 4) (j : Indice n) :=
  factores (coloresDelPerfil n h p).virtual i j

theorem virtual_de_la_malla (n h : ℕ) (p : FactoresContinuos) (i : Fin 4) (j : Indice n) :
    holguraInicial n h p i j=factores (pesosMalla n (fraccionHuecos n h) p) i j := by
  by_cases hz : h=0
  · subst h
    fin_cases i <;> simp [holguraInicial,coloresDelPerfil,coloresLlenos,fullColors,fraccionHuecos,
      factores,pesosMalla,RealFinita.masas]
  · simp [holguraInicial,coloresDelPerfil,hz,sameColors]

theorem indice_en_intervalo {n} (hn : 0<n) (i : Fin 4) (j : Indice n) (fis : i.val<2 → j.val<n) :
    posicionLinea n j.val i∈rangoF i := by
  fin_cases i
  · exact medio_admisible (fis (by decide))
  · exact medio_admisible (fis (by decide))
  · change oblicuo n (-1) j.val∈Icc (-1) 1
    convert oblicuo_admisible n hn j (-1) using 1; norm_num
  · change oblicuo n 0 j.val∈Icc 0 2
    simpa using oblicuo_admisible n hn j 0

theorem balance_desde_euler_continua {n h : ℕ} {p κ M L b} (hn : 0<n)
    (data : ControlEspacial p κ M L) (kp : 0<κ) (mp : 0≤M) (lp : 0≤L) (bp : 0<b)
    (masa : integralTablero (pesoContinuo p)=((↑(n-h):ℝ)/n)/b)
    (ec : ∀ i,∀ t∈rangoF i,b*integralFisica p i t=1-holguraLinea p (fraccionHuecos n h) i t)
    (cap : ∀ i,∀ t∈rangoF i,holguraLinea p (fraccionHuecos n h) i t≤1)
    (i : Fin 4) (j : Indice n) :
    (n:ℝ)*|cargaLinea n (n-h) p i j+holguraInicial n h p i j-1|≤(4*(4*M^3*L))/κ^4 := by
  rw [virtual_de_la_malla]
  by_cases fis : i.val<2 → j.val<n
  · have posn:=indice_en_intervalo hn i j fis
    have eq : factores (pesosMalla n (fraccionHuecos n h) p) i j =
        holguraLinea p (fraccionHuecos n h) i (posicionLinea n j.val i) := by
      fin_cases i <;> simp [factores,pesosMalla,holguraLinea,posicionLinea,factorF,fis]
    rw [eq]
    refine balance_inicial_E2 hn (Nat.sub_le ..) data kp mp lp b bp masa i j _ ?_ (cap i _ posn) ?_
    · unfold holguraLinea; split_ifs <;> positivity
    · rw [integra_la_linea_correcta hn p i j fis]; exact ec i _ posn
  · push_neg at fis
    have zero (col : Bool) := grado_transversal_ficticio (n:=n) p col j fis.2
    have cut : ¬j.val<n := by omega
    fin_cases i
    · have z : gradoInicial n p 0 j=0 := zero false
      change gradoInicial n p (⟨0,by decide⟩ : Fin 4) j=0 at z
      simp only [cargaLinea,factores,pesosMalla,if_neg cut,NNReal.coe_one,zero_add,sub_self,abs_zero]
      rw [z]
      simp only [mul_zero,zero_div,zero_add,sub_self,abs_zero]
      positivity
    · have z : gradoInicial n p 1 j=0 := zero true
      change gradoInicial n p (⟨1,by decide⟩ : Fin 4) j=0 at z
      simp only [cargaLinea,factores,pesosMalla,if_neg cut,NNReal.coe_one,zero_add,sub_self,abs_zero]
      rw [z]
      simp only [mul_zero,zero_div,zero_add,sub_self,abs_zero]
      positivity
    · exact False.elim ((by decide : ¬(2:Fin 4).val<2) fis.1)
    · exact False.elim ((by decide : ¬(3:Fin 4).val<2) fis.1)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.balance_desde_euler_continua
