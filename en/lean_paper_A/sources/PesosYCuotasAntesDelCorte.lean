import CoordenadasFisicasDeLaRegion
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita
noncomputable section

def totalIni (n h : ℕ) (p : FactoresContinuos) := masaN p (initial n h)/(n:ℝ≥0)^2
def gradoIni (n h : ℕ) (p : FactoresContinuos) (j : Vertex) := gradoN p (initial n h) j/(n:ℝ≥0)
def famIni (n h : ℕ) (p : FactoresContinuos) (i : Fin 4) := familiaN p h (initial n h) i/(n:ℝ≥0)
def cuotaR (n h : ℕ) := (↑(n-h):ℝ≥0)/n
def cuotaV (n h : ℕ) := (↑((2*n-1)-(n-h)):ℝ≥0)/n
def relojIni (n : ℕ) := (↑(2*n-1):ℝ≥0)/n
def probLinea (n h : ℕ) (p : FactoresContinuos) (j : Vertex) := cuotaR n h*gradoIni n h p j/totalIni n h p
def probArista (n h : ℕ) (p : FactoresContinuos) (e : Cell n) := cuotaR n h*vInicial p e/totalIni n h p

theorem cotas_reloj_y_cuotas {n : ℕ} (hn : 2≤n) (h : ℕ) :
    1≤relojIni n ∧ relojIni n≤2 ∧ cuotaR n h≤1 ∧ 1/2≤cuotaV n h ∧ cuotaR n h+cuotaV n h=relojIni n := by
  have np : 0<(n:ℝ≥0) := by exact_mod_cast (by omega : 0<n)
  have bound : n-h≤2*n-1 := by omega
  unfold relojIni cuotaR cuotaV
  refine ⟨(one_le_div np).mpr (by exact_mod_cast (by omega : n≤2*n-1)),
    (div_le_iff₀ np).mpr (by exact_mod_cast (by omega : 2*n-1≤2*n)),
    (div_le_one np).mpr (by exact_mod_cast Nat.sub_le n h),?_,?_⟩
  · apply (le_div_iff₀ np).mpr
    have d : (n:ℝ≥0)≤2*(↑((2*n-1)-(n-h)):ℝ≥0) := by exact_mod_cast (by omega : n≤2*((2*n-1)-(n-h)))
    exact_mod_cast (show (1/2:ℝ)*(n:ℝ)≤((2*n-1)-(n-h):ℕ) by
      have r : (n:ℝ)≤2*(↑((2*n-1)-(n-h)):ℝ) := by exact_mod_cast d
      linarith)
  · rw [←add_div,←Nat.cast_add,Nat.add_sub_of_le bound]

theorem suelo_total_fisico {n h p κ m L} (hn : 0<n) (sp : ControlEspacial p (κ:ℝ≥0) (m:ℝ≥0) L) :
    κ^4≤totalIni n h p := by
  have np : 0<(n:ℝ≥0) := by exact_mod_cast hn
  apply (le_div_iff₀ (pow_pos np 2)).mpr
  change ((κ^4*(n:ℝ≥0)^2:ℝ≥0):ℝ)≤(masaN p (initial n h):ℝ)
  simpa only [masa_cuando_empieza,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_natCast] using
    (show ((κ^4*(n:ℝ≥0)^2:ℝ≥0):ℝ)≤(masaN p (initial n h):ℝ) by
      rw [masa_cuando_empieza]; exact masa_inferior sp κ.property)

theorem cota_de_un_peso {n p κ m L} (sp : ControlEspacial p (κ:ℝ≥0) (m:ℝ≥0) L) (e : Cell n) :
    vInicial p e≤m^4 := (limites_del_producto sp κ.property _ _ (medio_admisible e.1.isLt)
      (medio_admisible e.2.isLt)).2

theorem carga_identificada {n h p} (hn : 0<n) (i : Fin 4) (j : Indice n) :
    (probLinea n h p (i,j.val):ℝ)=cargaLinea n (n-h) p i j := by
  unfold probLinea cuotaR gradoIni totalIni gradoN cargaLinea
  simp only [NNReal.coe_div,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_natCast,grado_inicial_del_proceso,masa_cuando_empieza]
  rw [show (↑(auxDegree masas (initial n h) (vInicial p) (i,j.val)):ℝ)=gradoInicial n p i j from grado_inicial_del_proceso p i j]
  have np : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  by_cases w : Wfisico n p=0
  · simp [w]
  · field_simp; ring

theorem grado_normalizado_acotado {n h p κ m L} (hn : 0<n) (sp : ControlEspacial p (κ:ℝ≥0) (m:ℝ≥0) L)
    (X : State n) (j : Vertex) :
    gradoN p X j/(n:ℝ≥0)≤m^4 ∧ gradoIni n h p j≤m^4 := by
  have np : 0<(n:ℝ≥0) := by exact_mod_cast hn
  have bound (Y : State n) : gradoN p Y j/(n:ℝ≥0)≤m^4 :=
    (div_le_iff₀ np).mpr (by simpa only [mul_comm] using grado_controlado_por_la_fibra p Y j _ (cota_de_un_peso sp))
  exact ⟨bound X,bound _⟩

theorem cargas_acotadas {n h p κ m L} (hn : 2≤n) (sp : ControlEspacial p (κ:ℝ≥0) (m:ℝ≥0) L)
    (kp : 0<κ) (j : Vertex) (e : Cell n) :
    probLinea n h p j≤m^4/κ^4 ∧ probArista n h p e≤m^4/κ^4 := by
  have pos : 0<n := by omega
  have low := suelo_total_fisico (h:=h) pos sp
  have qr := (cotas_reloj_y_cuotas hn h).2.2.1
  have divs (q : ℝ≥0) (bound : q≤m^4) : cuotaR n h*q/totalIni n h p≤m^4/κ^4 := by
    exact div_le_div₀ (zero_le _) ((mul_le_mul_right' qr q).trans (by simpa using bound)) (pow_pos kp 4) low
  exact ⟨divs _ (grado_normalizado_acotado (h:=h) pos sp (initial n h) j).2,divs _ (cota_de_un_peso sp e)⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cargas_acotadas
