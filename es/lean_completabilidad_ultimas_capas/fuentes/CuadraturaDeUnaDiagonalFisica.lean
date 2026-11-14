import GeometriaDeLaFibra
import OscilacionEspacialDelPeso
open Set MeasureTheory
open scoped Interval BigOperators
namespace ArticuloA.Historias
open Perfil Trayectoria
noncomputable section

def puntoFila (n j : ℕ) (t : ℝ) := (inicioR n j:ℝ)/n+t
def puntoCol (n j : ℕ) (a : Bool) (t : ℝ) :=
  if a then 1-((inicioC n j:ℝ)/n+t) else (inicioC n j:ℝ)/n+t
def largo (n j : ℕ) : ℝ := (longitudFibra n j:ℝ)/n
def corteOblicuo (p : FactoresContinuos) (n j : ℕ) (a : Bool) (t : ℝ) :=
  pesoContinuo p (puntoFila n j t) (puntoCol n j a t)
def integralOblicua (p : FactoresContinuos) (n j : ℕ) (a : Bool) :=
  ∫ t in (0:ℝ)..largo n j,corteOblicuo p n j a t
def pesoFisico (n : ℕ) (p : FactoresContinuos) (e : Cell n) :=
  pesoContinuo p (medio n e.1.val) (medio n e.2.val)
def gradoOblicuo (n : ℕ) (p : FactoresContinuos) (a : Bool) (j : Indice n) :=
  ∑ e : Fibra n a j,pesoFisico n p e.val

theorem corte_en_el_cuadrado {n} (np : 0<n) (j : Indice n) (a : Bool) {t : ℝ} (ht : t∈Icc 0 (largo n j.val)) :
    puntoFila n j.val t∈unidadCerrada ∧ puntoCol n j.val a t∈unidadCerrada := by
  obtain ⟨_,_,r,c,_,_⟩ := extremos_fibra np j
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have bnd (s : ℕ) (hs : s+longitudFibra n j.val≤n) : (s:ℝ)/n+t∈unidadCerrada := by
    obtain ⟨t0,t1⟩:=ht
    refine ⟨add_nonneg (by positivity) t0,?_⟩
    calc
      _ ≤ (s:ℝ)/n+largo n j.val := add_le_add_left t1 _
      _ ≤ 1 := by rw [largo,←add_div,div_le_one nr]; exact_mod_cast hs
  have cr:=bnd _ r; have cc:=bnd _ c
  refine ⟨cr,?_⟩
  cases a
  · exact cc
  · obtain ⟨c0,c1⟩:=cc
    exact ⟨sub_nonneg.mpr c1,sub_le_self _ c0⟩

theorem centro_de_la_fibra {n} (np : 0<n) (a : Bool) (j : Indice n) (z : Fin (longitudFibra n j.val))
    (p : FactoresContinuos) :
    pesoFisico n p (celdaFibra np a j z).val=corteOblicuo p n j.val a (medio n z.val) := by
  have hc := (extremos_fibra np j).2.2.2.1; have iz:=z.isLt
  have nr : (n:ℝ)≠0 := by exact_mod_cast np.ne'
  unfold pesoFisico corteOblicuo
  congr 1
  · change medio n (inicioR n j.val+z.val)=_
    simp only [medio,puntoFila,Nat.cast_add]; ring
  · change medio n (columnaOrientada n a (inicioC n j.val+z.val))=_
    cases a
    · simp only [medio,columnaOrientada,puntoCol,ite_false,Bool.false_eq_true,Nat.cast_add]; ring
    · simp only [medio,columnaOrientada,puntoCol,ite_true]
      rw [Nat.cast_sub (by omega : inicioC n j.val+z.val≤n-1),
        Nat.cast_sub (by omega : 1≤n),Nat.cast_one,Nat.cast_add]
      field_simp; ring

theorem cuadratura_del_grado_oblicuo {n p κ M L} (hn : 0<n) (data : ControlEspacial p κ M L)
    (m0 : 0≤M) (l0 : 0≤L) (a : Bool) (j : Indice n) :
    |gradoOblicuo n p a j-(n:ℝ)*integralOblicua p n j.val a|≤2*(4*M^3*L) := by
  let m:=longitudFibra n j.val
  let f:=corteOblicuo p n j.val a
  let L₀:=4*M^3*L
  have lp : 0≤L₀ := by dsimp [L₀]; positivity
  have lip : ∀ s∈Icc 0 (largo n j.val),∀ t∈Icc 0 (largo n j.val),|f s-f t|≤(2*L₀)*|s-t| := by
    intro s hs t ht
    obtain ⟨sr,sc⟩:=corte_en_el_cuadrado hn j a hs
    obtain ⟨tr,tc⟩:=corte_en_el_cuadrado hn j a ht
    have q:=variacion_del_peso data l0 _ _ _ _ sr tr sc tc
    have c : |puntoCol n j.val a s-puntoCol n j.val a t|=|s-t| := by
      cases a <;> simp [puntoCol,abs_sub_comm]
    simp only [puntoFila,add_sub_add_left_eq_sub,c] at q
    exact q.trans_eq (by dsimp [L₀]; ring)
  have pos : 0≤2*L₀ := by positivity
  have q:=cuadratura_malla n m hn 0 (1/2) (2*L₀) (by norm_num) (by norm_num) pos f
    (by simpa [largo,m] using continua_de_cota pos lip) (by simpa [largo,m] using lip)
  have u : (m:ℝ)/(n:ℝ)≤1 := (div_le_one (by exact_mod_cast hn)).mpr
    (by exact_mod_cast (extremos_fibra hn j).2.2.2.2.2)
  rw [gradoOblicuo,suma_fibra_fisica hn a j]
  simp_rw [centro_de_la_fibra]
  rw [←Finset.sum_range (fun z : ℕ => corteOblicuo p n j.val a (medio n z))]
  rw [abs_sub_comm]
  apply le_trans _ (mul_le_of_le_one_right pos u)
  simpa only [integralOblicua,largo,m,nodo,medio,zero_add,f,L₀] using q
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.centro_de_la_fibra
#print axioms ArticuloA.Historias.cuadratura_del_grado_oblicuo
