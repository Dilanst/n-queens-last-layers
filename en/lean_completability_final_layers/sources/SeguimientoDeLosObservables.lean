import PerdidaDeLasCuatroCoordenadas
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section

def lectura {n} (p : FactoresContinuos) (h : ℕ) (X : State n) :=
  observed masas (·⁻¹) (vInicial p) (coloresDelPerfil n h p) X

def blanco {n} (p : FactoresContinuos) (h : ℕ) (c : Coord) (z : ℝ≥0) :=
  lectura (n:=n) p h (initial n h) c*z^(ordenFisico c)

def coordenadaViva {n} (X : State n) : Coord→Prop
  | .degree j => activeLine X j
  | _ => True

theorem lectura_de_cuota {n} (p : FactoresContinuos) (h : ℕ) (X : State n) :
    lectura p h X .realCount=X.reals := ns_real _
theorem lectura_del_tablero {n} (p : FactoresContinuos) (h : ℕ) (X : State n) :
    lectura p h X .boardWeight=masaN p X/n := by
  simp only [lectura,observed,Trayectoria.E2.Regular.norm,ns_real]; exact inv_mul_eq_div _ _

theorem lectura_inicial_acotada {n h p κ m L} (hn : 0<n) (hh : h≤n)
    (sp : ControlEspacial p (κ:ℝ≥0) (m:ℝ≥0) L) (m1 : 1≤m) (c : Coord) :
    lectura p h (initial n h) c≤(n:ℝ≥0)*(1+m^4+2*m) := by
  cases c with
  | realCount =>
    rw [lectura_de_cuota]; change (↑(n-h):ℝ≥0)≤_
    calc _ ≤ (n:ℝ≥0)*1 := by rw [mul_one]; exact_mod_cast Nat.sub_le n h
         _ ≤ _ := mul_le_mul_left' (by exact (le_self_add : (1:ℝ≥0)≤1+m^4).trans le_self_add) _
  | degree j =>
    exact (grado_controlado_por_la_fibra p _ j _ (cota_de_un_peso sp)).trans
      (mul_le_mul_left' ((le_add_self : m^4≤1+m^4).trans le_self_add) _)
  | family i => exact (masa_virtual_acotada hn hh sp m1 _ i).trans (mul_le_mul_left' le_add_self _)
  | boardWeight =>
    rw [lectura_del_tablero]
    have np : 0<(n:ℝ≥0) := by exact_mod_cast hn
    apply (div_le_iff₀ np).mpr
    calc _ ≤ (n:ℝ≥0)^2*m^4 := masa_viva_acotada _ sp
         _ = ((n:ℝ≥0)*m^4)*n := by ring
         _ ≤ _ := mul_le_mul_right' (mul_le_mul_left' ((le_add_self : m^4≤1+m^4).trans le_self_add) _) _

private theorem desnormalizar {Y V z E s : ℝ≥0} (nz : s≠0)
    (h : within masas (Y/s) ((V/s)*z) (E/s)) : within masas Y (V*z) E := by
  have q:=scale masas s h
  change within masas (s*(Y/s)) (s*((V/s)*z)) (s*(E/s)) at q
  have cancel (a : ℝ≥0) : s*(a/s)=a := by field_simp
  rw [←mul_assoc,cancel,cancel,cancel] at q; exact q

theorem lectura_cerca_del_blanco {n h p z E} {X : State n} (hn : 0<n)
    (reg : Seguimiento h p X z E) (c : Coord) (live : coordenadaViva X c) :
    within masas (lectura p h X c) (blanco (n:=n) p h c z) E := by
  have nz : (n:ℝ≥0)≠0 := by exact_mod_cast hn.ne'
  cases c with
  | realCount =>
    simp only [blanco,lectura_de_cuota,ordenFisico,pow_one]
    exact desnormalizar nz reg.piezas
  | degree j => exact desnormalizar nz (reg.grados j live)
  | family i => simpa only [blanco,ordenFisico,pow_one] using desnormalizar nz (reg.virtual i)
  | boardWeight =>
    simp only [blanco,lectura_del_tablero,ordenFisico]
    apply desnormalizar nz
    simpa only [div_div,←pow_two,totalIni] using reg.masa

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.lectura_inicial_acotada
#print axioms ArticuloA.Historias.lectura_cerca_del_blanco
