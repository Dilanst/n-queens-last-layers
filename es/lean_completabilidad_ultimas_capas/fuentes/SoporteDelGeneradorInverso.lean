import NacimientoDeLasFuentesInversas
import ErrorDelGeneradorPorRaiz
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.Adjunto Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

def fuentesDeUnaMarca {n} (X : State n) (ocupada : Bool) := if ocupada then queens X.physical else board n
def pesoDeUnaFuente (n : ℕ) (ocupada : Bool) : ℝ≥0 := if ocupada then 1 else (n:ℝ≥0)⁻¹
def soporteDeParejas {n} (X : State n) (a b j₂ j₃ : Bool) := (grid (fuentesDeUnaMarca X a) (fuentesDeUnaMarca X b)).filter
  (fun m => decide (compatible m.1 m.2 ∧ patronInverso X m.1 m.2 a b j₂ j₃))

private theorem miembro_si_hay_fuente {n} (X : State n) (e : Cell n) (a : Bool) (s : estadoFuente X e a) :
    e∈fuentesDeUnaMarca X a := by cases a <;> first | exact board_complete _ | exact s

theorem miembros_del_soporte {n} (X : State n) (e f : Cell n) (a b j₂ j₃ : Bool) :
    (e,f)∈soporteDeParejas X a b j₂ j₃ ↔ compatible e f ∧ patronInverso X e f a b j₂ j₃ := by
  simp only [soporteDeParejas,List.mem_filter,decide_eq_true_eq]
  refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  exact List.mem_flatMap.mpr ⟨e,miembro_si_hay_fuente X e a h.2.1,
    List.mem_map.mpr ⟨f,miembro_si_hay_fuente X f b h.2.2.1,rfl⟩⟩

private theorem masa_de_una_lista {n} (hn : 0<n) (X : State n) (leg : Legal X.physical) (a : Bool) :
    pesoDeUnaFuente n a*((fuentesDeUnaMarca X a).length:ℝ≥0)≤n := by
  cases a with
  | false =>
    simp only [fuentesDeUnaMarca,pesoDeUnaFuente,if_false,Bool.false_eq_true,board_card,Nat.cast_mul]
    have nz : (n:ℝ≥0)≠0 := by exact_mod_cast hn.ne'
    change (n:ℝ≥0)⁻¹*(n*n)≤n; rw [←mul_assoc,inv_mul_cancel₀ nz,one_mul]
  | true =>
    simp only [fuentesDeUnaMarca,pesoDeUnaFuente,if_true,one_mul]
    have len:=distinct_le _ (List.finRange n) (distinctRows leg) (by intro i _; simp [List.finRange,List.mem_ofFn])
    simp only [List.length_map,List.length_finRange] at len
    exact_mod_cast len

theorem masa_del_soporte_inverso {n} (hn : 0<n) (X : State n) (leg : Legal X.physical) (a b j₂ j₃ : Bool) :
    (pesoDeUnaFuente n a*pesoDeUnaFuente n b)*((soporteDeParejas X a b j₂ j₃).length:ℝ≥0)≤(n:ℝ≥0)^2 := by
  have cardinal {α : Type} (l r : List α) : (grid l r).length=l.length*r.length := by
    induction l with
    | nil => simp [grid]
    | cons v l ih =>
      change ((r.map (fun f => (v,f)))++grid l r).length=_
      simp only [List.length_append,List.length_map,ih,List.length_cons,Nat.succ_mul]; omega
  have upper : ((soporteDeParejas X a b j₂ j₃).length:ℝ≥0) ≤
      ((fuentesDeUnaMarca X a).length:ℝ≥0)*(↑(fuentesDeUnaMarca X b).length:ℝ≥0) := by
    exact_mod_cast (show (soporteDeParejas X a b j₂ j₃).length≤_ from
      (List.length_filter_le _ _).trans_eq (cardinal _ _))
  have each:=mul_le_mul' (masa_de_una_lista hn X leg a) (masa_de_una_lista hn X leg b)
  calc
    _ ≤ _ := mul_le_mul_left' upper _
    _ = _ := mul_mul_mul_comm .. 
    _ ≤ _ := by simpa only [pow_two] using each

theorem cota_de_suma_de_borrados {n} (hn : 0<n) (X : State n) (leg : Legal X.physical)
    (a b j₂ j₃ : Bool) (err : Mark n→ℝ≥0) (D : ℝ≥0)
    (cap : ∀ u∈soporteDeParejas X a b j₂ j₃,(n:ℝ≥0)^2*err u≤D) :
    (pesoDeUnaFuente n a*pesoDeUnaFuente n b)*masas.sum (soporteDeParejas X a b j₂ j₃) err≤D := by
  let l:=soporteDeParejas X a b j₂ j₃
  have np : 0<(n:ℝ≥0)^2 := pow_pos (by exact_mod_cast hn) 2
  have B:=masas.sum_mono l err (fun _ => D/(n:ℝ≥0)^2) (fun u hu => (le_div_iff₀ np).mpr (by rw [mul_comm]; exact cap u hu))
  rw [const_sum,times_m,ns_real] at B
  calc
    _ ≤ _ := mul_le_mul_left' B _
    _ = ((pesoDeUnaFuente n a*pesoDeUnaFuente n b)*(l.length:ℝ≥0))*(D/(n:ℝ≥0)^2) := by change _*(_*_)=_; ac_rfl
    _ ≤ (n:ℝ≥0)^2*(D/(n:ℝ≥0)^2) := mul_le_mul_right' (masa_del_soporte_inverso hn X leg a b j₂ j₃) _
    _ = D := by field_simp

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.miembros_del_soporte
#print axioms ArticuloA.Historias.masa_del_soporte_inverso
#print axioms ArticuloA.Historias.cota_de_suma_de_borrados
