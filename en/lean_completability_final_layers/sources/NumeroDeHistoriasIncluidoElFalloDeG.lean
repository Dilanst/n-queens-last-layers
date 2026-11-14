import SoporteDeLasHistoriasDelProcesoGuiado
namespace ArticuloA.Historias
open Repair Trayectoria Trayectoria.ProfileKernel Trayectoria.Adjunto RealFinita
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem grado_de_ramificacion_de_G {n} (np : 0<n) (ρ : Cell n→ℝ≥0) (q t : ℕ) (x : EstadoGuiado n) :
    (pasoDeG ρ q t x).length≤n^2 := by
  have pos : 1≤n^2:=Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ np.ne')
  cases x with
  | none => exact pos
  | some l =>
    simp only [pasoDeG]
    unfold ProfileKernel.choose
    split
    · exact pos
    · simp only [List.length_map,opcionesGuiadas]
      apply (List.length_filter_le _ _).trans
      exact (board_card n).le.trans_eq (pow_two n).symm

private theorem largo_de_union_de_sucesores {X Y : Type} (f : X→List Y) (m : ℕ)
    (cap : ∀ x,(f x).length≤m) (xs : List X) : (xs.flatMap f).length≤xs.length*m := by
  induction xs with
  | nil=>simp
  | cons x tail ih=>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
    simpa [Nat.add_comm] using Nat.add_le_add (cap x) ih

theorem numero_de_rutas_de_G {n} (np : 0<n) (ρ : Cell n→ℝ≥0) (q j t : ℕ) (x : EstadoGuiado n) :
    (rutas (pasoDeG ρ q) t j x).length≤(n^2)^j := by
  induction j generalizing t x with
  | zero=>simp [rutas,point]
  | succ j ih=>
    dsimp only [rutas,bindAtoms]
    apply (largo_de_union_de_sucesores _ ((n^2)^j) _ _).trans
    · rw [pow_succ (n^2) j,Nat.mul_comm ((n^2)^j) (n^2)]
      exact Nat.mul_le_mul_right ((n^2)^j) (grado_de_ramificacion_de_G np ρ q t x)
    · intro a
      simpa only [List.length_map] using ih (t+1) a.2

theorem cota_del_numero_de_historias_malas {n q} (np : 0<n) (ρ : Cell n→ℝ≥0)
    (b : Finset (List (EstadoGuiado n)))
    (inLaw : ∀ l∈b,∃ w,(w,l)∈rutas (pasoDeG ρ q) 0 q (some [])) :
    b.card≤n^(2*q) := by
  let xs:=rutas (pasoDeG ρ q) 0 q (some [])
  have sub : b⊆(xs.map Prod.snd).toFinset := by
    intro l hl
    obtain ⟨w,hw⟩:=inLaw l hl
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(w,l),hw,rfl⟩)
  calc
    b.card ≤ (xs.map Prod.snd).toFinset.card := Finset.card_le_card sub
    _ ≤ (xs.map Prod.snd).length := List.toFinset_card_le _
    _ = xs.length := List.length_map _
    _ ≤ (n^2)^q := numero_de_rutas_de_G np ρ q q 0 (some [])
    _ = _ := (pow_mul n 2 q).symm
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cota_del_numero_de_historias_malas
