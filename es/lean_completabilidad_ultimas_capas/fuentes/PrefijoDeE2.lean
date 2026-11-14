import EntropiaDelTableroLleno
namespace ArticuloA.Historias
open Trayectoria.E2
noncomputable section
open Classical
variable {n q : ℕ}

def jugada : Pieza n → Choice n
  | .real e => .real e
  | .virtual a => .virtual a

def estado (H : Historia n q) (h : ℕ) : ℕ → State n
  | 0 => initial n h
  | t+1 => if ht : t<2*n-1 then next (estado H h t) (jugada (secuencia H ⟨t,ht⟩)) else estado H h t

private theorem activar (x : State n) (v : Pieza n) (i : Fin 4) (j : ℕ) :
    (next x (jugada v)).active i j = (x.active i j && (j != edgeOf v i)) := by
  cases v <;> rfl

theorem activo_prefijo (H : Historia n q) (h t : ℕ) (i : Fin 4) (j : ℕ) :
    (estado H h t).active i j = true ↔ ∀ s : Indice n, s.val<t → edgeOf (secuencia H s) i ≠ j := by
  induction t with
  | zero => simp [estado,initial]
  | succ t ih =>
    by_cases ht : t<2*n-1
    · rw [estado,dif_pos ht,activar,Bool.and_eq_true_iff,ih]
      constructor
      · rintro ⟨before,last⟩ s hs
        by_cases early : s.val<t
        · exact before s early
        · have eq : s=⟨t,ht⟩ := Fin.ext (by change s.val=t; omega)
          subst s
          exact Ne.symm (by simpa using last)
      · intro all
        refine ⟨fun s hs => all s (by omega),?_⟩
        simpa using Ne.symm (all ⟨t,ht⟩ (by simp))
    · rw [estado,dif_neg ht,ih]
      constructor
      · intro old s _; exact old s (by have hs := s.isLt; omega)
      · intro old s hs; exact old s (by omega)

theorem legal_en_el_nucleo (H : Historia n q) (h : ℕ) (t : Indice n) (a : Candidata n) :
    Trayectoria.E2.available (estado H h t.val) (numeros a) = true ↔ disponibleEn H t a := by
  rw [Trayectoria.E2.available,List.all_eq_true,activa_antes_del_paso]
  constructor
  · intro ok i s hs eq
    have active := (activo_prefijo H h t.val i (numeros a i)).mp (ok i (List.mem_finRange i))
    exact active s hs (congrArg Fin.val eq)
  · intro ok i _
    apply (activo_prefijo H h t.val i (numeros a i)).mpr
    intro s hs eq
    exact ok i s hs (Fin.ext eq)

theorem siguiente_disponible (H : Historia n q) (h : ℕ) (t : Indice n) :
    Trayectoria.E2.available (estado H h t.val) (edgeOf (secuencia H t)) = true :=
  (legal_en_el_nucleo H h t (tupla H t)).2 (pieza_disponible H t)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.activo_prefijo
#print axioms ArticuloA.Historias.siguiente_disponible
