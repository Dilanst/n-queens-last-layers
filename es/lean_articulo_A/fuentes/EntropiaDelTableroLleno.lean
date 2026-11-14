import EntropiaDeLasDosLeyes
open scoped BigOperators
namespace ArticuloA.Historias
open Trayectoria.E2
noncomputable section
open Classical
variable {n q : ℕ}

def lista (H : Historia n q) := (List.finRange (2*n-1)).map (secuencia H)

theorem cobertura_de_la_lista (H : Historia n q) (i : Fin 4) :
    ((lista H).map (fun j => edgeOf j i)).Perm (List.range (2*n-1)) := by
  let perm := H.2.2.trans (cobertura H.1 H.2.1 i)
  have h := (Equiv.Perm.map_finRange_perm perm).map Fin.val
  rw [List.map_coe_finRange] at h
  simpa only [lista,List.map_map] using h

def esReal : Pieza n → Bool | .real _ => true | .virtual _ => false
def palabra (H : Historia n q) : List Bool := (lista H).map esReal

theorem reales_contadas (H : Historia n q) : (palabra H).count true=q := by
  let P := H.1
  let f := fun j : Pieza n => edgeOf j 0
  let L := (lista H).filter esReal
  have nd : ((lista H).map f).Nodup := ((cobertura_de_la_lista H 0).symm.nodup List.nodup_range)
  have nd' : (L.map f).Nodup := nd.sublist ((List.filter_sublist : L.Sublist (lista H)).map f)
  have eqset : (L.map f).toFinset=ocupados P 0 := by
    ext r
    constructor
    · intro hr
      obtain ⟨j,hj,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
      obtain ⟨hl,real⟩ := List.mem_filter.mp hj
      obtain ⟨t,_,ht⟩ := List.mem_map.mp hl
      cases j with
      | real e =>
        have he := (reales_de_la_secuencia H e).1 ⟨t,ht⟩
        exact eq ▸ en_ocupados P e he 0
      | virtual a => contradiction
    · intro hr
      obtain ⟨e,he,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
      obtain ⟨t,ht⟩ := (reales_de_la_secuencia H e).2 he
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨.real e,List.mem_filter.mpr
        ⟨List.mem_map.mpr ⟨t,List.mem_finRange _,ht⟩,rfl⟩,eq⟩)
  have ndP : ((queens P.val).map (fun e => lines e 0)).Nodup :=
    List.pairwise_map.mpr ((legal_y_tamano P).1.imp (fun h => (separadas _ _).mp h 0))
  have size := congrArg Finset.card eqset
  rw [List.toFinset_card_of_nodup nd',List.length_map,ocupados,List.toFinset_card_of_nodup ndP,
    List.length_map,queenLength,(legal_y_tamano P).2] at size
  have cnt (xs : List (Pieza n)) : (xs.map esReal).count true=(xs.filter esReal).length := by
    induction xs with
    | nil => rfl
    | cons e xs ih =>
      cases h : esReal e <;> simp [h,List.count_cons,List.filter_cons,ih]
  exact (cnt (lista H)).trans size

theorem cuotas_de_la_historia (H : Historia n q) :
    productoCuotas (palabra H)=masaPalabra n q := by
  have sum (bs : List Bool) : bs.count false+bs.count true=bs.length := by
    induction bs with
    | nil => rfl
    | cons b bs ih => cases b <;> simp [List.count_cons] <;> omega
  have N : (palabra H).length=2*n-1 := by simp [palabra,lista]
  have all := sum (palabra H)
  rw [reales_contadas,N] at all
  have virt : (palabra H).count false=2*n-1-q := by omega
  rw [cuotas_factoriales,reales_contadas,virt,N,masaPalabra]

theorem ficticia_en_lleno (H : Historia n n) (t : Indice n) {g : Edge}
    (eq : secuencia H t = .virtual g) : n ≤ g 0 ∧ n ≤ g 1 := by
  apply sin_virtual_fisica H.1.val (legal_y_tamano H.1).1 (legal_y_tamano H.1).2 (lista H)
  · intro e he
    obtain ⟨j,real⟩ := (reales_de_la_secuencia H e).2 he
    exact List.mem_map.mpr ⟨j,List.mem_finRange j,real⟩
  · exact cobertura_de_la_lista H
  · exact List.mem_map.mpr ⟨t,List.mem_finRange t,eq⟩

def efectivos (u : Fin 4 → Indice n → ℝ) (i : Fin 4) (j : Indice n) :=
  if i.val<2 ∧ n≤j.val then 1 else u i j
def pesoVirtualCero (u : Fin 4 → Indice n → ℝ) (a : Candidata n) :=
  if n≤(a 0).val ∧ n≤(a 1).val then pesoDe (efectivos u) a else 0
def pesoElegido (H : Historia n n) (u : Fin 4 → Indice n → ℝ) (t : Indice n) :=
  match secuencia H t with
  | .real _ => peso H (efectivos u) t
  | .virtual _ => pesoVirtualCero u (tupla H t)

theorem efectivos_pos (u : Fin 4 → Indice n → ℝ) (hu : ∀ i j,0<u i j) :
    ∀ i j, 0<efectivos u i j := by
  intro i j
  unfold efectivos
  split_ifs
  · exact zero_lt_one
  · exact hu _ _

theorem peso_sobre_el_soporte (H : Historia n n) (u : Fin 4 → Indice n → ℝ) (t : Indice n) :
    pesoElegido H u t=peso H (efectivos u) t := by
  cases eq : secuencia H t with
  | real e => rw [pesoElegido,eq]
  | virtual g =>
    have hg := ficticia_en_lleno H t eq
    have val (i : Fin 4) : (tupla H t i).val=g i := congrArg (fun j => edgeOf j i) eq
    simp only [pesoElegido,eq,pesoVirtualCero,val,hg,and_self,if_true]; rfl

def normalizadorCero (H : Historia n n) (u : Fin 4 → Indice n → ℝ) (t : Indice n) : ℝ :=
  match secuencia H t with
  | .real _ => normalizador H (efectivos u) t
  | .virtual _ => ∑ a : Candidata n, if disponibleEn H t a then pesoVirtualCero u a else 0

theorem normalizadorCero_pos (H : Historia n n) (u : Fin 4 → Indice n → ℝ) (hu : ∀ i j,0<u i j)
    (t : Indice n) : 0<normalizadorCero H u t := by
  have pos (a : Candidata n) : 0 < pesoDe (efectivos u) a :=
    Finset.prod_pos (fun i _ => efectivos_pos u hu i _)
  cases eq : secuencia H t with
  | real e => rw [normalizadorCero,eq]; exact positivo H _ (efectivos_pos u hu) t
  | virtual g =>
    rw [normalizadorCero,eq]
    apply Finset.sum_pos'
    · intro a _
      unfold pesoVirtualCero
      split_ifs <;> first | exact (pos a).le | exact le_rfl
    · refine ⟨tupla H t,Finset.mem_univ _,?_⟩
      have same := peso_sobre_el_soporte H u t
      simp only [pesoElegido,eq] at same
      rw [if_pos (pieza_disponible H t),same]
      exact pos _

def ramaCero (H : Historia n n) (u : Fin 4 → Indice n → ℝ) :=
  masaPalabra n n * ∏ t, pesoElegido H u t / normalizadorCero H u t

theorem identidad_nivel_cero (u : Fin 4 → Indice n → ℝ) (hu : ∀ i j,0<u i j) (hn : 0<count n n) :
    ∑ H : Historia n n, proba n n * Real.log (proba n n / ramaCero H u) =
      (∑ H : Historia n n, proba n n * ∑ t, Real.log (normalizadorCero H u t)) -
      (∑ i, ∑ j, Real.log (efectivos u i j)) - Real.log (count n n) -
      Real.log n.factorial - 4*Real.log (2*n-1-n).factorial := by
  have eq (H : Historia n n) : ramaCero H u=masaRamaCon H (efectivos u) (fun B => normalizadorCero B u) := by
    unfold ramaCero masaRamaCon; simp_rw [peso_sobre_el_soporte]
  simp_rw [eq]
  exact identidad_con_normalizadores _ (fun B t => normalizadorCero_pos B u hu t) _ (efectivos_pos u hu) hn
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.peso_sobre_el_soporte
#print axioms ArticuloA.Historias.normalizadorCero_pos
#print axioms ArticuloA.Historias.identidad_nivel_cero
