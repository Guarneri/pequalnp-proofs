import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_474_aux

theorem card_filter_univ_sum {α} [Fintype α] (q : α → Prop) [DecidablePred q] :
    Finset.card (Finset.univ.filter q) = ∑ a : α, (if q a then 1 else 0) := by
  rw [← Finset.sum_filter, Finset.card_eq_sum_ones]

theorem countP_finRange {n : ℕ} (p : Fin n → Bool) :
    (List.finRange n).countP p = Finset.card (Finset.univ.filter (fun v => p v = true : Fin n → Prop)) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.finRange_succ_last, List.countP_append, List.countP_map]
    rw [card_filter_univ_sum, Fin.sum_univ_castSucc, ← card_filter_univ_sum]
    cases hlast : p (Fin.last m) <;> simp [hlast]
    · exact ih (fun v => p (Fin.castSucc v))
    · exact ih (fun v => p (Fin.castSucc v))

theorem length_filterMap_countP {α β : Type _} (g : α → Option β) (l : List α) :
    (l.filterMap g).length = l.countP (fun x => (g x).isSome) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases h : g a with
    | none => simp [h, ih]
    | some b => simp [h, ih]

theorem countP_split {α : Type _} (l : List α) (p q : α → Bool) :
    l.countP p = l.countP (fun x => p x && q x) + l.countP (fun x => p x && !q x) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, ih]
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq] <;> omega

def codePos {n : ℕ} (g : Fin n → Option α) (k : Fin n) : ℕ :=
  (List.finRange n).countP (fun r => (r.val < k.val) && (g r).isSome)

theorem codePos_zero {m : ℕ} (g : Fin (m+1) → Option α) : codePos g 0 = 0 := by
  simp only [codePos]
  rw [List.finRange_succ, List.countP_cons, List.countP_map]
  simp [Function.comp, Fin.val_succ]

theorem codePos_succ {m : ℕ} (g : Fin (m+1) → Option α) (k' : Fin m) :
    codePos g (Fin.succ k') = (if (g 0).isSome then 1 else 0) + codePos (g ∘ Fin.succ) k' := by
  simp only [codePos]
  rw [List.finRange_succ, List.countP_cons, List.countP_map]
  have hhead : ((0 : Fin (m+1))).val < (Fin.succ k').val := by
    simp [Fin.val_succ]
  simp only [decide_eq_true hhead]
  have hcong : List.countP ((fun r => decide (r.val < (Fin.succ k').val) && (g r).isSome) ∘ Fin.succ)
        (List.finRange m)
      = List.countP (fun r : Fin m => decide (r.val < k'.val) && ((g ∘ Fin.succ) r).isSome)
        (List.finRange m) := by
    congr 1
  rw [hcong]
  cases hg0 : (g 0).isSome <;> (simp [hg0] <;> omega)

theorem length_code_succ {m : ℕ} (g : Fin (m+1) → Option α) :
    ((List.finRange (m+1)).filterMap g).length
      = (if (g 0).isSome then 1 else 0) + ((List.finRange m).filterMap (g ∘ Fin.succ)).length := by
  rw [List.finRange_succ, ← List.filterMap_map]
  cases hg0 : g 0 with
  | none => rw [List.filterMap_cons_none hg0]; simp
  | some v => rw [List.filterMap_cons_some hg0]; simp; omega

theorem pos_bound {n : ℕ} (g : Fin n → Option α) (k : Fin n)
    (hk : (g k).isSome) : codePos g k < ((List.finRange n).filterMap g).length := by
  induction n with
  | zero =>
    exfalso
    have := Fin.isLt k
    omega
  | succ m ih =>
    by_cases hh : Fin.val k = 0
    · have hk0 : k = 0 := Fin.val_injective (by simpa using hh)
      subst hk0
      rw [codePos_zero]
      have h1 : ((List.finRange (m+1)).filterMap g).length
          = 1 + ((List.finRange m).filterMap (g ∘ Fin.succ)).length := by
        rw [length_code_succ, if_pos hk]
      omega
    · obtain ⟨k', hk'⟩ : ∃ k' : Fin m, Fin.succ k' = k :=
        ⟨⟨Fin.val k - 1, by omega⟩, Fin.val_injective (by simp [Fin.val_succ]; omega)⟩
      subst hk'
      rw [codePos_succ, length_code_succ]
      have htail := ih (g ∘ Fin.succ) k' (by simpa [Function.comp] using hk)
      omega

theorem exists_of_isSome {α : Type _} {o : Option α} (h : o.isSome) : ∃ v, o = some v := by
  cases o with
  | none => simp at h
  | some v => exact ⟨v, rfl⟩

theorem filterMap_getElemD {n : ℕ} (g : Fin n → Option α) (k : Fin n)
    (hk : (g k).isSome) (d : α) :
    ((List.finRange n).filterMap g).getD (codePos g k) d = (g k).get hk := by
  induction n with
  | zero =>
    exfalso
    have := Fin.isLt k
    omega
  | succ m ih =>
    by_cases hh : Fin.val k = 0
    · have hk0 : k = 0 := Fin.val_injective (by simpa using hh)
      subst hk0
      obtain ⟨v, hv⟩ := exists_of_isSome hk
      rw [codePos_zero, List.finRange_succ, List.filterMap_cons_some hv,
        List.getD_cons_zero]
      simp [hv]
    · obtain ⟨k', hk'⟩ : ∃ k' : Fin m, Fin.succ k' = k :=
        ⟨⟨Fin.val k - 1, by omega⟩, Fin.val_injective (by simp [Fin.val_succ]; omega)⟩
      subst hk'
      rw [codePos_succ]
      have h0 : g 0 = none ∨ ∃ v, g 0 = some v := by
        cases h' : g 0 with
        | none => exact Or.inl rfl
        | some v => exact Or.inr ⟨v, rfl⟩
      rcases h0 with hgn | ⟨v, hv⟩
      · rw [List.finRange_succ, List.filterMap_cons_none hgn, List.filterMap_map,
          if_neg (by simp [hgn]), Nat.zero_add]
        exact ih (g ∘ Fin.succ) k' hk
      · rw [List.finRange_succ, List.filterMap_cons_some hv, List.filterMap_map]
        have hswap : 1 + codePos (g ∘ Fin.succ) k' = codePos (g ∘ Fin.succ) k' + 1 := by
          omega
        rw [if_pos (by simp [hv]), hswap, List.getD_cons_succ]
        exact ih (g ∘ Fin.succ) k' hk

theorem getD_append_left {α : Type _} (d : α) {l1 l2 : List α} {i : ℕ} (h : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  induction l1 generalizing i with
  | nil => exact absurd h (by simp at h)
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i' =>
      simpa [List.getD_cons_succ] using ih
        (by have h2 := h; rw [List.length_cons] at h2; omega)

end PEqualNP.Outside.L_lib_474_aux

open PEqualNP.Outside.L_lib_474_aux

theorem PEqualNP.Outside.L_lib_474 : (∀ n : Nat,
  let V := Fin n
  let Point := V → Bool
  let Clause := Finset (V × Bool)
  let sat := fun (formula : Finset Clause) (x : Point) =>
    ∀ c ∈ formula, ∃ lit ∈ c, x lit.1 = lit.2
  let Order := Equiv.Perm V
  ∀ F : Finset Clause,
    let forced := fun (s : Point) (order : Order) =>
      (Finset.univ : Finset V).filter (fun i =>
        ∃ c ∈ F, (i,s i) ∈ c ∧ ∀ e ∈ c, e = (i,s i) ∨
          ((order e.1).val < (order i).val ∧ s e.1 ≠ e.2))
    let code := fun (s : Point) (order : Order) =>
      (List.finRange n).filterMap (fun rank =>
        let v := order.symm rank
        if v ∈ forced s order then none else some (s v))
    ∀ (order : Order) (s z : Point), sat F s → sat F z →
      (code s order).length + (forced s order).card = n ∧
      ((∃ tail : List Bool, code s order ++ tail = code z order) → s = z)) := by
  intro n V Point Clause sat Order F forced code order s z hs hz
  refine ⟨?_, fun hprefix => ?_⟩

  ·
    have himg : Finset.image order.symm
        (Finset.univ.filter (fun v : Fin n => order.symm v ∈ forced s order))
      = forced s order := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨v, hvS, rfl⟩
        exact hvS.2
      · intro hx
        refine ⟨order x, ⟨Finset.mem_univ _, ?_⟩, Equiv.symm_apply_apply order x⟩
        rw [Equiv.symm_apply_apply]
        exact hx
    have hcards : Finset.card (Finset.univ.filter (fun v : Fin n => order.symm v ∈ forced s order))
        = (forced s order).card := by
      rw [← Finset.card_image_of_injective _ (fun a b hab => Equiv.injective order.symm hab), himg]
    have hc : code s order =
        (List.finRange n).filterMap (fun rank : Fin n =>
          if order.symm rank ∈ forced s order then none else some (s (order.symm rank))) := rfl
    rw [hc, length_filterMap_countP, countP_finRange]
    have hpred : ∀ v ∈ Finset.univ,
        ((fun rank : Fin n => if order.symm rank ∈ forced s order then none
            else some (s (order.symm rank))) v).isSome = true
        ↔ ¬(order.symm v ∈ forced s order) := by
      intro v _
      by_cases h : order.symm v ∈ forced s order <;> simp [h]
    rw [Finset.filter_congr hpred, ← hcards]
    have hcomp := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (p := fun v : Fin n => order.symm v ∈ forced s order)
    rw [Finset.card_univ, Fintype.card_fin] at hcomp
    omega
  ·
    obtain ⟨tail, htail⟩ := hprefix
    let gs : Fin n → Option Bool := fun rank =>
      if order.symm rank ∈ forced s order then none else some (s (order.symm rank))
    let gz : Fin n → Option Bool := fun rank =>
      if order.symm rank ∈ forced z order then none else some (z (order.symm rank))
    have hcs : code s order = (List.finRange n).filterMap gs := rfl
    have hcz : code z order = (List.finRange n).filterMap gz := rfl
    rw [hcs, hcz] at htail

    have hFor : ∀ (pt : Fin n → Bool) (v : Fin n), v ∈ forced pt order ↔
        ∃ c ∈ F, (v, pt v) ∈ c ∧ ∀ e ∈ c, e = (v, pt v) ∨
          ((order e.1).val < (order v).val ∧ pt e.1 ≠ e.2) := by
      intro pt v
      simp only [forced, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hne
    rw [funext_iff] at hne
    push_neg at hne
    obtain ⟨i, hsi⟩ := hne
    classical

    have hexP : ∃ m : ℕ, ∃ r : Fin n, r.val = m ∧ s (order.symm r) ≠ z (order.symm r) :=
      ⟨(order i).val, order i, rfl, by rw [Equiv.symm_apply_apply]; exact hsi⟩
    set m0 := Nat.find hexP with hm0def
    obtain ⟨r0, hr0val, hr0ne⟩ := Nat.find_spec hexP
    have hagree : ∀ v : Fin n, (order v).val < m0 → s v = z v := by
      intro v hv
      by_contra hcon
      exact Nat.find_min hexP hv ⟨order v, rfl,
        by rw [Equiv.symm_apply_apply]; exact hcon⟩

    have hFagree : ∀ v : Fin n, (order v).val < m0 →
        (v ∈ forced s order ↔ v ∈ forced z order) := by
      intro v hv
      have hEq := hagree v hv
      rw [hFor s v, hFor z v]
      constructor
      · rintro ⟨c, hcF, hclit, hcl⟩
        refine ⟨c, hcF, by rw [← hEq]; exact hclit, ?_⟩
        intro e he
        rcases hcl e he with rfl | ⟨hbefore, hlit⟩
        · rw [hEq]
          exact Or.inl rfl
        · exact Or.inr ⟨hbefore, by rw [← hagree e.1 (by omega)]; exact hlit⟩
      · rintro ⟨c, hcF, hclit, hcl⟩
        refine ⟨c, hcF, by rw [hEq]; exact hclit, ?_⟩
        intro e he
        rcases hcl e he with rfl | ⟨hbefore, hlit⟩
        · rw [← hEq]
          exact Or.inl rfl
        · exact Or.inr ⟨hbefore, by rw [hagree e.1 (by omega)]; exact hlit⟩
    have hjm0 : (order (order.symm r0)).val = m0 := by
      rw [Equiv.apply_symm_apply]
      exact hr0val

    have hFsj : ¬ (order.symm r0 ∈ forced s order) := by
      intro hmem
      obtain ⟨c, hcF, hclit, hcl⟩ := (hFor s (order.symm r0)).mp hmem
      have hfals : ∀ e ∈ c, z e.1 ≠ e.2 := by
        intro e he
        rcases hcl e he with rfl | ⟨hbefore, hlit⟩
        · exact fun h => hr0ne h.symm
        · exact fun h => hlit ((hagree e.1 (by omega)).symm ▸ h)
      rcases hz c hcF with ⟨lit, hlitc, hzv⟩
      exact hfals lit hlitc hzv
    have hFzj : ¬ (order.symm r0 ∈ forced z order) := by
      intro hmem
      obtain ⟨c, hcF, hclit, hcl⟩ := (hFor z (order.symm r0)).mp hmem
      have hfals : ∀ e ∈ c, s e.1 ≠ e.2 := by
        intro e he
        rcases hcl e he with rfl | ⟨hbefore, hlit⟩
        · exact hr0ne
        · exact fun h => hlit (hagree e.1 (by omega) ▸ h)
      rcases hs c hcF with ⟨lit, hlitc, hsv⟩
      exact hfals lit hlitc hsv
    have hgss : (gs r0).isSome := by simp [gs, hFsj]
    have hgz : (gz r0).isSome := by simp [gz, hFzj]

    have hposEq : codePos gs r0 = codePos gz r0 := by
      simp only [codePos]
      exact List.countP_congr (fun rr _ => by
        by_cases hrr : rr.val < r0.val
        · have hlt : (order (order.symm rr)).val < m0 := by
            rw [Equiv.apply_symm_apply]
            omega
          simp [gs, gz, hFagree (order.symm rr) hlt]
        · simp [hrr])

    have hpos : codePos gs r0 < ((List.finRange n).filterMap gs).length :=
      pos_bound gs r0 hgss
    have hgsget : gs r0 = some (s (order.symm r0)) := by simp [gs, hFsj]
    have hgzget : gz r0 = some (z (order.symm r0)) := by simp [gz, hFzj]
    have hgets : ((List.finRange n).filterMap gs).getD (codePos gs r0) false
        = s (order.symm r0) := by
      have h0 := filterMap_getElemD gs r0 hgss false
      simp only [gs] at h0
      simp [hFsj] at h0
      exact h0
    have hgetz : ((List.finRange n).filterMap gz).getD (codePos gz r0) false
        = z (order.symm r0) := by
      have h0 := filterMap_getElemD gz r0 hgz false
      simp only [gz] at h0
      simp [hFzj] at h0
      exact h0
    have hposz : codePos gz r0 < ((List.finRange n).filterMap gs).length := by
      rw [← hposEq]
      exact hpos
    have hsame : s (order.symm r0) = z (order.symm r0) := by
      rw [← hgets, ← hgetz, hposEq, ← htail,
        getD_append_left (d := false) (h := hposz)]
    exact hr0ne hsame
