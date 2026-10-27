import EthCor.HamIso

/-! # Cut & Count for connected vertex sets

For a graph G on n vertices with edge list E and a CNF ψ on the vertex variables, the formula
`connF n E ψ` on 3n variables has a vertex bit x_v, a side bit s_v and its complement s̄_v for each
vertex. Its clauses are those of ψ, s̄_v = ¬s_v, s_v = 0 outside X = {v : x_v}, and s_u = s_v on
the edges inside X. Each pair of complementary bits holds exactly one true bit, so the satisfying
assignments with n + ℓ true variables are the pairs (X, s) with |X| = ℓ, X ⊨ ψ and s constant on
the edges of G[X] (`cntS_connF`). There are 2^{cc(G[X])} such s, so half their number is odd exactly
when G[X] is connected (`sig_parity`, by the flip of `EthCor.Ham.parity_sides`, with a root in X).
Hence `cntS / 2` has the parity of the number of sets X of size ℓ ≥ 1 with X ⊨ ψ and G[X]
connected (`conn_parity`). -/

namespace EthCor.Conn

open Groundwork.Prog CountKSat GraphProblems Finset EthCor.Ham EthCor.HamS EthCor.HamI

/-! ### The side maps of a graph on any vertex type -/

open Classical in
/-- The side maps constant along the edges of H with s r false are odd in number exactly if H is
connected. -/
theorem parity_root {V : Type} [Fintype V] (r : V) (H : SimpleGraph V) :
    (univ.filter fun s : V → Bool => s r = false ∧ ∀ u v, H.Adj u v → s u = s v).card % 2 =
      if H.Connected then 1 else 0 := by
  set S := univ.filter fun s : V → Bool => s r = false ∧ ∀ u v, H.Adj u v → s u = s v with hSdef
  have hreach : ∀ s ∈ S, ∀ u v, H.Reachable u v → s u = s v := by
    intro s hs u v ⟨p⟩
    induction p with
    | nil => rfl
    | cons h p ih => exact ((mem_filter.1 hs).2.2 _ _ h).trans ih
  split_ifs with hc
  · have hS : S = {fun _ => false} := by
      ext s
      simp only [mem_singleton]
      constructor
      · intro hs
        funext v
        rw [← (mem_filter.1 hs).2.1]
        exact hreach s hs _ _ (hc.preconnected v r)
      · rintro rfl
        simp [hSdef]
    rw [hS, card_singleton]
  · obtain ⟨w, hw⟩ : ∃ w, ¬ H.Reachable r w := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hc ((SimpleGraph.connected_iff H).2 ⟨fun u v => (h u).symm.trans (h v), ⟨r⟩⟩)
    let fl : (V → Bool) → (V → Bool) := fun s v => if H.Reachable w v then !s v else s v
    have hfl2 : ∀ s, fl (fl s) = s := fun s => by
      funext v; by_cases h : H.Reachable w v <;> simp [fl, h]
    have hflw : ∀ s, fl s w = !s w := fun s => by simp [fl]
    have hflS : ∀ s ∈ S, fl s ∈ S := by
      intro s hs
      obtain ⟨h0, hadj⟩ := (mem_filter.1 hs).2
      have hw0 : ¬ H.Reachable w r := fun h => hw h.symm
      refine mem_filter.2 ⟨mem_univ _, by simp [fl, hw0, h0], fun u v huv => ?_⟩
      have huv' : H.Reachable w u ↔ H.Reachable w v :=
        ⟨fun h => h.trans huv.reachable, fun h => h.trans huv.reachable.symm⟩
      by_cases h : H.Reachable w u
      · simp [fl, h, huv'.1 h, hadj u v huv]
      · simp [fl, h, mt huv'.2 h, hadj u v huv]
    have hsplit := card_filter_add_card_filter_not (s := S) (fun s => s w = false)
    have hbij : (S.filter fun s => s w = false).card = (S.filter fun s => ¬ s w = false).card := by
      refine Finset.card_bij (fun s _ => fl s) (fun s hs => ?_) (fun s _ t _ h => ?_) (fun t ht => ?_)
      · obtain ⟨hs, e⟩ := mem_filter.1 hs
        exact mem_filter.2 ⟨hflS s hs, by rw [hflw, e]; simp⟩
      · rw [← hfl2 s, h, hfl2]
      · obtain ⟨ht, e⟩ := mem_filter.1 ht
        refine ⟨fl t, mem_filter.2 ⟨hflS t ht, ?_⟩, hfl2 t⟩
        rw [hflw]; simpa using e
    omega

open Classical in
/-- Flipping every side halves the side maps: half of them have s r false. -/
theorem card_sides_two {V : Type} [Fintype V] (r : V) (H : SimpleGraph V) :
    (univ.filter fun s : V → Bool => ∀ u v, H.Adj u v → s u = s v).card =
      2 * (univ.filter fun s : V → Bool => s r = false ∧ ∀ u v, H.Adj u v → s u = s v).card := by
  set S := univ.filter fun s : V → Bool => ∀ u v, H.Adj u v → s u = s v with hSdef
  have hsplit := card_filter_add_card_filter_not (s := S) (fun s => s r = false)
  have h1 : S.filter (fun s => s r = false) =
      univ.filter fun s : V → Bool => s r = false ∧ ∀ u v, H.Adj u v → s u = s v := by
    ext s; simp only [hSdef, mem_filter, mem_univ, true_and]; exact and_comm
  have hbij : (S.filter fun s => s r = false).card = (S.filter fun s => ¬ s r = false).card := by
    refine Finset.card_bij (fun s _ => fun v => !s v) (fun s hs => ?_) (fun s _ t _ h => ?_) (fun t ht => ?_)
    · obtain ⟨hs, e⟩ := mem_filter.1 hs
      refine mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, fun u v huv => ?_⟩, by simp [e]⟩
      show (!s u) = !s v
      rw [(mem_filter.1 hs).2 u v huv]
    · funext v; have := congrFun h v; simpa using this
    · obtain ⟨ht, e⟩ := mem_filter.1 ht
      refine ⟨fun v => !t v, mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, fun u v huv => ?_⟩, by simpa using e⟩, ?_⟩
      · show (!t u) = !t v
        rw [(mem_filter.1 ht).2 u v huv]
      · funext v; simp
  rw [← h1]
  omega

/-! ### The side maps of a vertex set -/

/-- The side maps of the vertex set x: 0 outside x, constant on the edges of E inside x. -/
def sig (n : ℕ) (E : List (ℕ × ℕ)) (x : Fin n → Bool) : ℕ :=
  (univ.filter fun s : Fin n → Bool => (∀ v, x v = false → s v = false) ∧
    ∀ p ∈ E, ext x p.1 = true → ext x p.2 = true → ext s p.1 = ext s p.2).card

theorem edge_iff {n : ℕ} (G : SimpleGraph (Fin n)) (x s : Fin n → Bool) :
    (∀ p ∈ edges n (matrix G), ext x p.1 = true → ext x p.2 = true → ext s p.1 = ext s p.2) ↔
      ∀ u v : Fin n, G.Adj u v → x u = true → x v = true → s u = s v := by
  have hE := edges_bound n (matrix G)
  constructor
  · intro h u v huv hu hv
    rcases lt_trichotomy u v with huv' | rfl | huv'
    · have := h _ ((mem_edges stAdj G u v).2 ⟨huv', huv⟩)
      simp only [ext_fin] at this
      exact this hu hv
    · exact rfl
    · have := h _ ((mem_edges stAdj G v u).2 ⟨huv', huv.symm⟩)
      simp only [ext_fin] at this
      exact (this hv hu).symm
  · intro h p hp hu hv
    obtain ⟨h1, h2⟩ := hE p hp
    have hm := (mem_edges stAdj G ⟨p.1, by omega⟩ ⟨p.2, h2⟩).1 hp
    have := h ⟨p.1, by omega⟩ ⟨p.2, h2⟩ hm.2 (by rw [← ext_fin x ⟨p.1, by omega⟩]; exact hu)
      (by rw [← ext_fin x ⟨p.2, h2⟩]; exact hv)
    rw [← ext_fin s ⟨p.1, by omega⟩, ← ext_fin s ⟨p.2, h2⟩] at this
    exact this

open Classical in
/-- The side maps of x are those of the induced subgraph G[x]. -/
theorem sig_eq {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) :
    sig n (edges n (matrix G)) x = (univ.filter fun s : ({v | x v = true} : Set (Fin n)) → Bool =>
      ∀ u v, (G.induce {v | x v = true}).Adj u v → s u = s v).card := by
  unfold sig
  refine Finset.card_nbij' (fun s v => s v.val) (fun s' v => if h : x v = true then s' ⟨v, h⟩ else false)
    ?_ ?_ ?_ ?_
  · intro s hs
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hs ⊢
    intro u v huv
    rw [SimpleGraph.induce_adj] at huv
    exact (edge_iff G x s).1 hs.2 u v huv u.2 v.2
  · intro s' hs'
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hs' ⊢
    refine ⟨fun v hv => by simp [hv], (edge_iff G x _).2 fun u v huv hu hv => ?_⟩
    simp only [hu, hv, dif_pos]
    exact hs' ⟨u, hu⟩ ⟨v, hv⟩ (by rw [SimpleGraph.induce_adj]; exact huv)
  · intro s hs
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hs
    funext v
    by_cases hv : x v = true
    · simp [hv]
    · simp only [hv]
      exact (hs.1 v (by simpa using hv)).symm
  · intro s' _
    funext v
    show (if h : x v.val = true then s' ⟨v.val, h⟩ else false) = s' v
    rw [dif_pos (show x v.val = true from v.2)]

open Classical in
/-- **Half the side maps of a nonempty x are odd in number exactly if G[x] is connected.** -/
theorem sig_parity {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) (hx : ∃ r, x r = true) :
    sig n (edges n (matrix G)) x = 2 * (sig n (edges n (matrix G)) x / 2) ∧
      sig n (edges n (matrix G)) x / 2 % 2 = if (G.induce {v | x v = true}).Connected then 1 else 0 := by
  obtain ⟨r, hr⟩ := hx
  have h := card_sides_two (⟨r, hr⟩ : ({v | x v = true} : Set (Fin n))) (G.induce {v | x v = true})
  have hp := parity_root (⟨r, hr⟩ : ({v | x v = true} : Set (Fin n))) (G.induce {v | x v = true})
  have e1 : sig n (edges n (matrix G)) x = 2 * (univ.filter fun s : ({v | x v = true} : Set (Fin n)) → Bool =>
      s ⟨r, hr⟩ = false ∧ ∀ u v, (G.induce {v | x v = true}).Adj u v → s u = s v).card :=
    (sig_eq G x).trans (by convert h)
  rw [e1, Nat.mul_div_cancel_left _ two_pos]
  exact ⟨rfl, by convert hp⟩

/-! ### The formula -/

/-- s̄_v = ¬s_v, and s_v = 0 if v is not in the set. -/
def sideF (n : ℕ) : Fml := (List.range n).flatMap fun v =>
  [[(n + v, true), (n + n + v, true)], [(n + v, false), (n + n + v, false)], [(v, true), (n + v, false)]]

/-- s_u = s_v on the edges inside the set. -/
def edgeCC (n : ℕ) (E : List (ℕ × ℕ)) : Fml := E.flatMap fun p =>
  [[(p.1, false), (p.2, false), (n + p.1, false), (n + p.2, true)],
   [(p.1, false), (p.2, false), (n + p.1, true), (n + p.2, false)]]

def connF (n : ℕ) (E : List (ℕ × ℕ)) (ψ : Fml) : Fml := ψ ++ sideF n ++ edgeCC n E

theorem sat_sideF (f : ℕ → Bool) (n : ℕ) : (∀ C ∈ sideF n, ∃ l ∈ C, f l.1 = l.2) ↔
    ∀ v < n, f (n + n + v) = !f (n + v) ∧ (f v = false → f (n + v) = false) := by
  rw [sideF, forall_flatMap_range]
  refine forall₂_congr fun v _ => ?_
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, sat2]
  generalize f v = a, f (n + v) = b, f (n + n + v) = c
  cases a <;> cases b <;> cases c <;> decide

theorem sat4 (f : ℕ → Bool) (a b c d : ℕ × Bool) :
    (∃ l ∈ [a, b, c, d], f l.1 = l.2) ↔ f a.1 = a.2 ∨ f b.1 = b.2 ∨ f c.1 = c.2 ∨ f d.1 = d.2 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨l, hl, e⟩
    rcases hl with rfl | rfl | rfl | rfl <;> simp [e]
  · rintro (e | e | e | e)
    · exact ⟨a, Or.inl rfl, e⟩
    · exact ⟨b, Or.inr (Or.inl rfl), e⟩
    · exact ⟨c, Or.inr (Or.inr (Or.inl rfl)), e⟩
    · exact ⟨d, Or.inr (Or.inr (Or.inr rfl)), e⟩

theorem sat_edgeCC (f : ℕ → Bool) (n : ℕ) (E : List (ℕ × ℕ)) : (∀ C ∈ edgeCC n E, ∃ l ∈ C, f l.1 = l.2) ↔
    ∀ p ∈ E, f p.1 = true → f p.2 = true → f (n + p.1) = f (n + p.2) := by
  have h : (∀ C ∈ edgeCC n E, ∃ l ∈ C, f l.1 = l.2) ↔ ∀ p ∈ E, ∀ C ∈ [[(p.1, false), (p.2, false), (n + p.1, false),
      (n + p.2, true)], [(p.1, false), (p.2, false), (n + p.1, true), (n + p.2, false)]], ∃ l ∈ C, f l.1 = l.2 := by
    simp only [edgeCC, List.mem_flatMap]
    exact ⟨fun h p hp C hC => h C ⟨p, hp, hC⟩, fun h C ⟨p, hp, hC⟩ => h p hp C hC⟩
  rw [h]
  refine forall₂_congr fun p _ => ?_
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, sat4]
  generalize f p.1 = a, f p.2 = b, f (n + p.1) = c, f (n + p.2) = d
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-! ### The count -/

theorem card_true_append {a b : ℕ} (y : Fin a → Bool) (g : Fin b → Bool) :
    (univ.filter fun i => Fin.append y g i = true).card =
      (univ.filter fun i => y i = true).card + (univ.filter fun i => g i = true).card := by
  rw [card_filter, card_filter, card_filter, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem card_true_not {n : ℕ} (s : Fin n → Bool) :
    (univ.filter fun i => s i = true).card + (univ.filter fun i => (!s i) = true).card = n := by
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i => s i = true)
  rw [card_univ, Fintype.card_fin] at this
  have e : (univ.filter fun i => (!s i) = true) = univ.filter fun i => ¬ s i = true := by
    ext i; simp
  rw [e]; exact this

theorem ext_natAdd {n : ℕ} (y : Fin (n + n) → Bool) {v : ℕ} (hv : v < n) :
    ext y (n + v) = y (Fin.natAdd n ⟨v, hv⟩) := by
  simp only [CountKSat.ext, dif_pos (show n + v < n + n by omega)]; rfl

/-- Step A: the complementary bits are determined. -/
theorem cnt_stepA {n ℓ : ℕ} {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) {ψ : Fml}
    (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) :
    cntS (n + n + n) (n + ℓ) (connF n E ψ) =
      (univ.filter fun y : Fin (n + n) → Bool => ((∀ C ∈ ψ, ∃ l ∈ C, ext y l.1 = l.2) ∧
        (∀ v < n, ext y v = false → ext y (n + v) = false) ∧
        ∀ p ∈ E, ext y p.1 = true → ext y p.2 = true → ext y (n + p.1) = ext y (n + p.2)) ∧
        (univ.filter fun v : Fin n => y (Fin.castAdd n v) = true).card = ℓ).card := by
  unfold cntS
  refine card_append _ _ (fun y v => !y (Fin.natAdd n v)) fun y g => ?_
  have hlt : ∀ a < n + n, ext (Fin.append y g) a = ext y a := fun a ha => ext_append_lt y g ha
  have hE' : ∀ p ∈ E, (ext (Fin.append y g) p.1 = true → ext (Fin.append y g) p.2 = true →
      ext (Fin.append y g) (n + p.1) = ext (Fin.append y g) (n + p.2)) ↔
      (ext y p.1 = true → ext y p.2 = true → ext y (n + p.1) = ext y (n + p.2)) := fun p hp => by
    have := hE p hp
    rw [hlt p.1 (by omega), hlt p.2 (by omega), hlt (n + p.1) (by omega), hlt (n + p.2) (by omega)]
  have hside : (∀ v < n, ext (Fin.append y g) (n + n + v) = !ext (Fin.append y g) (n + v) ∧
      (ext (Fin.append y g) v = false → ext (Fin.append y g) (n + v) = false)) ↔
      (∀ v < n, ext g v = !ext y (n + v)) ∧ (∀ v < n, ext y v = false → ext y (n + v) = false) := by
    rw [← forall₂_and]
    exact forall₂_congr fun v hv => by rw [ext_append_ge, hlt (n + v) (by omega), hlt v (by omega)]
  have hg : (∀ v < n, ext g v = !ext y (n + v)) ↔ g = fun v => !y (Fin.natAdd n v) := by
    constructor
    · intro h
      funext v
      have := h v.val v.2
      rwa [ext_fin, ext_natAdd y v.2] at this
    · rintro rfl v hv
      rw [ext_natAdd y hv]
      simp only [CountKSat.ext, dif_pos hv]
  have hcy : (univ.filter fun i => y i = true).card = (univ.filter fun v : Fin n => y (Fin.castAdd n v) = true).card +
      (univ.filter fun v : Fin n => y (Fin.natAdd n v) = true).card := by
    conv_lhs => rw [← Fin.append_castAdd_natAdd (f := y)]
    exact card_true_append _ _
  have hcount : (univ.filter fun i => Fin.append y (fun v => !y (Fin.natAdd n v)) i = true).card =
      (univ.filter fun v : Fin n => y (Fin.castAdd n v) = true).card + n := by
    rw [card_true_append, hcy]
    have := card_true_not (fun v => y (Fin.natAdd n v))
    omega
  rw [connF, List.forall_mem_append, List.forall_mem_append,
    sat_congr (f' := ext y) (fun C hC l hl => hlt _ (by have := hψ C hC l hl; omega)),
    sat_edgeCC, sat_sideF, hside, hg, forall₂_congr hE']
  constructor
  · rintro ⟨⟨⟨hA, hG, hS⟩, hC⟩, hcnt⟩
    subst hG
    exact ⟨⟨⟨hA, hS, hC⟩, by rw [hcount] at hcnt; omega⟩, rfl⟩
  · rintro ⟨⟨⟨hA, hS, hC⟩, hcnt⟩, rfl⟩
    exact ⟨⟨⟨hA, rfl, hS⟩, hC⟩, by rw [hcount]; omega⟩

/-- Step B: the pairs (x, s). -/
theorem cnt_stepB {n ℓ : ℕ} {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) {ψ : Fml}
    (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) :
    (univ.filter fun y : Fin (n + n) → Bool => ((∀ C ∈ ψ, ∃ l ∈ C, ext y l.1 = l.2) ∧
        (∀ v < n, ext y v = false → ext y (n + v) = false) ∧
        ∀ p ∈ E, ext y p.1 = true → ext y p.2 = true → ext y (n + p.1) = ext y (n + p.2)) ∧
        (univ.filter fun v : Fin n => y (Fin.castAdd n v) = true).card = ℓ).card =
      ∑ x : Fin n → Bool, if (∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧ (univ.filter fun v => x v = true).card = ℓ
        then sig n E x else 0 := by
  rw [Finset.card_equiv (Fin.appendEquiv n n).symm (t := univ.filter fun p : (Fin n → Bool) × (Fin n → Bool) =>
      ((∀ C ∈ ψ, ∃ l ∈ C, ext p.1 l.1 = l.2) ∧ (univ.filter fun v => p.1 v = true).card = ℓ) ∧
      ((∀ v, p.1 v = false → p.2 v = false) ∧
        ∀ q ∈ E, ext p.1 q.1 = true → ext p.1 q.2 = true → ext p.2 q.1 = ext p.2 q.2))]
  · rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rw [sig, Finset.card_filter]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases h : (∀ v, x v = false → s v = false) ∧
          ∀ q ∈ E, ext x q.1 = true → ext x q.2 = true → ext s q.1 = ext s q.2
      · rw [if_pos ⟨hx, h⟩, if_pos h]
      · rw [if_neg (fun h' => h h'.2), if_neg h]
    · exact Finset.sum_eq_zero fun s _ => if_neg fun h => hx h.1
  · intro b
    simp only [mem_filter, mem_univ, true_and]
    obtain ⟨p, rfl⟩ : ∃ p, b = Fin.appendEquiv n n p := ⟨_, ((Fin.appendEquiv n n).apply_symm_apply b).symm⟩
    rw [Equiv.symm_apply_apply]
    have hb : (Fin.appendEquiv n n) p = Fin.append p.1 p.2 := funext fun a => Fin.appendEquiv_apply _ _ _ _
    rw [hb]
    have hlt : ∀ a < n, ext (Fin.append p.1 p.2) a = ext p.1 a := fun a ha => ext_append_lt _ _ ha
    rw [sat_congr (f' := ext p.1) (fun C hC l hl => hlt _ (hψ C hC l hl))]
    have hside : (∀ v < n, ext (Fin.append p.1 p.2) v = false → ext (Fin.append p.1 p.2) (n + v) = false) ↔
        ∀ v, p.1 v = false → p.2 v = false := by
      constructor
      · intro h v hv
        have := h v.val v.2 (by rw [hlt _ v.2, ext_fin]; exact hv)
        rwa [ext_append_ge, ext_fin] at this
      · intro h v hv e
        rw [hlt _ hv] at e
        rw [ext_append_ge]
        have := h ⟨v, hv⟩ (by rw [← ext_fin p.1 ⟨v, hv⟩]; exact e)
        rw [← ext_fin p.2 ⟨v, hv⟩] at this; exact this
    have hedge : (∀ q ∈ E, ext (Fin.append p.1 p.2) q.1 = true → ext (Fin.append p.1 p.2) q.2 = true →
        ext (Fin.append p.1 p.2) (n + q.1) = ext (Fin.append p.1 p.2) (n + q.2)) ↔
        ∀ q ∈ E, ext p.1 q.1 = true → ext p.1 q.2 = true → ext p.2 q.1 = ext p.2 q.2 :=
      forall₂_congr fun q hq => by
        have := hE q hq
        rw [hlt q.1 (by omega), hlt q.2 (by omega), ext_append_ge, ext_append_ge]
    have hcnt : (univ.filter fun v : Fin n => Fin.append p.1 p.2 (Fin.castAdd n v) = true) =
        univ.filter fun v => p.1 v = true := by
      simp only [Fin.append_left]
    rw [hside, hedge, hcnt]
    tauto

theorem cntS_connF {n ℓ : ℕ} {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) {ψ : Fml}
    (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) :
    cntS (n + n + n) (n + ℓ) (connF n E ψ) =
      ∑ x : Fin n → Bool, if (∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧ (univ.filter fun v => x v = true).card = ℓ
        then sig n E x else 0 := by
  rw [cnt_stepA hE hψ, cnt_stepB hE hψ]

open Classical in
/-- The number of vertex sets of size ℓ that satisfy ψ and induce a connected subgraph. -/
noncomputable def numConnF {n : ℕ} (G : SimpleGraph (Fin n)) (ψ : Fml) (ℓ : ℕ) : ℕ :=
  (univ.filter fun x : Fin n → Bool => (∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧
    (univ.filter fun v => x v = true).card = ℓ ∧ (G.induce {v | x v = true}).Connected).card

open Classical in
/-- **Cut & Count for connected vertex sets**: half the number of satisfying assignments of `connF`
with n + ℓ true variables has the parity of the number of sets X of size ℓ ≥ 1 with X ⊨ ψ and G[X]
connected. -/
theorem conn_parity {n : ℕ} (G : SimpleGraph (Fin n)) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) :
    cntS (n + n + n) (n + ℓ) (connF n (edges n (matrix G)) ψ) / 2 % 2 = numConnF G ψ ℓ % 2 := by
  rw [cntS_connF (edges_bound n (matrix G)) hψ]
  have key : ∀ x : Fin n → Bool,
      (if (∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧ (univ.filter fun v => x v = true).card = ℓ
        then sig n (edges n (matrix G)) x else 0) =
        2 * (if (∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧ (univ.filter fun v => x v = true).card = ℓ
          then sig n (edges n (matrix G)) x / 2 else 0) ∧
      (if (∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧ (univ.filter fun v => x v = true).card = ℓ
          then sig n (edges n (matrix G)) x / 2 else 0) % 2 =
        if (∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧ (univ.filter fun v => x v = true).card = ℓ ∧
          (G.induce {v | x v = true}).Connected then 1 else 0 := by
    intro x
    by_cases hP : (∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧ (univ.filter fun v => x v = true).card = ℓ
    · have hx : ∃ r, x r = true := by
        by_contra h
        push Not at h
        have : (univ.filter fun v => x v = true) = ∅ := filter_eq_empty_iff.2 fun v _ => by simp [h v]
        rw [this, card_empty] at hP
        omega
      obtain ⟨h1, h2⟩ := sig_parity G x hx
      rw [if_pos hP, if_pos hP, h2]
      refine ⟨h1, ?_⟩
      by_cases hc : (G.induce {v | x v = true}).Connected
      · rw [if_pos hc, if_pos ⟨hP.1, hP.2, hc⟩]
      · rw [if_neg hc, if_neg fun h => hc h.2.2]
    · rw [if_neg hP, if_neg hP, if_neg fun h => hP ⟨h.1, h.2.1⟩]
      simp
  rw [Finset.sum_congr rfl fun x _ => (key x).1, ← Finset.mul_sum, Nat.mul_div_cancel_left _ two_pos,
    Finset.sum_nat_mod, Finset.sum_congr rfl fun x _ => (key x).2, ← Finset.card_filter, numConnF]

end EthCor.Conn
