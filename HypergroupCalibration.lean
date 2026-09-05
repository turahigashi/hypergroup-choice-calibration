/-
  Choice in the Fundamental Theorem of Hypergroups
  — a self-contained development. Depends only on Mathlib.
  Lean 4, toolchain leanprover/lean4:v4.30.0.
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Tactic.Group
import Mathlib.Logic.Relation
import Mathlib.Tactic

namespace Hypergroups

-- ════════ ハイパー構造 (Marty 1934): 代数的ハイパー群 = 群論の真の一般化 ════════
-- [Corsini–Leoreanu] (fringe 代数的ハイパー構造). ∘ : H→H→P*(H), A∘B = ⋃_{a∈A,b∈B} a∘b,
-- 結合律 + 再生公理 a∘H=H=H∘a. novelty: hypergroup/hyperring = カタログ0件 + 全証明系未形式化.
-- ("hyperoperation" の Mathlib ヒットは Ackermann 超演算 = 同名異義, 代数的ハイパー構造と無関係.)

/-- 集合へのハイパー演算の拡張 A∘B = {z | ∃a∈A, ∃b∈B, z ∈ a∘b} (DB抽出に忠実) -/
def hsmul {H : Type*} (hop : H → H → Set H) (A B : Set H) : Set H :=
  {z | ∃ a ∈ A, ∃ b ∈ B, z ∈ hop a b}

/-- ハイパー群: ハイパー演算 + 非空性 + 結合律 + 両側再生公理. 群 (a∘b={a*b}) の一般化. -/
structure Hypergroup (H : Type*) where
  hop : H → H → Set H
  carrier_nonempty : Nonempty H            -- ★標準: ハイパー群は非空集合上の構造 (空carrier排除)
  hop_nonempty : ∀ a b, (hop a b).Nonempty
  hop_assoc : ∀ a b c, hsmul hop (hop a b) {c} = hsmul hop {a} (hop b c)
  repro_right : ∀ a, (⋃ x, hop a x) = Set.univ
  repro_left  : ∀ a, (⋃ x, hop x a) = Set.univ

/-- ★再生公理 ⟹ 右可解性: 方程式 b ∈ a∘x は常に解 x をもつ (準群可解性のハイパー版) -/
theorem hypergroup_right_solvable {H : Type*} (G : Hypergroup H) (a b : H) :
    ∃ x, b ∈ G.hop a x := by
  have hb : b ∈ (⋃ x, G.hop a x) := by rw [G.repro_right]; exact Set.mem_univ b
  simpa only [Set.mem_iUnion] using hb

/-- ★再生公理 ⟹ 左可解性: 方程式 b ∈ x∘a は常に解 x をもつ -/
theorem hypergroup_left_solvable {H : Type*} (G : Hypergroup H) (a b : H) :
    ∃ x, b ∈ G.hop x a := by
  have hb : b ∈ (⋃ x, G.hop x a) := by rw [G.repro_left]; exact Set.mem_univ b
  simpa only [Set.mem_iUnion] using hb

/-- ★非空性の証人 = 任意の群はハイパー群 (a∘b := {a*b}). Marty「群論の一般化」を形式化. -/
theorem group_is_hypergroup (G : Type*) [Group G] : Nonempty (Hypergroup G) :=
  ⟨{ hop := fun a b => {a * b}
     carrier_nonempty := ⟨1⟩
     hop_nonempty := fun a b => ⟨a * b, rfl⟩
     hop_assoc := fun a b c => by ext z; simp [hsmul, mul_assoc]
     repro_right := fun a => by
       ext z
       simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ, iff_true]
       exact ⟨a⁻¹ * z, by group⟩
     repro_left := fun a => by
       ext z
       simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ, iff_true]
       exact ⟨z * a⁻¹, by group⟩ }⟩

-- ── ★forced-use エンジン実走 (定義レベル): 未形式化 A=Hypergroup から 王道概念 S を定義 ──
-- S=ハイパー群準同型 は G.hop を使う=Hypergroup を定義的に forced-use → A 未形式化なら S も未形式化(保証).
/-- ★王道概念「準同型」をハイパー群 A の上に定義: f が超積を保つ f''(a∘b) ⊆ f(a)∘f(b). -/
def HypergroupHom {H1 H2 : Type*} (G1 : Hypergroup H1) (G2 : Hypergroup H2) (f : H1 → H2) : Prop :=
  ∀ a b, f '' (G1.hop a b) ⊆ G2.hop (f a) (f b)

/-- ★恒等写像は準同型 (圏 Hypergrp の id). -/
theorem hypergroupHom_id {H : Type*} (G : Hypergroup H) : HypergroupHom G G id := by
  intro a b y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hx

/-- ★★準同型の合成は準同型 (圏 Hypergrp の射の合成則=王道事実をハイパー群上で). -/
theorem hypergroupHom_comp {H1 H2 H3 : Type*}
    {G1 : Hypergroup H1} {G2 : Hypergroup H2} {G3 : Hypergroup H3}
    {f : H1 → H2} {g : H2 → H3}
    (hf : HypergroupHom G1 G2 f) (hg : HypergroupHom G2 G3 g) :
    HypergroupHom G1 G3 (g ∘ f) := by
  intro a b z hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hfx : f x ∈ G2.hop (f a) (f b) := hf a b ⟨x, hx, rfl⟩
  exact hg (f a) (f b) ⟨f x, hfx, rfl⟩

-- ── ★A 続: HypergroupHom の上に 王道概念「部分構造」を積む (3層定義連鎖=全て未形式化) ──
/-- ★王道概念「部分構造(閉じた部分集合)」をハイパー群上に定義: hop で閉じる. -/
def SubHypergroupClosed {H : Type*} (G : Hypergroup H) (K : Set H) : Prop :=
  ∀ a ∈ K, ∀ b ∈ K, G.hop a b ⊆ K

/-- ★univ は閉じている (自明な部分構造). -/
theorem subHypClosed_univ {H : Type*} (G : Hypergroup H) :
    SubHypergroupClosed G Set.univ :=
  fun _ _ _ _ => Set.subset_univ _

/-- ★★閉部分集合の交わりは閉じている (部分構造が交わりで閉=束/閉包系をなす, 王道事実をハイパー群上で). -/
theorem subHypClosed_inter {H : Type*} (G : Hypergroup H) {K L : Set H}
    (hK : SubHypergroupClosed G K) (hL : SubHypergroupClosed G L) :
    SubHypergroupClosed G (K ∩ L) := by
  intro a ha b hb x hx
  exact ⟨hK a ha.1 b hb.1 hx, hL a ha.2 b hb.2 hx⟩

/-- ★★準同型 f で 閉部分集合 L の原像 f⁻¹(L) は閉 (王道: 準同型の原像が部分構造=3層連鎖 Hypergroup→Hom→Sub). -/
theorem subHypClosed_preimage {H1 H2 : Type*}
    {G1 : Hypergroup H1} {G2 : Hypergroup H2} {f : H1 → H2}
    (hf : HypergroupHom G1 G2 f) {L : Set H2} (hL : SubHypergroupClosed G2 L) :
    SubHypergroupClosed G1 (f ⁻¹' L) := by
  intro a ha b hb x hx
  have hfx : f x ∈ G2.hop (f a) (f b) := hf a b ⟨x, hx, rfl⟩
  exact hL (f a) ha (f b) hb hfx

/-- ★★任意個の閉部分集合の交わりは閉 (部分構造が【完備束/閉包系】をなす, 王道事実をハイパー群上で). -/
theorem subHypClosed_iInter {H : Type*} (G : Hypergroup H) {ι : Type*} {K : ι → Set H}
    (hK : ∀ i, SubHypergroupClosed G (K i)) :
    SubHypergroupClosed G (⋂ i, K i) := by
  intro a ha b hb x hx
  simp only [Set.mem_iInter] at ha hb ⊢
  exact fun i => hK i a (ha i) b (hb i) hx

-- ── ★A 続: 生成部分ハイパー群 = 閉包作用素 (王道の generated-substructure 構成) ──
/-- ★閉部分集合の集合全体の交わり(⋂₀)も閉 (任意族版). -/
theorem subHypClosed_sInter {H : Type*} (G : Hypergroup H) {S : Set (Set H)}
    (hS : ∀ K ∈ S, SubHypergroupClosed G K) : SubHypergroupClosed G (⋂₀ S) := by
  intro a ha b hb x hx K hK
  exact hS K hK a (ha K hK) b (hb K hK) hx

/-- ★X が生成する部分ハイパー群 = X を含む全閉部分集合の交わり (閉包作用素). -/
def subHypGenerated {H : Type*} (G : Hypergroup H) (X : Set H) : Set H :=
  ⋂₀ {K | SubHypergroupClosed G K ∧ X ⊆ K}

/-- ★生成部分構造は閉じている. -/
theorem subHypGenerated_closed {H : Type*} (G : Hypergroup H) (X : Set H) :
    SubHypergroupClosed G (subHypGenerated G X) :=
  subHypClosed_sInter G (fun _ hK => hK.1)

/-- ★X ⊆ ⟨X⟩ (拡大性 extensive). -/
theorem subset_subHypGenerated {H : Type*} (G : Hypergroup H) (X : Set H) :
    X ⊆ subHypGenerated G X :=
  fun _ hx _ hK => hK.2 hx

/-- ★★⟨X⟩ は X を含む最小の閉部分構造 (minimality=閉包作用素の普遍性=galois 接続の核). -/
theorem subHypGenerated_minimal {H : Type*} (G : Hypergroup H) {X K : Set H}
    (hK : SubHypergroupClosed G K) (hXK : X ⊆ K) : subHypGenerated G X ⊆ K :=
  fun _ hx => hx K ⟨hK, hXK⟩

-- ════ ★A keystone: 基本関係 β / β* (Koskas 1970/Freni) — ハイパー群を群へ潰す標準関係 ════
/-- ★基本関係 β (β₂版): a,b が共通の2-ハイパー積 x∘y に属す. Koskas/Freni 基本関係の核. -/
def beta2Rel {H : Type*} (G : Hypergroup H) (a b : H) : Prop :=
  ∃ x y, a ∈ G.hop x y ∧ b ∈ G.hop x y

/-- ★β は反射的 (再生公理より a∈a∘x なる x が存在). -/
theorem beta2Rel_refl {H : Type*} (G : Hypergroup H) (a : H) :
    beta2Rel G a a := by
  obtain ⟨x, hx⟩ := hypergroup_right_solvable G a a
  exact ⟨a, x, hx, hx⟩

/-- ★β は対称的. -/
theorem beta2Rel_symm {H : Type*} (G : Hypergroup H) {a b : H}
    (h : beta2Rel G a b) : beta2Rel G b a := by
  obtain ⟨x, y, ha, hb⟩ := h
  exact ⟨x, y, hb, ha⟩

/-- ★基本関係 β* = β の同値閉包 (推移閉包込み, 自動的に同値関係). 商 H/β* の土台. -/
def beta2Star {H : Type*} (G : Hypergroup H) : H → H → Prop := Relation.EqvGen (beta2Rel G)

/-- ★β* は同値関係 (商 H/β* の土台). -/
theorem beta2Star_equivalence {H : Type*} (G : Hypergroup H) : Equivalence (beta2Star G) :=
  Relation.EqvGen.is_equivalence _

-- (群依存の β=equality / β*=equality は groupHypergroup 定義後に置く=前方参照回避)

/-- ★王道概念「同型」をハイパー群上に定義: 双方向準同型な全単射 (圏 Hypergrp の同型射). -/
structure HypergroupIso {H1 H2 : Type*} (G1 : Hypergroup H1) (G2 : Hypergroup H2) where
  toFun : H1 → H2
  invFun : H2 → H1
  left_inv : invFun ∘ toFun = id
  right_inv : toFun ∘ invFun = id
  hom : HypergroupHom G1 G2 toFun
  inv_hom : HypergroupHom G2 G1 invFun

/-- ★恒等写像は同型 (≅ の反射性). -/
def hypergroupIso_id {H : Type*} (G : Hypergroup H) : HypergroupIso G G :=
  { toFun := id, invFun := id, left_inv := rfl, right_inv := rfl,
    hom := hypergroupHom_id G, inv_hom := hypergroupHom_id G }

/-- ★同型の逆も同型 (≅ の対称性). -/
def hypergroupIso_symm {H1 H2 : Type*} {G1 : Hypergroup H1} {G2 : Hypergroup H2}
    (e : HypergroupIso G1 G2) : HypergroupIso G2 G1 :=
  { toFun := e.invFun, invFun := e.toFun, left_inv := e.right_inv, right_inv := e.left_inv,
    hom := e.inv_hom, inv_hom := e.hom }

-- ── ★A 続: 主流群論との整合 (埋め込み Grp→Hypergrp が functorial=一般化が忠実) ──
/-- ★群が誘導するハイパー群 (a∘b:={a*b}) の名前付き版 (Marty「群論の一般化」). -/
def groupHypergroup (G : Type*) [Group G] : Hypergroup G where
  hop := fun a b => {a * b}
  carrier_nonempty := ⟨1⟩
  hop_nonempty := fun a b => ⟨a * b, rfl⟩
  hop_assoc := fun a b c => by ext z; simp [hsmul, mul_assoc]
  repro_right := fun a => by
    ext z; simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact ⟨a⁻¹ * z, by group⟩
  repro_left := fun a => by
    ext z; simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact ⟨z * a⁻¹, by group⟩

/-- ★★群準同型は誘導ハイパー群の間のハイパー群準同型 (埋め込み Grp→Hypergrp が functorial
    =一般化が忠実・主流群論との整合=ハイパー群理論が群論の真の拡張であることの形式的証拠). -/
theorem groupHom_is_hypergroupHom {G1 G2 : Type*} [Group G1] [Group G2] (φ : G1 →* G2) :
    HypergroupHom (groupHypergroup G1) (groupHypergroup G2) φ := by
  intro a b y hy
  simp only [groupHypergroup, Set.image_singleton, Set.mem_singleton_iff] at hy ⊢
  rw [hy, map_mul]

/-- ★同型の合成も同型 (≅ の推移性 → id/symm/trans で ≅ が同値関係=圏 Hypergrp の骨格完成). -/
def hypergroupIso_trans {H1 H2 H3 : Type*}
    {G1 : Hypergroup H1} {G2 : Hypergroup H2} {G3 : Hypergroup H3}
    (e : HypergroupIso G1 G2) (f : HypergroupIso G2 G3) : HypergroupIso G1 G3 :=
  { toFun := f.toFun ∘ e.toFun
    invFun := e.invFun ∘ f.invFun
    left_inv := by
      ext x
      simp only [Function.comp_apply]
      have hf : f.invFun (f.toFun (e.toFun x)) = e.toFun x := congrFun f.left_inv (e.toFun x)
      rw [hf]; exact congrFun e.left_inv x
    right_inv := by
      ext x
      simp only [Function.comp_apply]
      have he : e.toFun (e.invFun (f.invFun x)) = f.invFun x := congrFun e.right_inv (f.invFun x)
      rw [he]; exact congrFun f.right_inv x
    hom := hypergroupHom_comp e.hom f.hom
    inv_hom := hypergroupHom_comp f.inv_hom e.inv_hom }

-- ── ★β/β* の群への適用 (groupHypergroup 定義後に配置=前方参照回避) ──
/-- ★★群が誘導するハイパー群では β は equality に潰れる (x∘y={x*y} ゆえ a,b∈{x*y}→a=b).
    = β は「非群性」を測る・群なら自明. -/
theorem beta2Rel_eq_for_group {G : Type*} [Group G] {a b : G}
    (h : beta2Rel (groupHypergroup G) a b) : a = b := by
  obtain ⟨x, y, ha, hb⟩ := h
  simp only [groupHypergroup, Set.mem_singleton_iff] at ha hb
  rw [ha, hb]

/-- ★★★群が誘導するハイパー群では β* も equality に潰れる (∴ 商 H/β* ≅ G で群を回復=correctness).
    β⊆equality ゆえ同値閉包 β* も equality (EqvGen 帰納). 基本関係構成の正しさの検証. -/
theorem beta2Star_eq_for_group {G : Type*} [Group G] {a b : G}
    (h : beta2Star (groupHypergroup G) a b) : a = b := by
  unfold beta2Star at h
  induction h with
  | rel _ _ hxy => exact beta2Rel_eq_for_group hxy
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

-- ════ ★crown: 強正則同値による商 H/R の群構造 (基本関係定理の条件版, Davvaz/Freni) ════
-- 多価ハイパー演算 (genuinely-new primitive) → β* → 商【群】(royal-road) への定義連鎖.
-- = Case B-reliable の構造的核心を kernel 検証 (well-defined が crux=多価演算が単一クラスへ潰れる).

/-- ★強正則同値関係: R は同値関係でハイパー演算と両立 (代表元に依らず・結果が単一クラス).
    Davvaz「基本関係」: R 強正則 ⟺ 商 H/R が群. -/
structure StronglyRegular {H : Type*} (G : Hypergroup H) (R : H → H → Prop) : Prop where
  equiv : Equivalence R
  compat : ∀ a a' b b', R a a' → R b b' → ∀ u ∈ G.hop a b, ∀ v ∈ G.hop a' b', R u v

/-- 強正則 R から Setoid (商 H/R の土台). -/
def srSetoid {H : Type*} {G : Hypergroup H} {R : H → H → Prop} (hR : StronglyRegular G R) :
    Setoid H := ⟨R, hR.equiv⟩

/-- ★商 H/R 上の誘導積 (well-defined=本定理の核心: 多価 a∘b の代表元選択に依らず単一クラス). -/
noncomputable def srMul {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) :
    Quotient (srSetoid hR) → Quotient (srSetoid hR) → Quotient (srSetoid hR) :=
  @Quotient.lift₂ H H (Quotient (srSetoid hR)) (srSetoid hR) (srSetoid hR)
    (fun a b => Quotient.mk (srSetoid hR) (G.hop_nonempty a b).choose)
    (fun a₁ b₁ a₂ b₂ h1 h2 => Quotient.sound
      (hR.compat a₁ a₂ b₁ b₂ h1 h2 _ (G.hop_nonempty a₁ b₁).choose_spec
        _ (G.hop_nonempty a₂ b₂).choose_spec))

/-- ★workhorse: 商の積 ⟦a⟧⊗⟦b⟧ は a∘b の【任意の元】のクラスに等しい. -/
theorem srMul_eq_of_mem {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) (a b c : H) (hc : c ∈ G.hop a b) :
    srMul hR (Quotient.mk (srSetoid hR) a) (Quotient.mk (srSetoid hR) b)
      = Quotient.mk (srSetoid hR) c := by
  apply Quotient.sound
  exact hR.compat a a b b (hR.equiv.refl a) (hR.equiv.refl b)
    _ (G.hop_nonempty a b).choose_spec c hc

/-- ★商の積は結合的 (well-defined + 結合律 = H/R は半群). -/
theorem srMul_assoc {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) (x y z : Quotient (srSetoid hR)) :
    srMul hR (srMul hR x y) z = srMul hR x (srMul hR y z) := by
  induction x using Quotient.inductionOn with | _ a =>
  induction y using Quotient.inductionOn with | _ b =>
  induction z using Quotient.inductionOn with | _ c =>
  obtain ⟨p, hp⟩ := G.hop_nonempty a b
  obtain ⟨q, hq⟩ := G.hop_nonempty p c
  obtain ⟨r, hr⟩ := G.hop_nonempty b c
  obtain ⟨s, hs⟩ := G.hop_nonempty a r
  rw [srMul_eq_of_mem hR a b p hp, srMul_eq_of_mem hR p c q hq,
      srMul_eq_of_mem hR b c r hr, srMul_eq_of_mem hR a r s hs]
  apply Quotient.sound
  have hq_in : q ∈ hsmul G.hop (G.hop a b) {c} := ⟨p, hp, c, rfl, hq⟩
  rw [G.hop_assoc a b c] at hq_in
  simp only [hsmul, Set.mem_setOf_eq, Set.mem_singleton_iff] at hq_in
  obtain ⟨a', ha', r', hr', hqar'⟩ := hq_in
  rw [ha'] at hqar'
  have hrr' : R r r' := hR.compat b b c c (hR.equiv.refl b) (hR.equiv.refl c) r hr r' hr'
  exact hR.equiv.symm (hR.compat a a r r' (hR.equiv.refl a) hrr' s hs q hqar')

/-- ★商では右割算可能: ∀⟦a⟧⟦b⟧, ∃⟦x⟧, ⟦a⟧⊗⟦x⟧=⟦b⟧ (再生公理 repro_right より). -/
theorem srMul_right_solvable {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) (a b : Quotient (srSetoid hR)) : ∃ x, srMul hR a x = b := by
  induction a using Quotient.inductionOn with | _ a =>
  induction b using Quotient.inductionOn with | _ b =>
  obtain ⟨x, hx⟩ := hypergroup_right_solvable G a b
  exact ⟨Quotient.mk (srSetoid hR) x, srMul_eq_of_mem hR a x b hx⟩

/-- ★商では左割算可能: ∀⟦a⟧⟦b⟧, ∃⟦y⟧, ⟦y⟧⊗⟦a⟧=⟦b⟧ (再生公理 repro_left より).
    半群 + 両側可解 = 群 ⇒ H/R は群の構造 (基本関係定理の構造的核心). -/
theorem srMul_left_solvable {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) (a b : Quotient (srSetoid hR)) : ∃ y, srMul hR y a = b := by
  induction a using Quotient.inductionOn with | _ a =>
  induction b using Quotient.inductionOn with | _ b =>
  obtain ⟨y, hy⟩ := hypergroup_left_solvable G a b
  exact ⟨Quotient.mk (srSetoid hR) y, srMul_eq_of_mem hR y a b hy⟩

/-- ★correctness sanity: 群が誘導するハイパー群では等号 (=) が強正則 (単価 a∘b={a*b} ゆえ).
    ★一般のハイパー群では等号は強正則とは限らない=「等号が強正則 ⟺ 本質的に単価=群」. -/
theorem eq_stronglyRegular_group (G : Type*) [Group G] :
    StronglyRegular (groupHypergroup G) (· = ·) where
  equiv := eq_equivalence
  compat := fun a a' b b' ha hb u hu v hv => by
    subst ha; subst hb
    simp only [groupHypergroup, Set.mem_singleton_iff] at hu hv
    rw [hu, hv]

-- ── ★keystone 完成: 強正則商 H/R は群 (両側単位元 + 逆元の存在) ──
/-- ★H/R に両側単位元が存在 (半群+両側可解→大域単位元). carrier_nonempty を内部供給(外部 [Nonempty H] 不要). -/
theorem srMul_exists_id {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) :
    ∃ e : Quotient (srSetoid hR),
      (∀ x, srMul hR e x = x) ∧ (∀ x, srMul hR x e = x) := by
  letI : Nonempty H := G.carrier_nonempty
  obtain ⟨a₀⟩ : Nonempty (Quotient (srSetoid hR)) :=
    ⟨Quotient.mk (srSetoid hR) (Classical.arbitrary H)⟩
  obtain ⟨e, he⟩ := srMul_right_solvable hR a₀ a₀
  obtain ⟨e', he'⟩ := srMul_left_solvable hR a₀ a₀
  have hrid : ∀ x, srMul hR x e = x := by
    intro x
    obtain ⟨y, hy⟩ := srMul_left_solvable hR a₀ x
    calc srMul hR x e = srMul hR (srMul hR y a₀) e := by rw [hy]
      _ = srMul hR y (srMul hR a₀ e) := srMul_assoc hR y a₀ e
      _ = srMul hR y a₀ := by rw [he]
      _ = x := hy
  have hlid : ∀ x, srMul hR e' x = x := by
    intro x
    obtain ⟨y, hy⟩ := srMul_right_solvable hR a₀ x
    calc srMul hR e' x = srMul hR e' (srMul hR a₀ y) := by rw [hy]
      _ = srMul hR (srMul hR e' a₀) y := (srMul_assoc hR e' a₀ y).symm
      _ = srMul hR a₀ y := by rw [he']
      _ = x := hy
  have hee : e' = e := by
    have h1 : srMul hR e' e = e' := hrid e'
    have h2 : srMul hR e' e = e := hlid e
    rw [← h1, h2]
  refine ⟨e, ?_, hrid⟩
  rw [← hee]; exact hlid

/-- ★H/R の各元に両側逆元が存在 (両側単位元 e のもとで) → srMul_assoc+exists_id と併せ H/R は群
    (Davvaz/Freni 基本関係定理の構造的完結). -/
theorem srMul_exists_inv {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R)
    (e : Quotient (srSetoid hR)) (hl : ∀ x, srMul hR e x = x) (hr : ∀ x, srMul hR x e = x)
    (x : Quotient (srSetoid hR)) :
    ∃ x', srMul hR x x' = e ∧ srMul hR x' x = e := by
  obtain ⟨xr, hxr⟩ := srMul_right_solvable hR x e
  obtain ⟨xl, hxl⟩ := srMul_left_solvable hR x e
  have hxlr : xl = xr := by
    calc xl = srMul hR xl e := (hr xl).symm
      _ = srMul hR xl (srMul hR x xr) := by rw [hxr]
      _ = srMul hR (srMul hR xl x) xr := (srMul_assoc hR xl x xr).symm
      _ = srMul hR e xr := by rw [hxl]
      _ = xr := hl xr
  refine ⟨xr, hxr, ?_⟩
  rw [← hxlr]; exact hxl

/-- ★★keystone 最強形: 強正則商 H/R は Lean `Group` インスタンス (基本関係定理の完全形式化).
    存在定理 srMul_exists_id/inv から Group.ofLeftAxioms で構成.
    外部 [Nonempty H] 不要 (srMul_exists_id が carrier_nonempty を内部供給). -/
@[reducible] noncomputable def srQuotientGroup {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) :
    Group (Quotient (srSetoid hR)) :=
  letI : Mul (Quotient (srSetoid hR)) := ⟨srMul hR⟩
  letI : One (Quotient (srSetoid hR)) := ⟨(srMul_exists_id hR).choose⟩
  letI : Inv (Quotient (srSetoid hR)) :=
    ⟨fun x => (srMul_exists_inv hR _ (srMul_exists_id hR).choose_spec.1
      (srMul_exists_id hR).choose_spec.2 x).choose⟩
  Group.ofLeftAxioms
    (fun a b c => srMul_assoc hR a b c)
    (fun a => (srMul_exists_id hR).choose_spec.1 a)
    (fun a => (srMul_exists_inv hR _ (srMul_exists_id hR).choose_spec.1
      (srMul_exists_id hR).choose_spec.2 a).choose_spec.2)

-- ── ★genuine multivalued example: total hypergroup (a∘b = H 全体, |H|≥2 で真に多価) ──
/-- helper: 全称ハイパー演算の hsmul は両 nonempty 集合で univ. -/
theorem hsmul_univ_of_nonempty {H : Type*} {A B : Set H} (hA : A.Nonempty) (hB : B.Nonempty) :
    hsmul (fun _ _ => (Set.univ : Set H)) A B = Set.univ := by
  ext z
  simp only [hsmul, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact ⟨a, ha, b, hb, trivial⟩

/-- ★genuine multivalued example: total hypergroup (a∘b = H 全体). 群誘導 singleton 例と対照. -/
def totalHypergroup (H : Type*) [Nonempty H] : Hypergroup H where
  hop := fun _ _ => Set.univ
  carrier_nonempty := inferInstance
  hop_nonempty := fun _ _ => Set.univ_nonempty
  hop_assoc := fun a b c => by
    show hsmul (fun _ _ => (Set.univ : Set H)) Set.univ {c}
       = hsmul (fun _ _ => (Set.univ : Set H)) {a} Set.univ
    rw [hsmul_univ_of_nonempty Set.univ_nonempty (Set.singleton_nonempty c),
        hsmul_univ_of_nonempty (Set.singleton_nonempty a) Set.univ_nonempty]
  repro_right := fun a => by
    ext z; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨Classical.arbitrary H, trivial⟩
  repro_left := fun a => by
    ext z; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨Classical.arbitrary H, trivial⟩

/-- ★total hypergroup は |H|≥2 で真に多価 (a∘b が異なる2元を含む)=genuinely multivalued の証拠. -/
theorem totalHypergroup_multivalued {H : Type*} [Nonempty H] {x y : H} (hxy : x ≠ y) (a b : H) :
    ∃ u v, u ∈ (totalHypergroup H).hop a b ∧ v ∈ (totalHypergroup H).hop a b ∧ u ≠ v :=
  ⟨x, y, Set.mem_univ x, Set.mem_univ y, hxy⟩

-- ── ★非自明な有限ハイパー群 (non-total): 2元 sign/Krasner hypergroup (査読 P1, Gemini 提案 S2) ──
/-- ★2元ハイパー群 ({false=e, true=a}, e=単位元, a∘a={e,a}=univ). 総ハイパー群より構造的=non-total. -/
def signHypergroup : Hypergroup Bool where
  carrier_nonempty := ⟨false⟩
  hop := fun a b => if a = false then {b} else if b = false then {a} else Set.univ
  hop_nonempty := fun a b => by rcases a <;> rcases b <;> simp
  hop_assoc := fun a b c => by
    rcases a <;> rcases b <;> rcases c <;>
      · ext z; rcases z <;> simp [hsmul]
  repro_right := fun a => by
    ext z; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]; rcases a
    · exact ⟨z, by simp⟩
    · exact ⟨true, by rcases z <;> simp⟩
  repro_left := fun a => by
    ext z; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]; rcases a
    · exact ⟨z, by rcases z <;> simp⟩
    · exact ⟨true, by rcases z <;> simp⟩

/-- ★signHypergroup は genuinely multivalued (a∘a={e,a} に異なる2元). -/
theorem signHypergroup_multivalued :
    ∃ u v, u ∈ signHypergroup.hop true true ∧ v ∈ signHypergroup.hop true true ∧ u ≠ v := by
  have h : signHypergroup.hop true true = Set.univ := by simp [signHypergroup]
  exact ⟨false, true, h ▸ Set.mem_univ _, h ▸ Set.mem_univ _, by decide⟩

/-- ★signHypergroup は non-total: e∘e={e}≠univ (総ハイパー群と区別=構造的有限例). -/
theorem signHypergroup_not_total :
    ∃ a b, signHypergroup.hop a b ≠ Set.univ := by
  refine ⟨false, false, ?_⟩
  have h : signHypergroup.hop false false = {false} := by simp [signHypergroup]
  rw [h]; intro he
  have : true ∈ ({false} : Set Bool) := he ▸ Set.mem_univ true
  simp at this


-- ════════ 基本関係 β=⋃ₙβₙ と普遍性 (Tier 1・[Rakhsh Khorshid–Ostadhadi-Dehkordi 2022] Thm 3.15 grounded) ════════
section HypergroupBeta
variable {H : Type*} (G : Hypergroup H)

/-- ハイパー積（先頭 `s`・前置リスト `rest`、右畳み込み）。
    `nProd G s [] = {s}`、`nProd G s (c :: rest) = {c} ∘ (nProd G s rest)`。 -/
def nProd (s : H) (rest : List H) : Set H :=
  rest.foldr (fun x acc => hsmul G.hop {x} acc) {s}

@[simp] theorem nProd_nil (s : H) : nProd G s [] = {s} := rfl

theorem nProd_cons (s c : H) (rest : List H) :
    nProd G s (c :: rest) = hsmul G.hop {c} (nProd G s rest) := rfl

/-- 基本関係 β: a,b が共通の有限ハイパー積に同居する（2770 定義3.14）. -/
def betaRel (a b : H) : Prop :=
  ∃ (s : H) (rest : List H), a ∈ nProd G s rest ∧ b ∈ nProd G s rest

/-- β* = β の同値閉包（推移閉包）. -/
def betaStar (a b : H) : Prop := Relation.EqvGen (betaRel G) a b

theorem betaRel_refl (a : H) : betaRel G a a :=
  ⟨a, [], by simp, by simp⟩

theorem betaRel_symm {a b : H} (h : betaRel G a b) : betaRel G b a := by
  obtain ⟨s, rest, ha, hb⟩ := h; exact ⟨s, rest, hb, ha⟩

theorem betaStar_equivalence : Equivalence (betaStar G) :=
  Relation.EqvGen.is_equivalence _

/-- ★補題（[Rakhsh Khorshid–Ostadhadi-Dehkordi 2022] Thm 3.15 第2部の核）: 強正則 R のもとで、ひとつのハイパー積
    `nProd G s rest` の元はすべて R-同値（積が単一 R-クラスへ潰れる）。リスト帰納 + `compat`。 -/
theorem nProd_single_class {R : H → H → Prop} (hR : StronglyRegular G R) (s : H) :
    ∀ (rest : List H), ∀ x ∈ nProd G s rest, ∀ y ∈ nProd G s rest, R x y := by
  intro rest
  induction rest with
  | nil =>
      intro x hx y hy
      simp only [nProd_nil, Set.mem_singleton_iff] at hx hy
      rw [hx, hy]
      exact hR.equiv.refl s
  | cons c t ih =>
      intro x hx y hy
      simp only [nProd_cons, hsmul, Set.mem_setOf_eq] at hx hy
      obtain ⟨a, ha, b, hb, hxab⟩ := hx
      obtain ⟨a', ha', b', hb', hyab⟩ := hy
      rw [Set.mem_singleton_iff] at ha ha'
      rw [ha] at hxab
      rw [ha'] at hyab
      exact hR.compat c c b b' (hR.equiv.refl c) (ih b hb b' hb') x hxab y hyab

/-- β ⊆ R （任意の強正則同値）: 共通積の元は単一クラスゆえ R-同値. -/
theorem betaRel_subset_of_stronglyRegular {R : H → H → Prop} (hR : StronglyRegular G R)
    {a b : H} (h : betaRel G a b) : R a b := by
  obtain ⟨s, rest, ha, hb⟩ := h
  exact nProd_single_class G hR s rest a ha b hb

/-- ★★Tier 1-d（普遍性の最小性方向・[Rakhsh Khorshid–Ostadhadi-Dehkordi 2022] Thm 3.15 第2部）:
    β* は任意の強正則同値 R に含まれる（β* ⊆ R）。
    ⟹ H/β* は最も粗い群化（任意の強正則群商が経由）. -/
theorem betaStar_subset_of_stronglyRegular {R : H → H → Prop} (hR : StronglyRegular G R)
    {a b : H} (h : betaStar G a b) : R a b := by
  unfold betaStar at h
  induction h with
  | rel x y hxy => exact betaRel_subset_of_stronglyRegular G hR hxy
  | refl x => exact hR.equiv.refl x
  | symm x y _ ih => exact hR.equiv.symm ih
  | trans x y z _ _ ihxy ihyz => exact hR.equiv.trans ihxy ihyz

/-- ★(A) 一般結合律: ハイパー積の集合レベル結合律（`hop_assoc` から `Set.ext` で導出）。
    両側 β* 強正則（右乗の積構造）に必要な標準メタ補題。 -/
theorem hsmul_assoc (A B C : Set H) :
    hsmul G.hop (hsmul G.hop A B) C = hsmul G.hop A (hsmul G.hop B C) := by
  ext z
  simp only [hsmul, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, ⟨a, ha, b, hb, hpab⟩, c, hc, hzpc⟩
    have h : z ∈ hsmul G.hop (G.hop a b) {c} := ⟨p, hpab, c, rfl, hzpc⟩
    rw [G.hop_assoc] at h
    simp only [hsmul, Set.mem_setOf_eq] at h
    obtain ⟨a', ha', q, hq, hzq⟩ := h
    rw [Set.mem_singleton_iff] at ha'
    rw [ha'] at hzq
    exact ⟨a, ha, q, ⟨b, hb, c, hc, hq⟩, hzq⟩
  · rintro ⟨a, ha, q, ⟨b, hb, c, hc, hqbc⟩, hzaq⟩
    have h : z ∈ hsmul G.hop {a} (G.hop b c) := ⟨a, rfl, q, hqbc, hzaq⟩
    rw [← G.hop_assoc] at h
    simp only [hsmul, Set.mem_setOf_eq] at h
    obtain ⟨p, hp, c', hc', hzpc⟩ := h
    rw [Set.mem_singleton_iff] at hc'
    rw [hc'] at hzpc
    exact ⟨p, ⟨a, ha, b, hb, hp⟩, c, hc, hzpc⟩

/-- ★(A) 積どうしの hsmul = 連結した1つの積（`hsmul_assoc` の r1 帰納）。両側性の鍵。 -/
theorem nProd_hsmul (s1 : H) (r1 : List H) (s2 : H) (r2 : List H) :
    hsmul G.hop (nProd G s1 r1) (nProd G s2 r2) = nProd G s2 (r1 ++ s1 :: r2) := by
  induction r1 with
  | nil => rw [nProd_nil, List.nil_append, nProd_cons]
  | cons c r1' ih => rw [nProd_cons, hsmul_assoc, ih, List.cons_append, nProd_cons]

/-- ★(A) 両側 compat の rel-rel 基底: βRel a a' ∧ βRel b b' ⟹ hop a b と hop a' b' は
    共通の積に入る（→ β* で結ばれる）。`nProd_hsmul` で右乗も1つの積に吸収。 -/
theorem betaRel_compat_both {a a' b b' : H}
    (ha : betaRel G a a') (hb : betaRel G b b') :
    ∀ u ∈ G.hop a b, ∀ v ∈ G.hop a' b', betaStar G u v := by
  obtain ⟨s1, r1, ha1, ha1'⟩ := ha
  obtain ⟨s2, r2, hb1, hb1'⟩ := hb
  intro u hu v hv
  have hP : nProd G s2 (r1 ++ s1 :: r2) = hsmul G.hop (nProd G s1 r1) (nProd G s2 r2) :=
    (nProd_hsmul G s1 r1 s2 r2).symm
  have hu' : u ∈ nProd G s2 (r1 ++ s1 :: r2) := by rw [hP]; exact ⟨a, ha1, b, hb1, hu⟩
  have hv' : v ∈ nProd G s2 (r1 ++ s1 :: r2) := by rw [hP]; exact ⟨a', ha1', b', hb1', hv⟩
  exact Relation.EqvGen.rel _ _ ⟨s2, r1 ++ s1 :: r2, hu', hv'⟩

/-- ★(A) β* の左引数を β* で持ち上げ（右引数 b 固定 → symm ケースが綺麗）。 -/
theorem betaStar_compat_left {a a' : H} (ha : betaStar G a a') :
    ∀ (b : H), ∀ u ∈ G.hop a b, ∀ v ∈ G.hop a' b, betaStar G u v := by
  unfold betaStar at ha
  induction ha with
  | rel x y hxy => intro b u hu v hv; exact betaRel_compat_both G hxy (betaRel_refl G b) u hu v hv
  | refl x => intro b u hu v hv; exact betaRel_compat_both G (betaRel_refl G x) (betaRel_refl G b) u hu v hv
  | symm x y _ ih => intro b u hu v hv; exact (betaStar_equivalence G).symm (ih b v hv u hu)
  | trans x y z _ _ ih1 ih2 =>
      intro b u hu v hv
      obtain ⟨w, hw⟩ := G.hop_nonempty y b
      exact (betaStar_equivalence G).trans (ih1 b u hu w hw) (ih2 b w hw v hv)

/-- ★(A) β* の右引数を β* で持ち上げ（左引数 a 固定）。 -/
theorem betaStar_compat_right {b b' : H} (hb : betaStar G b b') :
    ∀ (a : H), ∀ u ∈ G.hop a b, ∀ v ∈ G.hop a b', betaStar G u v := by
  unfold betaStar at hb
  induction hb with
  | rel x y hxy => intro a u hu v hv; exact betaRel_compat_both G (betaRel_refl G a) hxy u hu v hv
  | refl x => intro a u hu v hv; exact betaRel_compat_both G (betaRel_refl G a) (betaRel_refl G x) u hu v hv
  | symm x y _ ih => intro a u hu v hv; exact (betaStar_equivalence G).symm (ih a v hv u hu)
  | trans x y z _ _ ih1 ih2 =>
      intro a u hu v hv
      obtain ⟨w, hw⟩ := G.hop_nonempty a y
      exact (betaStar_equivalence G).trans (ih1 a u hu w hw) (ih2 a w hw v hv)

/-- ★★(A) β* は両側強正則（[Rakhsh Khorshid–Ostadhadi-Dehkordi 2022] Thm 3.15 第1部の両側拡張: 左→中間 w∈hop a' b→右 を β* 推移律で合成）。 -/
theorem betaStar_stronglyRegular : StronglyRegular G (betaStar G) where
  equiv := betaStar_equivalence G
  compat := by
    intro a a' b b' haa' hbb' u hu v hv
    obtain ⟨w, hw⟩ := G.hop_nonempty a' b
    exact (betaStar_equivalence G).trans
      (betaStar_compat_left G haa' b u hu w hw)
      (betaStar_compat_right G hbb' a' w hw v hv)

/-- ★★★(A) 普遍性の本体: 商 H/β* は群（既存 `srQuotientGroup` の REUSE）。
    `betaStar_subset_of_stronglyRegular`（β* は最小の強正則同値）と合わせ、H/β* は
    ★最も細かい(least-collapsed)群化＝基本群（任意の強正則商 H/R が H/β* の更なる商）。 -/
@[reducible] noncomputable def betaQuotientGroup :
    Group (Quotient (srSetoid (betaStar_stronglyRegular G))) :=
  srQuotientGroup (betaStar_stronglyRegular G)

/-- ★★★(A) 普遍性の factorization: β*⊆R（最小性）より、任意の強正則同値 R に対し
    標準商写像 H/β* → H/R が誘導される。これにより H/β* が「強正則群商の中で initial
    （全てがこれの更なる商）」＝普遍性が【写像として】検証される（[Rakhsh Khorshid–Ostadhadi-Dehkordi 2022] Thm 3.15 の写像版）。 -/
noncomputable def betaQuotientToSRQuotient {R : H → H → Prop} (hR : StronglyRegular G R) :
    Quotient (srSetoid (betaStar_stronglyRegular G)) → Quotient (srSetoid hR) :=
  Quotient.lift (fun a => Quotient.mk (srSetoid hR) a)
    (fun _ _ hab => Quotient.sound (betaStar_subset_of_stronglyRegular G hR hab))

/-- ★ factorization が射影と可換（H → H/β* → H/R = H → H/R）。 -/
theorem betaQuotientToSRQuotient_comm {R : H → H → Prop} (hR : StronglyRegular G R) (a : H) :
    betaQuotientToSRQuotient G hR (Quotient.mk (srSetoid (betaStar_stronglyRegular G)) a)
      = Quotient.mk (srSetoid hR) a := rfl

/-- ★★(P0-2) factorization は商の積を保つ（群準同型）。srMul_eq_of_mem で両辺を代表元 c の class に落として一致。 -/
theorem betaQuotientToSRQuotient_preserves_srMul {R : H → H → Prop} (hR : StronglyRegular G R)
    (x y : Quotient (srSetoid (betaStar_stronglyRegular G))) :
    betaQuotientToSRQuotient G hR (srMul (betaStar_stronglyRegular G) x y)
      = srMul hR (betaQuotientToSRQuotient G hR x) (betaQuotientToSRQuotient G hR y) := by
  refine Quotient.inductionOn₂ x y (fun a b => ?_)
  obtain ⟨c, hc⟩ := G.hop_nonempty a b
  rw [srMul_eq_of_mem (betaStar_stronglyRegular G) a b c hc, betaQuotientToSRQuotient_comm,
      betaQuotientToSRQuotient_comm, betaQuotientToSRQuotient_comm, srMul_eq_of_mem hR a b c hc]

/-- ★★(P0-2) factorization は射影と可換な唯一の写像（uniqueness）。preserves_srMul と合わせ
    H/β* は強正則群商の中で initial＝普遍性が圏論的にも正当化される。 -/
theorem betaQuotientToSRQuotient_unique {R : H → H → Prop} (hR : StronglyRegular G R)
    (f : Quotient (srSetoid (betaStar_stronglyRegular G)) → Quotient (srSetoid hR))
    (hf : ∀ a, f (Quotient.mk (srSetoid (betaStar_stronglyRegular G)) a)
              = Quotient.mk (srSetoid hR) a) :
    f = betaQuotientToSRQuotient G hR := by
  funext x
  refine Quotient.inductionOn x (fun a => ?_)
  rw [hf a]
  exact (betaQuotientToSRQuotient_comm G hR a).symm

/-- ★(P1-3) 強正則の核: 単一の積 a∘b は R で単一クラスに潰れる（hR.compat の対角適用）=
    集合値積が商上で単一値演算になる本質。 -/
theorem srProduct_single_class {R : H → H → Prop} (hR : StronglyRegular G R) (a b : H) :
    ∀ u ∈ G.hop a b, ∀ v ∈ G.hop a b, R u v := by
  intro u hu v hv
  exact hR.compat a a b b (hR.equiv.refl a) (hR.equiv.refl b) u hu v hv

/-- ★(P1-2) 符号ハイパー群(carrier=Bool, e=false, a=true; a∘a=univ) の β* は universal:
    全元が共通積 nProd true [true]=univ に同居 → 全ペアが β*。 -/
theorem signHypergroup_betaStar_universal : ∀ x y : Bool, betaStar signHypergroup x y := by
  have hft : betaStar signHypergroup false true := by
    apply Relation.EqvGen.rel
    refine ⟨true, [true], ?_, ?_⟩ <;>
      (rw [nProd_cons, nProd_nil]; exact ⟨true, rfl, true, rfl, by simp [signHypergroup]⟩)
  intro x y
  cases x <;> cases y
  · exact (betaStar_equivalence signHypergroup).refl false
  · exact hft
  · exact (betaStar_equivalence signHypergroup).symm hft
  · exact (betaStar_equivalence signHypergroup).refl true

/-- ★(P1-2) 従って符号ハイパー群の基本商 H/β* は自明群（subsingleton）= pipeline 全段を有限例で検査。 -/
theorem signHypergroup_betaQuotient_subsingleton :
    Subsingleton (Quotient (srSetoid (betaStar_stronglyRegular signHypergroup))) := by
  constructor
  intro x y
  refine Quotient.inductionOn₂ x y (fun a b => ?_)
  exact Quotient.sound (signHypergroup_betaStar_universal a b)

-- ════════ ★文献の片側強正則性との同値 ([Afshar–Ameri 2025] Def. 2.1 / Davvaz) ════════
-- paper future work「StronglyRegular ↔ 文献定義の同値」を解消。文献 Def 2.1:
-- 右強正則 = a R b ⟹ ∀x, a∘x と b∘x の全要素が R 関係 (A R̄̄ B), 左も同様。強正則 = 右∧左。
/-- 文献 [Afshar–Ameri 2025] Def. 2.1の右強正則性: `R a b` なら任意の `x` で `a∘x` と `b∘x` の全要素が `R`。 -/
def RightStronglyRegular (R : H → H → Prop) : Prop :=
  ∀ ⦃a b⦄, R a b → ∀ x, ∀ u ∈ G.hop a x, ∀ v ∈ G.hop b x, R u v

/-- 文献 [Afshar–Ameri 2025] Def. 2.1の左強正則性。 -/
def LeftStronglyRegular (R : H → H → Prop) : Prop :=
  ∀ ⦃a b⦄, R a b → ∀ x, ∀ u ∈ G.hop x a, ∀ v ∈ G.hop x b, R u v

/-- ★complete-part 形 `StronglyRegular` ⟹ 文献の右・左片側強正則（compat を片側に特化）。 -/
theorem stronglyRegular_to_oneSided {R : H → H → Prop} (hR : StronglyRegular G R) :
    RightStronglyRegular G R ∧ LeftStronglyRegular G R := by
  refine ⟨?_, ?_⟩
  · intro a b hab x u hu v hv
    exact hR.compat a b x x hab (hR.equiv.refl x) u hu v hv
  · intro a b hab x u hu v hv
    exact hR.compat x x a b (hR.equiv.refl x) hab u hu v hv

/-- ★★文献の右∧左片側強正則 + R 同値 ⟹ complete-part 形 `StronglyRegular`
    （中間元 w∈hop a' b を取り、右で u↦w・左で w↦v を関係づけ R 推移律で合成）。
    `stronglyRegular_to_oneSided` と合わせ両形は同値 = paper future work を解消 ([Afshar–Ameri 2025] Def. 2.1)。 -/
theorem stronglyRegular_of_oneSided {R : H → H → Prop} (hequiv : Equivalence R)
    (hright : RightStronglyRegular G R) (hleft : LeftStronglyRegular G R) :
    StronglyRegular G R where
  equiv := hequiv
  compat := by
    intro a a' b b' haa' hbb' u hu v hv
    obtain ⟨w, hw⟩ := G.hop_nonempty a' b
    exact hequiv.trans (hright haa' b u hu w hw) (hleft hbb' a' w hw v hv)

-- ════════ ★完全部分 (complete part) と強正則類の完全部分性 ([Afshar–Ameri 2025] L153/L219, Corsini/Davvaz) ════════
/-- 文献([Afshar–Ameri 2025] L153)の完全部分: 任意の n 元ハイパー積 `nProd s rest` が `C` と交われば積全体が `C` に含まれる。 -/
def IsCompletePart (C : Set H) : Prop :=
  ∀ (s : H) (rest : List H), (∃ z, z ∈ C ∧ z ∈ nProd G s rest) → nProd G s rest ⊆ C

/-- ★強正則 `R` の各同値類 `{x | R a x}` は完全部分。
    `nProd_single_class`(積は単一 R 類に収まる) + R 推移律で証明。
    [Afshar–Ameri 2025] L153 完全部分定義 + L219 (S_ρ の完全部分性) の一般化 (古典 Corsini/Davvaz)。 -/
theorem rClass_isCompletePart {R : H → H → Prop} (hR : StronglyRegular G R) (a : H) :
    IsCompletePart G {x | R a x} := by
  rintro s rest ⟨z, hzC, hz⟩ w hw
  simp only [Set.mem_setOf_eq] at hzC ⊢
  exact hR.equiv.trans hzC (nProd_single_class G hR s rest z hz w hw)

/-- ★完全部分は任意交叉で閉じる: 各 `C i` が完全部分なら `⋂ i, C i` も完全部分。
    完全閉包(集合を含む最小の完全部分)・導来部分ハイパー群の交叉定義 ([Afshar–Ameri 2025] L205) の根拠 (Corsini-Davvaz)。 -/
theorem isCompletePart_iInter {ι : Type*} {C : ι → Set H}
    (hC : ∀ i, IsCompletePart G (C i)) : IsCompletePart G (⋂ i, C i) := by
  rintro s rest ⟨z, hzC, hz⟩ w hw
  rw [Set.mem_iInter] at hzC ⊢
  intro i
  exact hC i s rest ⟨z, hzC i, hz⟩ hw

-- ════════ ★完全閉包 (complete closure) = X を含む最小の完全部分 ([Afshar–Ameri 2025] L205, Corsini-Davvaz) ════════
/-- 集合 `X` の完全閉包: `X` を含むすべての完全部分の共通部分。 -/
def completeClosure (X : Set H) : Set H :=
  ⋂ (C : {C : Set H // X ⊆ C ∧ IsCompletePart G C}), C.1

/-- ★完全閉包は完全部分 (完全部分族の交叉ゆえ, `isCompletePart_iInter` と同技法)。 -/
theorem completeClosure_isCompletePart (X : Set H) :
    IsCompletePart G (completeClosure G X) := by
  rintro s rest ⟨z, hzC, hz⟩ w hw
  unfold completeClosure at hzC ⊢
  rw [Set.mem_iInter] at hzC ⊢
  intro C
  exact C.2.2 s rest ⟨z, hzC C, hz⟩ hw

/-- ★`X` は自身の完全閉包に含まれる。 -/
theorem subset_completeClosure (X : Set H) : X ⊆ completeClosure G X := by
  intro x hx
  unfold completeClosure
  rw [Set.mem_iInter]
  intro C
  exact C.2.1 hx

/-- ★完全閉包の最小性: `X` を含む任意の完全部分 `D` は完全閉包を含む。
    上3つで「完全閉包 = X を含む最小の完全部分」を特徴づけ ([Afshar–Ameri 2025] L205 導来部分ハイパー群の交叉定義の枠組み)。 -/
theorem completeClosure_minimal (X D : Set H) (hXD : X ⊆ D) (hD : IsCompletePart G D) :
    completeClosure G X ⊆ D := by
  intro x hx
  unfold completeClosure at hx
  rw [Set.mem_iInter] at hx
  exact hx ⟨D, hXD, hD⟩

/-- ★完全閉包の単調性 ([Gutan 1996] §2 Property 3): `X ⊆ Y` なら `completeClosure X ⊆ completeClosure Y`
    (`completeClosure Y` は X⊇ を含む完全部分ゆえ最小性で). -/
theorem completeClosure_mono {X Y : Set H} (h : X ⊆ Y) :
    completeClosure G X ⊆ completeClosure G Y :=
  completeClosure_minimal G X (completeClosure G Y)
    (Set.Subset.trans h (subset_completeClosure G Y)) (completeClosure_isCompletePart G Y)

/-- ★完全閉包の冪等性 ([Gutan 1996] §2 Property 2): `completeClosure (completeClosure X) = completeClosure X`
    (完全閉包は完全部分ゆえ最小性で⊆, subset_completeClosure で⊇, 反対称律). -/
theorem completeClosure_idem (X : Set H) :
    completeClosure G (completeClosure G X) = completeClosure G X :=
  Set.Subset.antisymm
    (completeClosure_minimal G (completeClosure G X) (completeClosure G X)
      subset_rfl (completeClosure_isCompletePart G X))
    (subset_completeClosure G (completeClosure G X))

-- ════════ ★橋渡し: 完全部分/完全閉包理論 ⟷ 基本関係 β* ([Gutan 1996]/Koskas, 理論の目的) ════════
/-- ★基本関係 β* の各類は完全部分 (β* は強正則ゆえ #2 を適用)。
    完全部分理論が β*(基本群)と結びつく核心 ([Gutan 1996] §2 + Koskas)。 -/
theorem betaStar_class_isCompletePart (a : H) :
    IsCompletePart G {x | betaStar G a x} :=
  rClass_isCompletePart G (betaStar_stronglyRegular G) a

/-- ★単項集合の完全閉包は β* 類に含まれる: `completeClosure {a} ⊆ {x | β* a x}`。
    β*(a) は a を含む完全部分ゆえ完全閉包の最小性 (#5) で従う ([Gutan 1996] §2)。 -/
theorem completeClosure_singleton_subset_betaStarClass (a : H) :
    completeClosure G {a} ⊆ {x | betaStar G a x} := by
  apply completeClosure_minimal G {a} {x | betaStar G a x} _ (betaStar_class_isCompletePart G a)
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [Set.mem_setOf_eq, hx]
  exact (betaStar_equivalence G).refl a

/-- ★完全部分 `C` の完全閉包は `C` 自身: `completeClosure C = C` (閉包作用素の不動点 ⟺ 完全部分)。
    最小性 (C⊆C で 𝒞C⊆C) + 包含 (C⊆𝒞C) の反対称律。閉包作用素3法則 (拡大/単調/冪等) を完備。 -/
theorem completeClosure_eq_self {C : Set H} (hC : IsCompletePart G C) :
    completeClosure G C = C :=
  Set.Subset.antisymm (completeClosure_minimal G C C subset_rfl hC) (subset_completeClosure G C)

/-- ★全体集合は完全部分 (任意のハイパー積は univ に含まれる)。 -/
theorem isCompletePart_univ : IsCompletePart G (Set.univ : Set H) := by
  rintro s rest _ w _
  exact Set.mem_univ w

-- ════════ ★大域的冪等性 と β-1ステップ⊆完全閉包 ([Gutan 1996] §3) ════════
/-- ★超群は大域的冪等: `H∘H = H`。reproduction(右可解性 `hypergroup_right_solvable`)から
    任意の x は或る積 a∘b に属す。[Gutan 1996] §3 定理3.1(βₙ 増大列 ⟺ H=H∘H)の前提。 -/
theorem hsmul_univ_univ : hsmul G.hop (Set.univ : Set H) (Set.univ : Set H) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨a⟩ := G.carrier_nonempty
  obtain ⟨b, hb⟩ := hypergroup_right_solvable G a x
  exact ⟨a, Set.mem_univ a, b, Set.mem_univ b, hb⟩

/-- ★β の1ステップは完全閉包に着地: `betaRel a b → b ∈ completeClosure {a}`。
    a,b が共通ハイパー積 Q に同居 ⟹ 𝒞({a})∩Q∋a ⟹ (𝒞({a})完全部分ゆえ)Q⊆𝒞({a}) ⟹ b∈𝒞({a})。
    Gutan の特徴づけ「x β* y ⟺ x∈𝒞(y)」([Gutan 1996] §3 L282)の基礎ステップ。 -/
theorem betaRel_subset_completeClosure {a b : H} (h : betaRel G a b) :
    b ∈ completeClosure G {a} := by
  obtain ⟨s, rest, ha, hb⟩ := h
  refine completeClosure_isCompletePart G {a} s rest ⟨a, ?_, ha⟩ hb
  exact subset_completeClosure G {a} rfl

-- ════════ ★Gutan §3 補題3.2: ハイパー積はより長い積へ拡張可能 (βₙ 増大の鍵) ════════
/-- ★`hsmul` は右引数について単調 (B⊆C ⟹ A∘B⊆A∘C)。 -/
theorem hsmul_mono_right {A B C : Set H} (h : B ⊆ C) :
    hsmul G.hop A B ⊆ hsmul G.hop A C := by
  rintro z ⟨a, ha, b, hb, hz⟩
  exact ⟨a, ha, b, h hb, hz⟩

/-- ★([Gutan 1996] §3 補題3.2) `s ∈ p∘q` なら積 `nProd s rest` は1因子長い積 `nProd q (rest++[p])` に含まれる
    (底 `{s}⊆p∘q` を foldr 単調性で持ち上げ)。 -/
theorem nProd_subset_extend {s p q : H} (hs : s ∈ G.hop p q) :
    ∀ (rest : List H), nProd G s rest ⊆ nProd G q (rest ++ [p]) := by
  intro rest
  induction rest with
  | nil =>
    simp only [List.nil_append, nProd_nil, nProd_cons]
    exact Set.singleton_subset_iff.mpr ⟨p, rfl, q, rfl, hs⟩
  | cons c rest' ih =>
    rw [nProd_cons, List.cons_append, nProd_cons]
    exact hsmul_mono_right G ih

/-- ★([Gutan 1996] §3 補題3.2 完全版) 超群では任意の積はより長い積に含まれる
    (大域的冪等 reproduction で底 s を s∈a∘q と分解)。 -/
theorem nProd_exists_extend (s : H) (rest : List H) :
    ∃ p q, nProd G s rest ⊆ nProd G q (rest ++ [p]) := by
  obtain ⟨a⟩ := G.carrier_nonempty
  obtain ⟨q, hq⟩ := hypergroup_right_solvable G a s
  exact ⟨a, q, nProd_subset_extend G hq rest⟩

/-- ★完全閉包の吸収性: `b ∈ 𝒞({a})` なら `𝒞({b}) ⊆ 𝒞({a})` (最小性で)。
    β* ⟷ 𝒞 特徴づけの推移ステップ ([Gutan 1996] §2)。 -/
theorem completeClosure_singleton_subset_of_mem {a b : H} (h : b ∈ completeClosure G {a}) :
    completeClosure G {b} ⊆ completeClosure G {a} :=
  completeClosure_minimal G {b} (completeClosure G {a})
    (Set.singleton_subset_iff.mpr h) (completeClosure_isCompletePart G {a})

-- ════════ ★★★Gutan 1996 定理4.1: β の推移性の特徴づけ ([Gutan 1996] §2/§3/§4) ════════
-- ★源の限定: 原典は【半超群】で述べる。本ライブラリには Semihypergroup 構造が無いため
--   【超群】(再生公理つき) で述べている。以下の証明は再生公理を一切使っていないので
--   Semihypergroup 構造を導入すれば literal 一般形へそのまま移せる (future work)。

/-- ★([Gutan 1996] §2) 1ステップ完全閉包 `𝒞₁(B) = ⋃{Q ∈ P(H) | Q ∩ B ≠ ∅}`。
    P(H) の元は本ライブラリでは `nProd G s rest` (先頭 s・前置リスト rest) で表される。 -/
def completeClosure1 (B : Set H) : Set H :=
  {z | ∃ (s : H) (rest : List H), z ∈ nProd G s rest ∧ ∃ b ∈ B, b ∈ nProd G s rest}

/-- ★β と 𝒞₁ の橋渡し: `b ∈ 𝒞₁({a}) ⟺ a β b`
    (どちらも「a,b が共通のハイパー積に同居する」の言い換え)。 -/
theorem mem_completeClosure1_singleton_iff {a b : H} :
    b ∈ completeClosure1 G {a} ↔ betaRel G a b := by
  constructor
  · rintro ⟨s, rest, hb, x, hx, hxQ⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨s, rest, hxQ, hb⟩
  · rintro ⟨s, rest, ha, hb⟩
    exact ⟨s, rest, hb, a, rfl, ha⟩

/-- ★([Gutan 1996] §2 性質1 の 1ステップ版) `B ⊆ 𝒞₁(B)`
    (単項積 `nProd b [] = {b}` が B と交わる)。 -/
theorem subset_completeClosure1 (B : Set H) : B ⊆ completeClosure1 G B := by
  intro b hb
  exact ⟨b, [], by simp, b, hb, by simp⟩

/-- ★`𝒞₁(B) ⊆ 𝒞(B)`: 𝒞(B) は B を含む完全部分ゆえ、B と交わる積は丸ごと 𝒞(B) に入る。 -/
theorem completeClosure1_subset_completeClosure (B : Set H) :
    completeClosure1 G B ⊆ completeClosure G B := by
  rintro z ⟨s, rest, hz, b, hbB, hbQ⟩
  exact completeClosure_isCompletePart G B s rest ⟨b, subset_completeClosure G B hbB, hbQ⟩ hz

/-- ★(定理4.1 逆向きの心臓部) β が推移的なら `𝒞₁({x})` は完全部分。
    源の証明: Q ∩ 𝒞₁(x) ≠ ∅ とすると x ∈ Q′ かつ Q ∩ Q′ ≠ ∅ なる Q′ が取れ、
    y ∈ Q ∩ Q′・z ∈ Q に対し z β y かつ y β x ゆえ推移性で z β x、よって Q ⊆ 𝒞₁(x)。 -/
theorem completeClosure1_isCompletePart_of_transitive
    (htr : ∀ a b c : H, betaRel G a b → betaRel G b c → betaRel G a c) (x : H) :
    IsCompletePart G (completeClosure1 G {x}) := by
  rintro s rest ⟨y, hy, hyQ⟩ z hz
  rw [mem_completeClosure1_singleton_iff] at hy ⊢
  exact htr _ _ _ hy (betaRel_symm G ⟨s, rest, hz, hyQ⟩)

/-- ★★★([Gutan 1996] 定理4.1) **β が推移的 ⟺ 任意の x で 𝒞(x) = 𝒞₁(x)**。
    (⟹) 𝒞₁({x}) が完全部分かつ x を含むゆえ 𝒞 の最小性で 𝒞 ⊆ 𝒞₁、逆は常に成立。
    (⟸) a β b, b β c から b ∈ 𝒞(a)、b を含む積 Q′ は完全部分 𝒞(a) に丸ごと入るので
         c ∈ 𝒞(a) = 𝒞₁(a)、すなわち a β c。
    ★原典は半超群で述べる (上記の限定を参照)。 -/
theorem betaRel_transitive_iff_completeClosure_eq_one :
    (∀ a b c : H, betaRel G a b → betaRel G b c → betaRel G a c) ↔
      ∀ x : H, completeClosure G {x} = completeClosure1 G {x} := by
  constructor
  · intro htr x
    apply Set.Subset.antisymm
    · exact completeClosure_minimal G {x} (completeClosure1 G {x})
        (Set.singleton_subset_iff.mpr (subset_completeClosure1 G {x} rfl))
        (completeClosure1_isCompletePart_of_transitive G htr x)
    · exact completeClosure1_subset_completeClosure G {x}
  · intro h a b c hab hbc
    have hb : b ∈ completeClosure G {a} := betaRel_subset_completeClosure G hab
    obtain ⟨s, rest, hbQ, hcQ⟩ := hbc
    have hc : c ∈ completeClosure G {a} :=
      completeClosure_isCompletePart G {a} s rest ⟨b, hb, hbQ⟩ hcQ
    rw [h a] at hc
    exact (mem_completeClosure1_singleton_iff G).mp hc

/-- ★(定理4.1 の帰結) β が推移的なら **β = β\***
    (β は既に反射的・対称的ゆえ、推移性が加われば同値関係となり同値閉包は自分自身)。 -/
theorem betaStar_iff_betaRel_of_transitive
    (htr : ∀ a b c : H, betaRel G a b → betaRel G b c → betaRel G a c) (a b : H) :
    betaStar G a b ↔ betaRel G a b := by
  have key : ∀ x y : H, Relation.EqvGen (betaRel G) x y → betaRel G x y := by
    intro x y hxy
    induction hxy with
    | rel u v huv => exact huv
    | refl u => exact betaRel_refl G u
    | symm u v _ ih => exact betaRel_symm G ih
    | trans u v w _ _ ih1 ih2 => exact htr _ _ _ ih1 ih2
  constructor
  · intro h
    have h' : Relation.EqvGen (betaRel G) a b := h
    exact key a b h'
  · intro h
    exact Relation.EqvGen.rel _ _ h

/-- ★([Gutan 1996] §3 L282 の特徴づけ) **x β\* y ⟺ y ∈ 𝒞({x})**。
    (←) は既存 `completeClosure_singleton_subset_betaStarClass`。
    (→) は「β の1ステップは 𝒞 を変えない」(吸収性を両向きに使う) を EqvGen で持ち上げる。 -/
theorem betaStar_iff_mem_completeClosure {a b : H} :
    betaStar G a b ↔ b ∈ completeClosure G {a} := by
  constructor
  · intro h
    have key : ∀ x y : H, betaRel G x y →
        completeClosure G {x} = completeClosure G {y} := by
      intro x y hxy
      exact Set.Subset.antisymm
        (completeClosure_singleton_subset_of_mem G
          (betaRel_subset_completeClosure G (betaRel_symm G hxy)))
        (completeClosure_singleton_subset_of_mem G (betaRel_subset_completeClosure G hxy))
    have step : ∀ x y : H, Relation.EqvGen (betaRel G) x y →
        completeClosure G {x} = completeClosure G {y} := by
      intro x y hxy
      induction hxy with
      | rel u v huv => exact key u v huv
      | refl u => rfl
      | symm u v _ ih => exact ih.symm
      | trans u v w _ _ ih1 ih2 => exact ih1.trans ih2
    have h' : Relation.EqvGen (betaRel G) a b := h
    rw [step a b h']
    exact subset_completeClosure G {b} rfl
  · intro h
    exact completeClosure_singleton_subset_betaStarClass G a h
end HypergroupBeta

-- ════════════════════════════════════════════════════════════════════════════
-- ★★★ 強正則商は群【関係版・公理ゼロ】 — 同じ定理の第2提示 (2026-08-01)
--   既存 srQuotientGroup は Quotient 型を作るため代表元を data として取り出す必要があり
--   Classical.choice を引く (硬度2)。ここでは Bishop 流の setoid 提示に置き換える:
--   台は H のまま・等号は R・積は「c が a∘b の代表元」という【関係】。集合の等号を
--   一切証明しないので propext / Quot.sound も引かない ⇒ 公理ゼロ (硬度4)。
--   ★選択公理を消せば排中律も消える (Lean の Classical.em は Classical.choice から
--     Diaconescu で導かれる) ため、本提示は AC・LEM・外延性のいずれも使わない。
--   ★これはフェーズ(B)=表現の変更。原典忠実な srMul/srQuotientGroup 版は残置し並置する。
-- ════════════════════════════════════════════════════════════════════════════

/-- ★再生公理 ⟹ 右可解性【公理ゼロ版】。既存 `hypergroup_right_solvable` と同じ主張だが、
    `simpa only [Set.mem_iUnion]` (Iff 書き換え=propext) を `Set.mem_iUnion.mp` (純項) に置換。 -/
theorem hypergroup_right_solvable_af {H : Type*} (G : Hypergroup H) (a b : H) :
    ∃ x, b ∈ G.hop a x := by
  have h : b ∈ (⋃ x, G.hop a x) := by rw [G.repro_right]; exact Set.mem_univ b
  exact Set.mem_iUnion.mp h

/-- ★再生公理 ⟹ 左可解性【公理ゼロ版】。 -/
theorem hypergroup_left_solvable_af {H : Type*} (G : Hypergroup H) (a b : H) :
    ∃ x, b ∈ G.hop x a := by
  have h : b ∈ (⋃ x, G.hop x a) := by rw [G.repro_left]; exact Set.mem_univ b
  exact Set.mem_iUnion.mp h

/-- ★商 H/R における積の関係版: 「c は a⊗b の代表元」= a∘b の元がすべて c と R-同値。
    強正則性より a∘b は単一 R 類なので、これは代表元の取り方に依らない。 -/
def IsProdMod {H : Type*} (G : Hypergroup H) (R : H → H → Prop) (a b c : H) : Prop :=
  ∀ u ∈ G.hop a b, R c u

/-- ★積の存在 (a∘b が空でないことから)。選択は不要 = 存在は Prop の中で消費される。 -/
theorem srRel_prod_exists {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) (a b : H) : ∃ c, IsProdMod G R a b c := by
  obtain ⟨c, hc⟩ := G.hop_nonempty a b
  exact ⟨c, fun u hu => srProduct_single_class G hR a b c hc u hu⟩

/-- ★積の一意性 (R の意味で): 代表元は R を除いて一意。 -/
theorem srRel_prod_unique {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) {a b c c' : H}
    (h : IsProdMod G R a b c) (h' : IsProdMod G R a b c') : R c c' := by
  obtain ⟨u, hu⟩ := G.hop_nonempty a b
  exact hR.equiv.trans (h u hu) (hR.equiv.symm (h' u hu))

/-- ★well-defined 性: 入力を R-同値で取り替えても積は R-同値。
    (これが「多価演算が商で単価になる」ことの内容。代表元選択は使っていない。) -/
theorem srRel_prod_wd {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) {a a' b b' c c' : H}
    (ha : R a a') (hb : R b b') (h : IsProdMod G R a b c) (h' : IsProdMod G R a' b' c') :
    R c c' := by
  obtain ⟨u, hu⟩ := G.hop_nonempty a b
  obtain ⟨v, hv⟩ := G.hop_nonempty a' b'
  exact hR.equiv.trans (h u hu)
    (hR.equiv.trans (hR.compat a a' b b' ha hb u hu v hv) (hR.equiv.symm (h' v hv)))

/-- ★結合律 (R の意味で): u が a⊗b・p が u⊗c・v が b⊗c・q が a⊗v の代表元なら R p q。
    集合の等号は証明せず、構造体フィールド `hop_assoc` を消費するだけ。 -/
theorem srRel_assoc {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) {a b c u p v q : H}
    (hu : IsProdMod G R a b u) (hp : IsProdMod G R u c p)
    (hv : IsProdMod G R b c v) (hq : IsProdMod G R a v q) : R p q := by
  obtain ⟨w, hw⟩ := G.hop_nonempty a b
  obtain ⟨z, hz⟩ := G.hop_nonempty w c
  have hpz : R p z := by
    obtain ⟨y, hy⟩ := G.hop_nonempty u c
    exact hR.equiv.trans (hp y hy)
      (hR.compat u w c c (hu w hw) (hR.equiv.refl c) y hy z hz)
  have h1 : z ∈ hsmul G.hop (G.hop a b) {c} := ⟨w, hw, c, rfl, hz⟩
  have h2 : z ∈ hsmul G.hop {a} (G.hop b c) := by rw [← G.hop_assoc a b c]; exact h1
  obtain ⟨a', ha', v', hv', hz'⟩ := h2
  have haa : a' = a := ha'
  have hz'' : z ∈ G.hop a v' := haa ▸ hz'
  have hqz : R q z := by
    obtain ⟨y, hy⟩ := G.hop_nonempty a v
    exact hR.equiv.trans (hq y hy)
      (hR.compat a a v v' (hR.equiv.refl a) (hv v' hv') y hy z hz'')
  exact hR.equiv.trans hpz (hR.equiv.symm hqz)

/-- ★右可解 (R の意味で): 任意の a,b に対し b が a⊗x の代表元となる x が存在。 -/
theorem srRel_right_solvable {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) (a b : H) : ∃ x, IsProdMod G R a x b := by
  obtain ⟨x, hx⟩ := hypergroup_right_solvable_af G a b
  exact ⟨x, fun u hu => srProduct_single_class G hR a x b hx u hu⟩

/-- ★左可解 (R の意味で)。 -/
theorem srRel_left_solvable {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) (a b : H) : ∃ y, IsProdMod G R y a b := by
  obtain ⟨y, hy⟩ := hypergroup_left_solvable_af G a b
  exact ⟨y, fun u hu => srProduct_single_class G hR y a b hy u hu⟩

/-- ★★両側単位元の存在 (R の意味で): ∃e, ∀x, x 自身が e⊗x と x⊗e の代表元。
    証明は既存 `srMul_exists_id` (半群+両側可解→大域単位元) の関係版。 -/
theorem srRel_exists_id {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) :
    ∃ e : H, ∀ x : H, IsProdMod G R e x x ∧ IsProdMod G R x e x := by
  obtain ⟨a₀⟩ := G.carrier_nonempty
  obtain ⟨e, he⟩ := hypergroup_right_solvable_af G a₀ a₀
  obtain ⟨e', he'⟩ := hypergroup_left_solvable_af G a₀ a₀
  have hrid : ∀ x : H, IsProdMod G R x e x := by
    intro x u hu
    obtain ⟨y, hy⟩ := hypergroup_left_solvable_af G a₀ x
    have h1 : u ∈ hsmul G.hop (G.hop y a₀) {e} := ⟨x, hy, e, rfl, hu⟩
    have h2 : u ∈ hsmul G.hop {y} (G.hop a₀ e) := by rw [← G.hop_assoc y a₀ e]; exact h1
    obtain ⟨y', hy', w, hw, huw⟩ := h2
    have hyy : y' = y := hy'
    have huw' : u ∈ G.hop y w := hyy ▸ huw
    exact hR.compat y y a₀ w (hR.equiv.refl y)
      (srProduct_single_class G hR a₀ e a₀ he w hw) x hy u huw'
  have hlid : ∀ x : H, IsProdMod G R e' x x := by
    intro x u hu
    obtain ⟨y, hy⟩ := hypergroup_right_solvable_af G a₀ x
    have h1 : u ∈ hsmul G.hop {e'} (G.hop a₀ y) := ⟨e', rfl, x, hy, hu⟩
    have h2 : u ∈ hsmul G.hop (G.hop e' a₀) {y} := by rw [G.hop_assoc e' a₀ y]; exact h1
    obtain ⟨w, hw, y', hy', huw⟩ := h2
    have hyy : y' = y := hy'
    have huw' : u ∈ G.hop w y := hyy ▸ huw
    exact hR.compat a₀ w y y (srProduct_single_class G hR e' a₀ a₀ he' w hw)
      (hR.equiv.refl y) x hy u huw'
  have hee : R e' e := by
    obtain ⟨u, hu⟩ := G.hop_nonempty e' e
    exact hR.equiv.trans (hrid e' u hu) (hR.equiv.symm (hlid e u hu))
  refine ⟨e, fun x => ⟨?_, hrid x⟩⟩
  intro u hu
  obtain ⟨p, hp⟩ := G.hop_nonempty e' x
  exact hR.equiv.trans (hlid x p hp)
    (hR.compat e' e x x hee (hR.equiv.refl x) p hp u hu)

/-- ★★両側逆元の存在 (R の意味で)。既存 `srMul_exists_inv` の関係版。 -/
theorem srRel_exists_inv {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) (e : H)
    (hid : ∀ x : H, IsProdMod G R e x x ∧ IsProdMod G R x e x) (x : H) :
    ∃ x', IsProdMod G R x x' e ∧ IsProdMod G R x' x e := by
  obtain ⟨xr, hxr⟩ := hypergroup_right_solvable_af G x e
  obtain ⟨xl, hxl⟩ := hypergroup_left_solvable_af G x e
  have hxrP : IsProdMod G R x xr e := fun u hu => srProduct_single_class G hR x xr e hxr u hu
  have hxlP : IsProdMod G R xl x e := fun u hu => srProduct_single_class G hR xl x e hxl u hu
  have hlr : R xl xr := by
    obtain ⟨u, hu⟩ := G.hop_nonempty xl e
    have h1 : R xl u := (hid xl).2 u hu
    have h2 : u ∈ hsmul G.hop {xl} (G.hop x xr) := ⟨xl, rfl, e, hxr, hu⟩
    have h3 : u ∈ hsmul G.hop (G.hop xl x) {xr} := by rw [G.hop_assoc xl x xr]; exact h2
    obtain ⟨w, hw, xr', hxr', huw⟩ := h3
    have hxx : xr' = xr := hxr'
    have huw' : u ∈ G.hop w xr := hxx ▸ huw
    obtain ⟨p, hp⟩ := G.hop_nonempty e xr
    have h4 : R p u := hR.compat e w xr xr (hxlP w hw) (hR.equiv.refl xr) p hp u huw'
    exact hR.equiv.trans h1 (hR.equiv.symm (hR.equiv.trans ((hid xr).1 p hp) h4))
  refine ⟨xr, hxrP, ?_⟩
  intro u hu
  obtain ⟨p, hp⟩ := G.hop_nonempty xl x
  exact hR.equiv.trans (hxlP p hp)
    (hR.compat xl xr x x hlr (hR.equiv.refl x) p hp u hu)

/-- ★★★keystone【公理ゼロ版】: 強正則商 H/R は群 — 群の公理をすべて R の意味で満たす。
    ①積の存在 ②R を除いた一意性 ③well-defined ④結合律 ⑤両側単位元 ⑥両側逆元。
    `Quotient` 型を作らないので代表元選択が不要 = `Classical.choice` も排中律も使わない。 -/
theorem srRel_group_axioms {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) :
    (∀ a b : H, ∃ c, IsProdMod G R a b c) ∧
    (∀ a b c c' : H, IsProdMod G R a b c → IsProdMod G R a b c' → R c c') ∧
    (∀ a a' b b' c c' : H, R a a' → R b b' →
        IsProdMod G R a b c → IsProdMod G R a' b' c' → R c c') ∧
    (∀ a b c u p v q : H, IsProdMod G R a b u → IsProdMod G R u c p →
        IsProdMod G R b c v → IsProdMod G R a v q → R p q) ∧
    (∃ e : H, (∀ x : H, IsProdMod G R e x x ∧ IsProdMod G R x e x) ∧
        (∀ x : H, ∃ x', IsProdMod G R x x' e ∧ IsProdMod G R x' x e)) :=
  ⟨srRel_prod_exists hR,
   fun _ _ _ _ h h' => srRel_prod_unique hR h h',
   fun _ _ _ _ _ _ ha hb h h' => srRel_prod_wd hR ha hb h h',
   fun _ _ _ _ _ _ _ hu hp hv hq => srRel_assoc hR hu hp hv hq,
   by
     obtain ⟨e, he⟩ := srRel_exists_id hR
     exact ⟨e, he, fun x => srRel_exists_inv hR e he x⟩⟩

/-- ★★([Afshar–Ameri 2025] Lemma 3.1) 強正則 R と両側単位元 e に対し、**R の類は単位元の類の平行移動**:
    `{y | R x y} = x ∘ {z | R e z}` (原典の ρ(x) = x∘S_ρ)。
    原典の証明を関係版で忠実に追う: (⊆) 再生公理で y ∈ x∘h を取り、逆元 x' を使って R e h を導く。
    (⊇) 単位元の性質と compat で R x y。 -/
theorem srRel_class_eq_hsmul_kernel {H : Type*} {G : Hypergroup H} {R : H → H → Prop}
    (hR : StronglyRegular G R) (e : H)
    (hid : ∀ x : H, IsProdMod G R e x x ∧ IsProdMod G R x e x) (x : H) :
    {y : H | R x y} = hsmul G.hop {x} {z : H | R e z} := by
  ext y
  constructor
  · intro hxy
    obtain ⟨h, hh⟩ := hypergroup_right_solvable_af G x y
    obtain ⟨x', _, hx'xe⟩ := srRel_exists_inv hR e hid x
    obtain ⟨w, hw⟩ := G.hop_nonempty x' y
    have hew : R e w := by
      obtain ⟨p, hp⟩ := G.hop_nonempty x' x
      exact hR.equiv.trans (hx'xe p hp)
        (hR.compat x' x' x y (hR.equiv.refl x') hxy p hp w hw)
    have h1 : w ∈ hsmul G.hop {x'} (G.hop x h) := ⟨x', rfl, y, hh, hw⟩
    have h2 : w ∈ hsmul G.hop (G.hop x' x) {h} := by
      rw [G.hop_assoc x' x h]; exact h1
    obtain ⟨v, hv, h', hh', hwv⟩ := h2
    have hh'h : h' = h := hh'
    have hwv' : w ∈ G.hop v h := hh'h ▸ hwv
    have hev : R e v := hx'xe v hv
    have hwh : R w h := by
      obtain ⟨q, hq⟩ := G.hop_nonempty e h
      exact hR.equiv.trans
        (hR.compat v e h h (hR.equiv.symm hev) (hR.equiv.refl h) w hwv' q hq)
        (hR.equiv.symm ((hid h).1 q hq))
    exact ⟨x, rfl, h, hR.equiv.trans hew hwh, hh⟩
  · rintro ⟨a, ha, s, hs, hy⟩
    have hax : a = x := ha
    have hy' : y ∈ G.hop x s := hax ▸ hy
    obtain ⟨u, hu⟩ := G.hop_nonempty x e
    exact hR.equiv.trans ((hid x).2 u hu)
      (hR.compat x x e s (hR.equiv.refl x) hs u hu y hy')

-- ════════════════════════════════════════════════════════════════════════════
-- ★★★ Gutan 1996 系4.2: 超群では β は推移的 ⟹ β = β* ([Gutan 1996] §2 補題2.3/2.4/定理2.2)
--   ★補題2.3 は原典が □ で証明省略 (routine)。既存 verified 部品 (`nProd_subset_extend`
--     `nProd_hsmul`) で「最右因子 s を c∘a に置き換える」routine 証明を与える。
--   ★これで論文 future work の「β=β* (Freni 1991)」に Gutan 経路で到達。全て choice-free。
-- ════════════════════════════════════════════════════════════════════════════
section GutanCor42
variable {H : Type*} (G : Hypergroup H)

/-- ★hsmul の左単調性 (A⊆B ⟹ A∘C ⊆ B∘C)。既存 `hsmul_mono_right` の対。 -/
theorem hsmul_mono_left {A B C : Set H} (h : A ⊆ B) :
    hsmul G.hop A C ⊆ hsmul G.hop B C := by
  rintro z ⟨a, ha, b, hb, hz⟩
  exact ⟨a, h ha, b, hb, hz⟩

/-- ★単項集合どうしの hsmul はハイパー演算そのもの: {a}∘{b} = a∘b。 -/
theorem hsmul_singleton_singleton (a b : H) : hsmul G.hop {a} {b} = G.hop a b := by
  ext z
  constructor
  · rintro ⟨x, hx, y, hy, hz⟩
    have hxa : x = a := hx
    have hyb : y = b := hy
    rw [hxa, hyb] at hz
    exact hz
  · intro hz
    exact ⟨a, rfl, b, rfl, hz⟩

/-- ★([Gutan 1996] 補題2.3) 超群では、任意のハイパー積 Q と任意の a に対し
    `Q ⊆ Q'∘{a}` となるハイパー積 Q' が存在する。
    ★原典は □ で証明省略 (routine)。証明: 再生公理で s ∈ c∘a なる c を取り、
    Q の最右因子 s を c∘a に置き換える (`nProd_subset_extend`)。 -/
theorem nProd_subset_hsmul_right (s : H) (rest : List H) (a : H) :
    ∃ (c : H) (rest' : List H), nProd G s rest ⊆ hsmul G.hop (nProd G c rest') {a} := by
  obtain ⟨c, hc⟩ := hypergroup_left_solvable_af G a s
  refine ⟨c, rest, ?_⟩
  have h := nProd_hsmul G c rest a []
  rw [nProd_nil] at h
  rw [h]
  exact nProd_subset_extend G hc rest

/-- ★([Gutan 1996] 補題2.4) 超群で Q,Q' がハイパー積で交わりを持つとき、
    任意の a ∈ Q に対し `Q' ∪ {a}` を含むハイパー積 Q'' が存在する。
    源の証明: Q' ⊆ Q₁∘a ⊆ Q₁∘(b∘x) = (Q₁∘b)∘x ⊆ (Q₁∘Q)∘x =: Q''、
    かつ a ∈ b∘x ⊆ (Q₁∘a)∘x ⊆ Q''。 -/
theorem nProd_merge_of_meet {s1 : H} {r1 : List H} {s2 : H} {r2 : List H} {b a : H}
    (hb1 : b ∈ nProd G s1 r1) (hb2 : b ∈ nProd G s2 r2) (ha : a ∈ nProd G s1 r1) :
    ∃ (s3 : H) (r3 : List H),
      nProd G s2 r2 ⊆ nProd G s3 r3 ∧ a ∈ nProd G s3 r3 := by
  obtain ⟨c, r', hQ'⟩ := nProd_subset_hsmul_right G s2 r2 a
  obtain ⟨x, hx⟩ := hypergroup_right_solvable_af G b a
  have hQ1Q : hsmul G.hop (nProd G c r') (nProd G s1 r1) = nProd G s1 (r' ++ c :: r1) :=
    nProd_hsmul G c r' s1 r1
  have hQ'' : hsmul G.hop (nProd G s1 (r' ++ c :: r1)) {x}
      = nProd G x ((r' ++ c :: r1) ++ s1 :: []) := by
    have h := nProd_hsmul G s1 (r' ++ c :: r1) x []
    rw [nProd_nil] at h
    exact h
  refine ⟨x, (r' ++ c :: r1) ++ s1 :: [], ?_, ?_⟩
  · intro z hz
    rw [← hQ'', ← hQ1Q]
    have h1 : z ∈ hsmul G.hop (nProd G c r') {a} := hQ' hz
    have h2 : z ∈ hsmul G.hop (nProd G c r') (hsmul G.hop {b} {x}) := by
      rw [hsmul_singleton_singleton]
      exact hsmul_mono_right G (Set.singleton_subset_iff.mpr hx) h1
    rw [← hsmul_assoc] at h2
    exact hsmul_mono_left G (hsmul_mono_right G (Set.singleton_subset_iff.mpr hb1)) h2
  · rw [← hQ'', ← hQ1Q]
    have hbQ' : b ∈ hsmul G.hop (nProd G c r') {a} := hQ' hb2
    have h1 : a ∈ hsmul G.hop {b} {x} := by
      rw [hsmul_singleton_singleton]; exact hx
    have h2 : a ∈ hsmul G.hop (hsmul G.hop (nProd G c r') {a}) {x} :=
      hsmul_mono_left G (Set.singleton_subset_iff.mpr hbQ') h1
    exact hsmul_mono_left G (hsmul_mono_right G (Set.singleton_subset_iff.mpr ha)) h2

/-- ★([Gutan 1996] 定理2.2 の心臓部) 超群では `𝒞₁({x})` は完全部分。 -/
theorem completeClosure1_isCompletePart_hypergroup (x : H) :
    IsCompletePart G (completeClosure1 G {x}) := by
  rintro s rest ⟨y, hy, hyQ⟩ z hz
  obtain ⟨s', rest', hy', w, hw, hwQ'⟩ := hy
  have hwx : w = x := hw
  have hxQ' : x ∈ nProd G s' rest' := hwx ▸ hwQ'
  obtain ⟨s3, r3, hsub, hxin⟩ := nProd_merge_of_meet G hy' hyQ hxQ'
  exact ⟨s3, r3, hsub hz, x, rfl, hxin⟩

/-- ★★([Gutan 1996] 定理2.2) 超群では完全閉包は1ステップで到達: `𝒞({x}) = 𝒞₁({x})`。 -/
theorem completeClosure_eq_completeClosure1_hypergroup (x : H) :
    completeClosure G {x} = completeClosure1 G {x} :=
  Set.Subset.antisymm
    (completeClosure_minimal G {x} (completeClosure1 G {x})
      (Set.singleton_subset_iff.mpr (subset_completeClosure1 G {x} rfl))
      (completeClosure1_isCompletePart_hypergroup G x))
    (completeClosure1_subset_completeClosure G {x})

/-- ★★★([Gutan 1996] 系4.2) **超群では β は推移的** (定理2.2 + 定理4.1)。 -/
theorem betaRel_transitive_hypergroup :
    ∀ a b c : H, betaRel G a b → betaRel G b c → betaRel G a c :=
  (betaRel_transitive_iff_completeClosure_eq_one G).mpr
    (completeClosure_eq_completeClosure1_hypergroup G)

/-- ★★★**超群では β = β\*** (基本関係が1ステップで確定する)。
    古典的には Freni 1991 の結論に相当するが、本形式化は Gutan 1996 ([Gutan 1996])
    の経路 (定理2.2 + 定理4.1) で到達している。 -/
theorem betaStar_iff_betaRel_hypergroup (a b : H) : betaStar G a b ↔ betaRel G a b :=
  betaStar_iff_betaRel_of_transitive G (betaRel_transitive_hypergroup G) a b

end GutanCor42

section KoskasRegular
variable {H : Type*} (G : Hypergroup H)

/-- Koskas の記法 `A R̄ B`：両側から相手の代表元が取れる（★∃ を含む弱い方）。 -/
def RelBar {H : Type*} (R : H → H → Prop) (A B : Set H) : Prop :=
  (∀ a ∈ A, ∃ b ∈ B, R a b) ∧ (∀ b ∈ B, ∃ a ∈ A, R a b)

/-- Koskas の記法 `A R̿ B`：全対が関係する（★∀ の強い方）。 -/
def RelBarBar {H : Type*} (R : H → H → Prop) (A B : Set H) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, R a b

/-- 原典の右正則性：`x R y` なら任意の `a` で `(x∘a) R̄ (y∘a)`。 -/
def RightRegular (R : H → H → Prop) : Prop :=
  ∀ ⦃x y⦄, R x y → ∀ a, RelBar R (G.hop x a) (G.hop y a)

/-- 原典の左正則性。 -/
def LeftRegular (R : H → H → Prop) : Prop :=
  ∀ ⦃x y⦄, R x y → ∀ a, RelBar R (G.hop a x) (G.hop a y)

/-- 原典の `𝔉_r`：正則同値関係。 -/
structure Regular (R : H → H → Prop) : Prop where
  equiv : Equivalence R
  right : RightRegular G R
  left  : LeftRegular G R

/-- ★`R̿ ⟹ R̄`（集合が非空なとき）。原典の `𝔉'_r ⊆ 𝔉_r` の核。 -/
theorem koskas_relBar_of_relBarBar {R : H → H → Prop} {A B : Set H}
    (hA : A.Nonempty) (hB : B.Nonempty) (h : RelBarBar R A B) : RelBar R A B := by
  obtain ⟨a0, ha0⟩ := hA
  obtain ⟨b0, hb0⟩ := hB
  exact ⟨fun a ha => ⟨b0, hb0, h a ha b0 hb0⟩, fun b hb => ⟨a0, ha0, h a0 ha0 b hb⟩⟩

/-- ★原典 `𝔉'_r ⊆ 𝔉_r`：強正則な同値関係は正則である。 -/
theorem koskas_regular_of_stronglyRegular {R : H → H → Prop}
    (hequiv : Equivalence R)
    (hr : RightStronglyRegular G R) (hl : LeftStronglyRegular G R) :
    Regular G R where
  equiv := hequiv
  right := by
    intro x y hxy a
    exact koskas_relBar_of_relBarBar (G.hop_nonempty x a) (G.hop_nonempty y a)
      (fun u hu v hv => hr hxy a u hu v hv)
  left := by
    intro x y hxy a
    exact koskas_relBar_of_relBarBar (G.hop_nonempty a x) (G.hop_nonempty a y)
      (fun u hu v hv => hl hxy a u hu v hv)

/-- ★原典 命題2(b) 第一主張：`R ∈ 𝔉_r`、`R' ∈ 𝔉'_r` なら交わり `R ∧ R'` は `𝔉_r` に属する。
    原典の証明：`u ∈ x∘a` に対し `R` の正則性が `v ∈ y∘a` と `u R v` を与え、
    `R'` の強正則性が **同じ** `u,v` について `u R' v` を与える。 -/
theorem koskas_prop2b_meet_regular {R R' : H → H → Prop}
    (hR : Regular G R) (hR' : Equivalence R')
    (hR'r : RightStronglyRegular G R') (hR'l : LeftStronglyRegular G R') :
    Regular G (fun x y => R x y ∧ R' x y) where
  equiv :=
    { refl  := fun x => ⟨hR.equiv.refl x, hR'.refl x⟩
      symm  := fun h => ⟨hR.equiv.symm h.1, hR'.symm h.2⟩
      trans := fun h1 h2 => ⟨hR.equiv.trans h1.1 h2.1, hR'.trans h1.2 h2.2⟩ }
  right := by
    rintro x y ⟨hxy, hxy'⟩ a
    obtain ⟨hfwd, hbwd⟩ := hR.right hxy a
    refine ⟨fun u hu => ?_, fun v hv => ?_⟩
    · obtain ⟨v, hv, huv⟩ := hfwd u hu
      exact ⟨v, hv, huv, hR'r hxy' a u hu v hv⟩
    · obtain ⟨u, hu, huv⟩ := hbwd v hv
      exact ⟨u, hu, huv, hR'r hxy' a u hu v hv⟩
  left := by
    rintro x y ⟨hxy, hxy'⟩ a
    obtain ⟨hfwd, hbwd⟩ := hR.left hxy a
    refine ⟨fun u hu => ?_, fun v hv => ?_⟩
    · obtain ⟨v, hv, huv⟩ := hfwd u hu
      exact ⟨v, hv, huv, hR'l hxy' a u hu v hv⟩
    · obtain ⟨u, hu, huv⟩ := hbwd v hv
      exact ⟨u, hu, huv, hR'l hxy' a u hu v hv⟩

/-- ★原典 命題2(b) 第二主張：`R ∈ 𝔉_r`、`R' ∈ 𝔉'_r`、`R' ⊆ R` なら `R ∈ 𝔉'_r`。
    原典の証明：`u ∈ x∘a`、`v ∈ y∘a` に対し `R` の正則性が `w ∈ y∘a` と `u R w` を与える。
    `R'` は強正則で `y R' y`（反射律）だから `w R' v`、`R' ⊆ R` より `w R v`、
    推移律で `u R v`。 -/
theorem koskas_prop2b_stronglyRegular_of_subset {R R' : H → H → Prop}
    (hR : Regular G R) (hR' : Equivalence R')
    (hR'r : RightStronglyRegular G R') (hR'l : LeftStronglyRegular G R')
    (hsub : ∀ ⦃x y⦄, R' x y → R x y) :
    RightStronglyRegular G R ∧ LeftStronglyRegular G R := by
  constructor
  · intro x y hxy a u hu v hv
    obtain ⟨hfwd, _⟩ := hR.right hxy a
    obtain ⟨w, hw, huw⟩ := hfwd u hu
    exact hR.equiv.trans huw (hsub (hR'r (hR'.refl y) a w hw v hv))
  · intro x y hxy a u hu v hv
    obtain ⟨hfwd, _⟩ := hR.left hxy a
    obtain ⟨w, hw, huw⟩ := hfwd u hu
    exact hR.equiv.trans huw (hsub (hR'l (hR'.refl y) a w hw v hv))


/-! ### ★非退化の証人 — `Regular` は `StronglyRegular` より真に弱い

`Regular` を定義しただけでは、それが強正則と同じものかもしれない（同じなら原典 命題2(b) は空回り）。
★全ハイパー群 `totalHypergroup Bool`（`a∘b = univ`）の上で **等号** を取ると、
`R̄` は反射律だけで満たされるので正則だが、`R̿` は `univ` の全対を要求するので
`false = true` を強いて破れる。⇒ 二つの条件は**分離している**。 -/

/-- ★等号は全ハイパー群 `Bool` 上で **正則**（`R̄` は相手を1つ見つければよい）。 -/
theorem koskas_regular_eq_total : Regular (totalHypergroup Bool) (· = ·) where
  equiv := eq_equivalence
  right := by
    intro _ _ _ _
    exact ⟨fun u _ => ⟨u, Set.mem_univ u, rfl⟩, fun v _ => ⟨v, Set.mem_univ v, rfl⟩⟩
  left := by
    intro _ _ _ _
    exact ⟨fun u _ => ⟨u, Set.mem_univ u, rfl⟩, fun v _ => ⟨v, Set.mem_univ v, rfl⟩⟩

/-- ★★同じ等号は **強正則ではない**（`R̿` が `univ` の全対を要求し `false = true` になる）。
    ⇒ `Regular` ⊋ 強正則＝原典が二つの族 `𝔉_r`・`𝔉'_r` を分けたことに実質がある。 -/
theorem koskas_regular_not_stronglyRegular :
    ¬ RightStronglyRegular (totalHypergroup Bool) (· = ·) := by
  intro h
  exact Bool.noConfusion
    (h (rfl : (false : Bool) = false) false false (Set.mem_univ false) true (Set.mem_univ true))

/-- ★下流への再利用（思想3 新規性の伝播）：基本関係 `β*` は強正則なので、原典 `𝔉'_r ⊆ 𝔉_r`
    により **正則**でもある。既存の β* 資産がそのまま Koskas の `𝔉_r` に載る。 -/
theorem koskas_betaStar_regular {H : Type*} (G : Hypergroup H) : Regular G (betaStar G) :=
  koskas_regular_of_stronglyRegular G (betaStar_stronglyRegular G).equiv
    (stronglyRegular_to_oneSided G (betaStar_stronglyRegular G)).1
    (stronglyRegular_to_oneSided G (betaStar_stronglyRegular G)).2

end KoskasRegular

namespace Calibration


universe u
variable {H : Type u} {G : Hypergroup H} {R : H → H → Prop}

/-- The **relational** formulation of "H/R is a group": the group laws stated modulo `R`,
    with no quotient type and no selection of representatives. -/
def GroupModulo (G : Hypergroup H) (R : H → H → Prop) : Prop :=
  (∀ a b : H, ∃ c, IsProdMod G R a b c) ∧
  (∀ a b c c' : H, IsProdMod G R a b c → IsProdMod G R a b c' → R c c') ∧
  (∀ a a' b b' c c' : H, R a a' → R b b' →
      IsProdMod G R a b c → IsProdMod G R a' b' c' → R c c') ∧
  (∀ a b c u p v q : H, IsProdMod G R a b u → IsProdMod G R u c p →
      IsProdMod G R b c v → IsProdMod G R a v q → R p q) ∧
  (∃ e : H, (∀ x : H, IsProdMod G R e x x ∧ IsProdMod G R x e x) ∧
      (∀ x : H, ∃ x', IsProdMod G R x x' e ∧ IsProdMod G R x' x e))

/-- Step 1 (axiom-free): strong regularity implies the relational formulation. -/
theorem groupModulo_of_stronglyRegular (hR : StronglyRegular G R) : GroupModulo G R :=
  srRel_group_axioms hR

section Bridge
variable (hequiv : Equivalence R) (h : GroupModulo G R)

/-- The setoid determined by `R`. -/
def setoidOf : Setoid H := ⟨R, hequiv⟩

local notation "Q" => Quotient (setoidOf hequiv)

/-- Multiplication on the quotient (this is where a representative is selected). -/
noncomputable def qmul : Q → Q → Q :=
  Quotient.lift₂ (fun a b => Quotient.mk (setoidOf hequiv) (h.1 a b).choose)
    (fun a₁ b₁ a₂ b₂ ha hb => Quotient.sound
      (h.2.2.1 a₁ a₂ b₁ b₂ _ _ ha hb (h.1 a₁ b₁).choose_spec (h.1 a₂ b₂).choose_spec))

/-- Workhorse: if `c` represents `a ⊗ b` then `⟦a⟧ ⊗ ⟦b⟧ = ⟦c⟧`. -/
theorem qmul_mk {a b c : H} (hc : IsProdMod G R a b c) :
    qmul hequiv h (Quotient.mk _ a) (Quotient.mk _ b) = Quotient.mk _ c :=
  Quotient.sound (h.2.1 a b _ c (h.1 a b).choose_spec hc)

/-- The unit of the quotient. -/
noncomputable def qone : Q := Quotient.mk (setoidOf hequiv) h.2.2.2.2.choose

theorem qmul_assoc (x y z : Q) :
    qmul hequiv h (qmul hequiv h x y) z = qmul hequiv h x (qmul hequiv h y z) := by
  induction x using Quotient.inductionOn with | _ a =>
  induction y using Quotient.inductionOn with | _ b =>
  induction z using Quotient.inductionOn with | _ c =>
  obtain ⟨u, hu⟩ := h.1 a b
  obtain ⟨p, hp⟩ := h.1 u c
  obtain ⟨v, hv⟩ := h.1 b c
  obtain ⟨q, hq⟩ := h.1 a v
  rw [qmul_mk hequiv h hu, qmul_mk hequiv h hp, qmul_mk hequiv h hv, qmul_mk hequiv h hq]
  exact Quotient.sound (h.2.2.2.1 a b c u p v q hu hp hv hq)

theorem qone_mul (x : Q) : qmul hequiv h (qone hequiv h) x = x := by
  induction x using Quotient.inductionOn with | _ a =>
  exact qmul_mk hequiv h (h.2.2.2.2.choose_spec.1 a).1

theorem qexists_inv (x : Q) : ∃ y : Q, qmul hequiv h y x = qone hequiv h := by
  induction x using Quotient.inductionOn with | _ a =>
  obtain ⟨a', _, h2⟩ := h.2.2.2.2.choose_spec.2 a
  exact ⟨Quotient.mk (setoidOf hequiv) a', qmul_mk hequiv h h2⟩

/-- Inverse: the selection is made directly on the quotient, so no well-definedness obligation arises. -/
noncomputable def qinv (x : Q) : Q := (qexists_inv hequiv h x).choose

theorem qinv_mul (x : Q) : qmul hequiv h (qinv hequiv h x) x = qone hequiv h :=
  (qexists_inv hequiv h x).choose_spec

/-- Step 2 (the bridge): the relational formulation yields a `Group` structure on the quotient
    type. This implication is where `Classical.choice` is consumed. -/
@[reducible] noncomputable def groupOfGroupModulo : Group Q :=
  letI : Mul Q := ⟨qmul hequiv h⟩
  letI : One Q := ⟨qone hequiv h⟩
  letI : Inv Q := ⟨qinv hequiv h⟩
  Group.ofLeftAxioms (qmul_assoc hequiv h) (qone_mul hequiv h) (qinv_mul hequiv h)

end Bridge

/-- Corollary: the strongly regular quotient is a group, obtained via the axiom-free relational
    form followed by the bridge. -/
@[reducible] noncomputable def srQuotientGroup_via_modulo (hR : StronglyRegular G R) :
    Group (Quotient (setoidOf hR.equiv)) :=
  groupOfGroupModulo hR.equiv (groupModulo_of_stronglyRegular hR)

/-! ## The data formulation — isolating what choice actually does -/

/-- The relational formulation with every existential clause replaced by data: a product
    representative, a unit and an inverse are supplied as functions/elements. -/
structure GroupModuloData (G : Hypergroup H) (R : H → H → Prop) where
  prod    : H → H → H
  prod_spec : ∀ a b, IsProdMod G R a b (prod a b)
  unique  : ∀ a b c c' : H, IsProdMod G R a b c → IsProdMod G R a b c' → R c c'
  wd      : ∀ a a' b b' c c' : H, R a a' → R b b' →
              IsProdMod G R a b c → IsProdMod G R a' b' c' → R c c'
  assoc   : ∀ a b c u p v q : H, IsProdMod G R a b u → IsProdMod G R u c p →
              IsProdMod G R b c v → IsProdMod G R a v q → R p q
  one     : H
  one_spec : ∀ x, IsProdMod G R one x x ∧ IsProdMod G R x one x
  inv     : H → H
  inv_spec : ∀ x, IsProdMod G R x (inv x) one ∧ IsProdMod G R (inv x) x one

section BridgeData
variable (hequiv : Equivalence R) (d : GroupModuloData G R)

/-- Quotient multiplication from the data formulation (no choice). -/
def dmul : Quotient (setoidOf hequiv) → Quotient (setoidOf hequiv) → Quotient (setoidOf hequiv) :=
  Quotient.lift₂ (fun a b => Quotient.mk (setoidOf hequiv) (d.prod a b))
    (fun a₁ b₁ a₂ b₂ ha hb => Quotient.sound
      (d.wd a₁ a₂ b₁ b₂ _ _ ha hb (d.prod_spec a₁ b₁) (d.prod_spec a₂ b₂)))

theorem dmul_mk {a b c : H} (hc : IsProdMod G R a b c) :
    dmul hequiv d (Quotient.mk _ a) (Quotient.mk _ b) = Quotient.mk _ c :=
  Quotient.sound (d.unique a b _ c (d.prod_spec a b) hc)

def done : Quotient (setoidOf hequiv) := Quotient.mk (setoidOf hequiv) d.one

def dinv : Quotient (setoidOf hequiv) → Quotient (setoidOf hequiv) :=
  Quotient.lift (fun a => Quotient.mk (setoidOf hequiv) (d.inv a))
    (by
      intro a b hab
      apply Quotient.sound
      show R (d.inv a) (d.inv b)
      have hu : R d.one (d.prod (d.inv a) b) :=
        d.wd (d.inv a) (d.inv a) a b d.one _ (hequiv.refl _) hab
          (d.inv_spec a).2 (d.prod_spec (d.inv a) b)
      have hp : R (d.inv b) (d.prod (d.prod (d.inv a) b) (d.inv b)) :=
        d.wd d.one (d.prod (d.inv a) b) (d.inv b) (d.inv b) (d.inv b) _
          hu (hequiv.refl _) (d.one_spec (d.inv b)).1
          (d.prod_spec (d.prod (d.inv a) b) (d.inv b))
      have hv : R d.one (d.prod b (d.inv b)) :=
        d.unique b (d.inv b) d.one _ (d.inv_spec b).1 (d.prod_spec b (d.inv b))
      have hq : R (d.inv a) (d.prod (d.inv a) (d.prod b (d.inv b))) :=
        d.wd (d.inv a) (d.inv a) d.one (d.prod b (d.inv b)) (d.inv a) _
          (hequiv.refl _) hv (d.one_spec (d.inv a)).2
          (d.prod_spec (d.inv a) (d.prod b (d.inv b)))
      have hpq : R (d.prod (d.prod (d.inv a) b) (d.inv b))
                   (d.prod (d.inv a) (d.prod b (d.inv b))) :=
        d.assoc (d.inv a) b (d.inv b) (d.prod (d.inv a) b)
          (d.prod (d.prod (d.inv a) b) (d.inv b)) (d.prod b (d.inv b))
          (d.prod (d.inv a) (d.prod b (d.inv b)))
          (d.prod_spec _ _) (d.prod_spec _ _) (d.prod_spec _ _) (d.prod_spec _ _)
      exact hequiv.symm (hequiv.trans (hequiv.trans hp hpq) (hequiv.symm hq)))

theorem dmul_assoc (x y z : Quotient (setoidOf hequiv)) :
    dmul hequiv d (dmul hequiv d x y) z = dmul hequiv d x (dmul hequiv d y z) := by
  induction x using Quotient.inductionOn with | _ a =>
  induction y using Quotient.inductionOn with | _ b =>
  induction z using Quotient.inductionOn with | _ c =>
  rw [dmul_mk hequiv d (d.prod_spec a b), dmul_mk hequiv d (d.prod_spec (d.prod a b) c),
      dmul_mk hequiv d (d.prod_spec b c), dmul_mk hequiv d (d.prod_spec a (d.prod b c))]
  exact Quotient.sound
    (d.assoc a b c (d.prod a b) (d.prod (d.prod a b) c) (d.prod b c) (d.prod a (d.prod b c))
      (d.prod_spec _ _) (d.prod_spec _ _) (d.prod_spec _ _) (d.prod_spec _ _))

theorem done_mul (x : Quotient (setoidOf hequiv)) : dmul hequiv d (done hequiv d) x = x := by
  induction x using Quotient.inductionOn with | _ a =>
  exact dmul_mk hequiv d (d.one_spec a).1

theorem dinv_mul (x : Quotient (setoidOf hequiv)) :
    dmul hequiv d (dinv hequiv d x) x = done hequiv d := by
  induction x using Quotient.inductionOn with | _ a =>
  exact dmul_mk hequiv d (d.inv_spec a).2

/-- Step 2' (the bridge from data): with the existentials replaced by data, the same `Group`
    structure on the quotient is obtained **without** `Classical.choice`. -/
@[reducible] def groupOfGroupModuloData : Group (Quotient (setoidOf hequiv)) :=
  letI : Mul (Quotient (setoidOf hequiv)) := ⟨dmul hequiv d⟩
  letI : One (Quotient (setoidOf hequiv)) := ⟨done hequiv d⟩
  letI : Inv (Quotient (setoidOf hequiv)) := ⟨dinv hequiv d⟩
  Group.ofLeftAxioms (dmul_assoc hequiv d) (done_mul hequiv d) (dinv_mul hequiv d)

end BridgeData

/-- Closing the triangle: `Classical.choice` is used only to turn the relational formulation
    into the data formulation, i.e. to extract product representatives, a unit and inverses. -/
noncomputable def dataOfGroupModulo (h : GroupModulo G R) : GroupModuloData G R where
  prod := fun a b => (h.1 a b).choose
  prod_spec := fun a b => (h.1 a b).choose_spec
  unique := h.2.1
  wd := h.2.2.1
  assoc := h.2.2.2.1
  one := h.2.2.2.2.choose
  one_spec := h.2.2.2.2.choose_spec.1
  inv := fun x => (h.2.2.2.2.choose_spec.2 x).choose
  inv_spec := fun x => (h.2.2.2.2.choose_spec.2 x).choose_spec

/-! ## The local axiom of descriptions

The relations from which `dataOfGroupModulo` extracts data are total and functional **up to `R`**.
That pattern is the *axiom of descriptions* (unique choice) for setoids. Factoring the bridge
through it separates the logical principle from Lean's classical implementation of it. -/

/-- A local axiom-of-descriptions interface for the setoid `(H, R)`: it selects from relations that
    are total and whose outputs are unique up to `R`. -/
structure RDescription (R : H → H → Prop) where
  pick : (A : Type u) → (P : A → H → Prop) →
    (∀ a, ∃ b, P a b) → (∀ a b b', P a b → P a b' → R b b') → A → H
  pick_spec : ∀ (A : Type u) (P : A → H → Prop)
    (htotal : ∀ a, ∃ b, P a b) (hfun : ∀ a b b', P a b → P a b' → R b b') (a : A),
    P a (pick A P htotal hfun a)

/-- Lean's classical implementation of the local description interface. -/
noncomputable def classicalRDescription (R : H → H → Prop) : RDescription (H := H) R where
  pick := fun _ _ htotal _ a => (htotal a).choose
  pick_spec := fun _ _ htotal _ a => (htotal a).choose_spec

/-- `e` is a two-sided unit modulo `R`. -/
def UnitMod (G : Hypergroup H) (R : H → H → Prop) (e : H) : Prop :=
  ∀ x, IsProdMod G R e x x ∧ IsProdMod G R x e x

/-- `y` is a two-sided inverse of `x` relative to the unit `e`, modulo `R`. -/
def InvMod (G : Hypergroup H) (R : H → H → Prop) (e x y : H) : Prop :=
  IsProdMod G R x y e ∧ IsProdMod G R y x e

/-- Units are unique up to `R`. -/
theorem unitMod_unique (hequiv : Equivalence R) (h : GroupModulo G R)
    {e e' : H} (he : UnitMod G R e) (he' : UnitMod G R e') : R e e' :=
  hequiv.symm (h.2.1 e e' e' e (he e').1 (he' e).2)

/-- Inverses are unique up to `R`. -/
theorem invMod_unique (hequiv : Equivalence R) (h : GroupModulo G R)
    {e x y z : H} (he : UnitMod G R e)
    (hy : InvMod G R e x y) (hz : InvMod G R e x z) : R y z :=
  hequiv.symm (h.2.2.2.1 y x z e z e y hy.2 (he z).1 hz.1 (he y).2)

/-- ★The three selection families that this particular bridge actually consumes: a product
    representative, a unit, and an inverse for each element. -/
structure GroupModuloSelections (G : Hypergroup H) (R : H → H → Prop) where
  prod      : H → H → H
  prod_spec : ∀ a b, IsProdMod G R a b (prod a b)
  one       : H
  one_spec  : UnitMod G R one
  inv       : H → H
  inv_spec  : ∀ x, InvMod G R one x (inv x)

/-- ★Given the relational laws, the three selections are exactly what is missing from the data
    formulation: everything else is transported unchanged. Axiom-free. -/
def dataOfSelections (h : GroupModulo G R) (s : GroupModuloSelections G R) :
    GroupModuloData G R where
  prod := s.prod
  prod_spec := s.prod_spec
  unique := h.2.1
  wd := h.2.2.1
  assoc := h.2.2.2.1
  one := s.one
  one_spec := s.one_spec
  inv := s.inv
  inv_spec := s.inv_spec

/-- ★A description operator supplies the three selection families. Axiom-free. -/
def selectionsOfDescription
    (hequiv : Equivalence R) (desc : RDescription (H := H) R) (h : GroupModulo G R) :
    GroupModuloSelections G R := by
  -- products
  have Ptot : ∀ ab : H × H, ∃ c, IsProdMod G R ab.1 ab.2 c := fun ab => h.1 ab.1 ab.2
  have Pfun : ∀ (ab : H × H) c c', IsProdMod G R ab.1 ab.2 c → IsProdMod G R ab.1 ab.2 c' → R c c' :=
    fun ab c c' hc hc' => h.2.1 ab.1 ab.2 c c' hc hc'
  -- unit
  have Utot : ∀ _ : PUnit.{u+1}, ∃ e, UnitMod G R e := by
    intro _; obtain ⟨e, he, _⟩ := h.2.2.2.2; exact ⟨e, he⟩
  have Ufun : ∀ (_ : PUnit.{u+1}) e e', UnitMod G R e → UnitMod G R e' → R e e' :=
    fun _ e e' he he' => unitMod_unique hequiv h he he'
  set one : H := desc.pick PUnit.{u+1} (fun _ e => UnitMod G R e) Utot Ufun PUnit.unit with hone
  have one_spec : UnitMod G R one :=
    desc.pick_spec PUnit.{u+1} (fun _ e => UnitMod G R e) Utot Ufun PUnit.unit
  -- inverses
  have Itot : ∀ x : H, ∃ y, InvMod G R one x y := by
    intro x
    obtain ⟨e₀, he₀, hinv₀⟩ := h.2.2.2.2
    obtain ⟨y, hy⟩ := hinv₀ x
    have hoe : R one e₀ := unitMod_unique hequiv h one_spec he₀
    exact ⟨y, fun u hu => hequiv.trans hoe (hy.1 u hu), fun u hu => hequiv.trans hoe (hy.2 u hu)⟩
  have Ifun : ∀ (x : H) y z, InvMod G R one x y → InvMod G R one x z → R y z :=
    fun x y z hy hz => invMod_unique hequiv h one_spec hy hz
  exact
    { prod := fun a b => desc.pick (H × H) (fun ab c => IsProdMod G R ab.1 ab.2 c) Ptot Pfun (a, b)
      prod_spec := fun a b =>
        desc.pick_spec (H × H) (fun ab c => IsProdMod G R ab.1 ab.2 c) Ptot Pfun (a, b)
      one := one
      one_spec := one_spec
      inv := fun x => desc.pick H (fun x y => InvMod G R one x y) Itot Ifun x
      inv_spec := fun x => desc.pick_spec H (fun x y => InvMod G R one x y) Itot Ifun x }

/-- ★The relational-to-data bridge needs only the local description interface: given such an
    operator, the passage (R) ⟹ (D) is proved with an **empty** axiom footprint. It factors through
    the three selection families of `GroupModuloSelections`. -/
def dataOfGroupModuloWithDescription
    (hequiv : Equivalence R) (desc : RDescription (H := H) R) (h : GroupModulo G R) :
    GroupModuloData G R :=
  dataOfSelections h (selectionsOfDescription hequiv desc h)

/-- Composing the two recovers the classical bridge; only the operator is classical. -/
noncomputable def dataOfGroupModulo_via_description
    (hequiv : Equivalence R) (h : GroupModulo G R) : GroupModuloData G R :=
  dataOfGroupModuloWithDescription hequiv (classicalRDescription R) h

/-! ## Witnessed hypergroups — the existential axioms replaced by witnesses -/

/-- A hypergroup whose existential axioms are supplied with witness functions. This is a
    strengthening of Marty's definition: a selection rule is part of the structure. -/
structure HypergroupW (H : Type u) extends Hypergroup H where
  pt      : H
  wit     : H → H → H
  wit_mem : ∀ a b, wit a b ∈ hop a b
  rsolve  : H → H → H
  rsolve_spec : ∀ a b, b ∈ hop a (rsolve a b)

section Witness
variable (W : HypergroupW H) {R : H → H → Prop}

private theorem w_rid (hR : StronglyRegular W.toHypergroup R) (x : H) :
    IsProdMod W.toHypergroup R x (W.rsolve W.pt W.pt) x := by
  intro u hu
  obtain ⟨y, hy⟩ := hypergroup_left_solvable_af W.toHypergroup W.pt x
  have h1 : u ∈ hsmul W.hop (W.hop y W.pt) {W.rsolve W.pt W.pt} := ⟨x, hy, _, rfl, hu⟩
  have h2 : u ∈ hsmul W.hop {y} (W.hop W.pt (W.rsolve W.pt W.pt)) := by
    rw [← W.hop_assoc y W.pt (W.rsolve W.pt W.pt)]; exact h1
  obtain ⟨y', hy', w, hw, huw⟩ := h2
  have hyy : y' = y := hy'
  have huw' : u ∈ W.hop y w := hyy ▸ huw
  exact hR.compat y y W.pt w (hR.equiv.refl y)
    (srProduct_single_class W.toHypergroup hR W.pt (W.rsolve W.pt W.pt) W.pt
      (W.rsolve_spec W.pt W.pt) w hw) x hy u huw'

private theorem w_lid (hR : StronglyRegular W.toHypergroup R) (x : H) :
    IsProdMod W.toHypergroup R (W.rsolve W.pt W.pt) x x := by
  obtain ⟨e', he'⟩ := hypergroup_left_solvable_af W.toHypergroup W.pt W.pt
  have hlid : ∀ z : H, IsProdMod W.toHypergroup R e' z z := by
    intro z v hv
    obtain ⟨y, hy⟩ := hypergroup_right_solvable_af W.toHypergroup W.pt z
    have h1 : v ∈ hsmul W.hop {e'} (W.hop W.pt y) := ⟨e', rfl, z, hy, hv⟩
    have h2 : v ∈ hsmul W.hop (W.hop e' W.pt) {y} := by rw [W.hop_assoc e' W.pt y]; exact h1
    obtain ⟨w, hw, y', hy', hvw⟩ := h2
    have hyy : y' = y := hy'
    have hvw' : v ∈ W.hop w y := hyy ▸ hvw
    exact hR.compat W.pt w y y
      (srProduct_single_class W.toHypergroup hR e' W.pt W.pt he' w hw)
      (hR.equiv.refl y) z hy v hvw'
  have hee : R e' (W.rsolve W.pt W.pt) := by
    obtain ⟨v, hv⟩ := W.hop_nonempty e' (W.rsolve W.pt W.pt)
    exact hR.equiv.trans (w_rid W hR e' v hv)
      (hR.equiv.symm (hlid (W.rsolve W.pt W.pt) v hv))
  intro u hu
  obtain ⟨p, hp⟩ := W.hop_nonempty e' x
  exact hR.equiv.trans (hlid x p hp)
    (hR.compat e' (W.rsolve W.pt W.pt) x x hee (hR.equiv.refl x) p hp u hu)

/-- With witnessed axioms, the data formulation holds with an empty footprint. -/
def groupModuloDataOfWitness (hR : StronglyRegular W.toHypergroup R) :
    GroupModuloData W.toHypergroup R where
  prod := W.wit
  prod_spec := fun a b u hu =>
    srProduct_single_class W.toHypergroup hR a b (W.wit a b) (W.wit_mem a b) u hu
  unique := fun a b _ _ h h' => srRel_prod_unique hR h h'
  wd := fun a a' b b' _ _ ha hb h h' => srRel_prod_wd hR ha hb h h'
  assoc := fun a b c u p v q hu hp hv hq => srRel_assoc hR hu hp hv hq
  one := W.rsolve W.pt W.pt
  one_spec := fun x => ⟨w_lid W hR x, w_rid W hR x⟩
  inv := fun x => W.rsolve x (W.rsolve W.pt W.pt)
  inv_spec := fun x => by
    refine ⟨fun u hu => srProduct_single_class W.toHypergroup hR x _ _
      (W.rsolve_spec x (W.rsolve W.pt W.pt)) u hu, ?_⟩
    obtain ⟨xl, hxl⟩ := hypergroup_left_solvable_af W.toHypergroup x (W.rsolve W.pt W.pt)
    have hxrP : IsProdMod W.toHypergroup R x (W.rsolve x (W.rsolve W.pt W.pt))
        (W.rsolve W.pt W.pt) := fun u hu =>
      srProduct_single_class W.toHypergroup hR x _ _ (W.rsolve_spec x _) u hu
    have hxlP : IsProdMod W.toHypergroup R xl x (W.rsolve W.pt W.pt) := fun u hu =>
      srProduct_single_class W.toHypergroup hR xl x _ hxl u hu
    have hlr : R xl (W.rsolve x (W.rsolve W.pt W.pt)) := by
      obtain ⟨u, hu⟩ := W.hop_nonempty xl (W.rsolve W.pt W.pt)
      have h1 : R xl u := w_rid W hR xl u hu
      have h2 : u ∈ hsmul W.hop {xl} (W.hop x (W.rsolve x (W.rsolve W.pt W.pt))) :=
        ⟨xl, rfl, W.rsolve W.pt W.pt, W.rsolve_spec x _, hu⟩
      have h3 : u ∈ hsmul W.hop (W.hop xl x) {W.rsolve x (W.rsolve W.pt W.pt)} := by
        rw [W.hop_assoc xl x (W.rsolve x (W.rsolve W.pt W.pt))]; exact h2
      obtain ⟨w, hw, xr', hxr', huw⟩ := h3
      have hxx : xr' = W.rsolve x (W.rsolve W.pt W.pt) := hxr'
      have huw' : u ∈ W.hop w (W.rsolve x (W.rsolve W.pt W.pt)) := hxx ▸ huw
      obtain ⟨p, hp⟩ := W.hop_nonempty (W.rsolve W.pt W.pt) (W.rsolve x (W.rsolve W.pt W.pt))
      have h4 : R p u := hR.compat (W.rsolve W.pt W.pt) w _ _ (hxlP w hw)
        (hR.equiv.refl _) p hp u huw'
      exact hR.equiv.trans h1
        (hR.equiv.symm (hR.equiv.trans (w_lid W hR (W.rsolve x (W.rsolve W.pt W.pt)) p hp) h4))
    intro u hu
    obtain ⟨p, hp⟩ := W.hop_nonempty xl x
    exact hR.equiv.trans (hxlP p hp)
      (hR.compat xl (W.rsolve x (W.rsolve W.pt W.pt)) x x hlr (hR.equiv.refl x) p hp u hu)

/-- Corollary: for a witnessed hypergroup the strongly regular quotient is a Lean `Group`
    without `Classical.choice` (footprint `{propext, Quot.sound}`). -/
@[reducible] def quotientGroupOfWitness (hR : StronglyRegular W.toHypergroup R) :
    Group (Quotient (setoidOf hR.equiv)) :=
  groupOfGroupModuloData hR.equiv (groupModuloDataOfWitness W hR)

end Witness

/-! ## Non-degeneracy witnesses -/

/-- Witness 1 (genuinely multivalued, built without choice): the total hypergroup `a ∘ b = H`
    with witnesses. Set equality forces `propext`; nothing forces choice. -/
def totalW (H : Type u) (a₀ : H) : HypergroupW H where
  toHypergroup :=
    { hop := fun _ _ => Set.univ
      carrier_nonempty := ⟨a₀⟩
      hop_nonempty := fun _ _ => ⟨a₀, trivial⟩
      hop_assoc := fun a b c => Set.ext fun _ =>
        ⟨fun _ => ⟨a, rfl, a₀, trivial, trivial⟩, fun _ => ⟨a₀, trivial, c, rfl, trivial⟩⟩
      repro_right := fun _ => Set.ext fun _ =>
        ⟨fun _ => trivial, fun _ => Set.mem_iUnion.mpr ⟨a₀, trivial⟩⟩
      repro_left := fun _ => Set.ext fun _ =>
        ⟨fun _ => trivial, fun _ => Set.mem_iUnion.mpr ⟨a₀, trivial⟩⟩ }
  pt := a₀
  wit := fun _ b => b
  wit_mem := fun _ _ => trivial
  rsolve := fun _ b => b
  rsolve_spec := fun _ _ => trivial

/-- Witness 1 is genuinely multivalued. -/
theorem totalW_multivalued :
    ∃ u v : Bool, u ∈ (totalW Bool true).hop true true ∧
      v ∈ (totalW Bool true).hop true true ∧ u ≠ v :=
  ⟨false, true, trivial, trivial, Bool.noConfusion⟩

/-! ### A genuinely multivalued witness with a non-trivial quotient -/

/-- A genuinely multivalued hypergroup: `Gr × Bool` with `(g,x) ∘ (h,y) = {z | z.1 = g*h}`.
    The second coordinate is unconstrained, so every hyperproduct has two elements; the relation
    "equal first coordinates" is strongly regular. -/
def prodW (Gr : Type u) [Group Gr] : HypergroupW (Gr × Bool) where
  toHypergroup :=
    { hop := fun a b => {z | z.1 = a.1 * b.1}
      carrier_nonempty := ⟨(1, false)⟩
      hop_nonempty := fun a b => ⟨(a.1 * b.1, false), rfl⟩
      hop_assoc := fun a b c => Set.ext fun z =>
        ⟨fun ⟨w, hw, y, hy, hz⟩ => ⟨a, rfl, (b.1 * c.1, false), rfl, by
            simp only [Set.mem_setOf_eq] at *
            rw [hz, hw, hy, mul_assoc]⟩,
         fun ⟨w, hw, y, hy, hz⟩ => ⟨(a.1 * b.1, false), rfl, c, rfl, by
            simp only [Set.mem_setOf_eq] at *
            rw [hz, hw, hy, mul_assoc]⟩⟩
      repro_right := fun a => Set.ext fun z =>
        ⟨fun _ => trivial, fun _ => Set.mem_iUnion.mpr ⟨(a.1⁻¹ * z.1, false), by
            show z.1 = a.1 * (a.1⁻¹ * z.1); rw [← mul_assoc, mul_inv_cancel, one_mul]⟩⟩
      repro_left := fun a => Set.ext fun z =>
        ⟨fun _ => trivial, fun _ => Set.mem_iUnion.mpr ⟨(z.1 * a.1⁻¹, false), by
            show z.1 = z.1 * a.1⁻¹ * a.1; rw [mul_assoc, inv_mul_cancel, mul_one]⟩⟩ }
  pt := (1, false)
  wit := fun a b => (a.1 * b.1, false)
  wit_mem := fun _ _ => rfl
  rsolve := fun a b => (a.1⁻¹ * b.1, false)
  rsolve_spec := fun a b => by
    show b.1 = a.1 * (a.1⁻¹ * b.1); rw [← mul_assoc, mul_inv_cancel, one_mul]

/-- `prodW` is genuinely multivalued. -/
theorem prodW_multivalued (Gr : Type u) [Group Gr] :
    ∃ u v : Gr × Bool, u ∈ (prodW Gr).hop (1, false) (1, false) ∧
      v ∈ (prodW Gr).hop (1, false) (1, false) ∧ u ≠ v :=
  ⟨(1, false), (1, true), by show (1:Gr) = 1 * 1; rw [mul_one],
    by show (1:Gr) = 1 * 1; rw [mul_one], by simp⟩

/-- Equality of first coordinates is a strongly regular equivalence on `prodW`. -/
theorem prodW_fstRel_stronglyRegular (Gr : Type u) [Group Gr] :
    StronglyRegular (prodW Gr).toHypergroup (fun a b : Gr × Bool => a.1 = b.1) where
  equiv := ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩
  compat := fun a a' b b' ha hb u hu v hv => by
    show u.1 = v.1
    have hu' : u.1 = a.1 * b.1 := hu
    have hv' : v.1 = a'.1 * b'.1 := hv
    rw [hu', hv', ha, hb]

/-- Distinct elements of `Gr` are not related, hence the quotient is non-trivial when `Gr` is. -/
theorem prodW_quotient_nontrivial (Gr : Type u) [Group Gr] {g : Gr} (hg : g ≠ 1) :
    ¬ (fun a b : Gr × Bool => a.1 = b.1) (g, false) (1, false) := hg


/-! ### The quotient of `prodW` is (isomorphic to) `Gr` -/

/-- Distinct elements of `Gr` give distinct classes in the quotient **type**. -/
theorem prodW_quotient_classes_distinct (Gr : Type u) [Group Gr] {g : Gr} (hg : g ≠ 1) :
    Quotient.mk (setoidOf (prodW_fstRel_stronglyRegular Gr).equiv) ((g, false) : Gr × Bool) ≠
      Quotient.mk (setoidOf (prodW_fstRel_stronglyRegular Gr).equiv) ((1, false) : Gr × Bool) := by
  intro h
  exact hg (Quotient.exact h)

/-- The quotient of `prodW` by "equal first coordinates" is in bijection with `Gr`. -/
def prodW_quotientEquiv (Gr : Type u) [Group Gr] :
    Quotient (setoidOf (prodW_fstRel_stronglyRegular Gr).equiv) ≃ Gr where
  toFun := Quotient.lift (fun a : Gr × Bool => a.1) (fun _ _ h => h)
  invFun := fun g => Quotient.mk _ (g, false)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with | _ a =>
    exact Quotient.sound rfl
  right_inv := fun _ => rfl

/-- The bijection intertwines the quotient multiplication (the one carried by the choice-free
    group structure of Theorem `quotientGroupOfWitness`) with the multiplication of `Gr`.
    Together with `prodW_quotientEquiv` this identifies the quotient with `Gr`. -/
theorem prodW_quotientEquiv_mul (Gr : Type u) [Group Gr]
    (x y : Quotient (setoidOf (prodW_fstRel_stronglyRegular Gr).equiv)) :
    prodW_quotientEquiv Gr
        (dmul (prodW_fstRel_stronglyRegular Gr).equiv
          (groupModuloDataOfWitness (prodW Gr) (prodW_fstRel_stronglyRegular Gr)) x y)
      = prodW_quotientEquiv Gr x * prodW_quotientEquiv Gr y := by
  induction x using Quotient.inductionOn with | _ a =>
  induction y using Quotient.inductionOn with | _ b =>
  rw [dmul_mk (prodW_fstRel_stronglyRegular Gr).equiv
        (groupModuloDataOfWitness (prodW Gr) (prodW_fstRel_stronglyRegular Gr))
        ((groupModuloDataOfWitness (prodW Gr) (prodW_fstRel_stronglyRegular Gr)).prod_spec a b)]
  rfl

end Calibration

/-! ## Axiom audit — every public declaration of this section, plus the surveyed results -/

section Audit
#print axioms Hypergroups.Calibration.GroupModulo
#print axioms Hypergroups.Calibration.groupModulo_of_stronglyRegular
#print axioms Hypergroups.Calibration.setoidOf
#print axioms Hypergroups.Calibration.qmul
#print axioms Hypergroups.Calibration.qmul_mk
#print axioms Hypergroups.Calibration.qone
#print axioms Hypergroups.Calibration.qmul_assoc
#print axioms Hypergroups.Calibration.qone_mul
#print axioms Hypergroups.Calibration.qexists_inv
#print axioms Hypergroups.Calibration.qinv
#print axioms Hypergroups.Calibration.qinv_mul
#print axioms Hypergroups.Calibration.groupOfGroupModulo
#print axioms Hypergroups.Calibration.srQuotientGroup_via_modulo
#print axioms Hypergroups.Calibration.GroupModuloData
#print axioms Hypergroups.Calibration.dmul
#print axioms Hypergroups.Calibration.dmul_mk
#print axioms Hypergroups.Calibration.done
#print axioms Hypergroups.Calibration.dinv
#print axioms Hypergroups.Calibration.dmul_assoc
#print axioms Hypergroups.Calibration.done_mul
#print axioms Hypergroups.Calibration.dinv_mul
#print axioms Hypergroups.Calibration.groupOfGroupModuloData
#print axioms Hypergroups.Calibration.dataOfGroupModulo
#print axioms Hypergroups.Calibration.RDescription
#print axioms Hypergroups.Calibration.UnitMod
#print axioms Hypergroups.Calibration.InvMod
#print axioms Hypergroups.Calibration.classicalRDescription
#print axioms Hypergroups.Calibration.unitMod_unique
#print axioms Hypergroups.Calibration.invMod_unique
#print axioms Hypergroups.Calibration.GroupModuloSelections
#print axioms Hypergroups.Calibration.dataOfSelections
#print axioms Hypergroups.Calibration.selectionsOfDescription
#print axioms Hypergroups.Calibration.dataOfGroupModuloWithDescription
#print axioms Hypergroups.Calibration.dataOfGroupModulo_via_description
#print axioms Hypergroups.Calibration.HypergroupW
#print axioms Hypergroups.Calibration.groupModuloDataOfWitness
#print axioms Hypergroups.Calibration.quotientGroupOfWitness
#print axioms Hypergroups.Calibration.totalW
#print axioms Hypergroups.Calibration.totalW_multivalued
#print axioms Hypergroups.Calibration.prodW
#print axioms Hypergroups.Calibration.prodW_multivalued
#print axioms Hypergroups.Calibration.prodW_fstRel_stronglyRegular
#print axioms Hypergroups.Calibration.prodW_quotient_nontrivial
#print axioms Hypergroups.Calibration.prodW_quotient_classes_distinct
#print axioms Hypergroups.Calibration.prodW_quotientEquiv
#print axioms Hypergroups.Calibration.prodW_quotientEquiv_mul

-- surveyed results reported in the paper's Section 5
#print axioms Hypergroups.stronglyRegular_to_oneSided
#print axioms Hypergroups.stronglyRegular_of_oneSided
#print axioms Hypergroups.koskas_relBar_of_relBarBar
#print axioms Hypergroups.koskas_regular_of_stronglyRegular
#print axioms Hypergroups.koskas_prop2b_meet_regular
#print axioms Hypergroups.koskas_prop2b_stronglyRegular_of_subset
#print axioms Hypergroups.koskas_regular_eq_total
#print axioms Hypergroups.koskas_regular_not_stronglyRegular
#print axioms Hypergroups.betaStar_subset_of_stronglyRegular
#print axioms Hypergroups.betaStar_stronglyRegular
#print axioms Hypergroups.betaRel_transitive_hypergroup
#print axioms Hypergroups.betaRel_transitive_iff_completeClosure_eq_one
#print axioms Hypergroups.srMul_assoc
#print axioms Hypergroups.srMul_exists_id
#print axioms Hypergroups.srMul_exists_inv
#print axioms Hypergroups.srQuotientGroup
-- Ambient comparison used explicitly in the paper.
#print axioms Classical.em
end Audit

end Hypergroups
