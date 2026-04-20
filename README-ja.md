# Lean Lexicon

[English](README.md)

AT Protocol の Lexicon を Lean 4 / Mathlib で形式化するプロジェクト。

**zero sorry, zero axiom, zero opaque.** Lean v4.29.0, Mathlib v4.29.0。

## 概要

Lexicon を**型の宇宙**として捉え直す。各 endpoint は型の間の射であり、API を使うことは射を合成して目的地に到達すること。

```
createSession: {identifier, password} → {accessJwt, did, ...}
getProfile:    {accessJwt, actor}     → {profileViewDetailed}
```

2 つを繋ぐと `{identifier, password} → createSession → getProfile → {profileViewDetailed}` という経路が得られる。この経路が操作手順の**証人 (witness)**。

## Lean の役割

経路を見つけるのは [Laplan](https://github.com/barineco/laplan) の solver。Lean は solver が返す結果に**意味論的な保証**を与える proof layer を提供する。対象は経路の正しさ、制約の効果、不足情報の分類。

## 形式化されている結論

### 経路と到達可能性

- 経路は到達可能性の構成的証明: BFS 探索が返す endpoint 名の列は、marking から goal への到達 witness を構成する (Witness)
- 探索の健全性: `search` と `searchAll` が返す recipe は、Petri net 到達関係に対する構成的証明である (Witness)
- 制約で到達性が変わる: 注釈 (型包含、所有権) を加えると経路集合が厳密に細分化される (ConstraintProfiles)
- 注釈は型から復元不能: code shape が同じ endpoint は、注釈を欠いた状態では区別できず、pruning-only の boundary で過剰近似が発生する (NonRecoverability)

### 前提条件と needs の分類

- 前提条件は input フィールドではない: JWT や capability のような暗黙前提は、input の型だけからは導出できない (RequirementSatisfaction)
- 画面要求データの分類は 4 種類: `alreadySatisfied` / `witnessAvailable` / `recoverableByRecipe` / `needsUserAction`。境界で枝刈りされた要求は `needsUserAction` に回収される (Needs)

前提条件の充足源は 5 分類:

| 充足源 | 例 |
|---|---|
| ユーザーが直接与える | パスワード |
| 既に marking にある | 前の操作で得た値 |
| 他 endpoint の output | createSession が返す認証トークン |
| 所有権から導出 | did から自分のリポジトリ |
| 型包含から導出 | did → at-identifier |

### 宇宙分離と圏構造

- Lexicon₀ (型) と Lexicon₁ (射) の宇宙分離: 型の encoding は非正準であり、提示方法が一意に定まらない (Universe)
- 射の圏構造: 結合律と左右の単位律が成立する (Transition)
- 分岐は型構造の帰結: `if` は union 型の dispatch と射の合成に還元され、新しい primitive ではない (Transition)

### 単調性と階層の崩壊

- guard と fire の単調性: marking の包含に対して WSTS の単調性を満たす (Monotonicity)
- consumes 付き fire の単調性: `(m \ C) ∪ P` も同様に単調 (Monotonicity)
- inhibitor arc の不在: 正のメンバーシップ判定のみで構成され、token 追加で遷移が無効化される状況は発生しない (Monotonicity)
- Lex1 より上は崩壊する: 合成・分岐・列挙はすべて Lex1 に留まる。Lex2 (functor) と Lex1 (morph) の違いは観測粒度であって計算量的性質ではない (Collapse)

### 停止性

- consumes 付き経路の帰納的定義: `RichReachesBy` で排他消費の経路を記述 (Termination)
- 宇宙閉包: fire は有限 fact universe の内側に留まる (Termination)
- visited set による停止: 探索空間は `2^|U|` で有界、各 step で gap が厳密に減少する (Termination)
- サイクル復帰: consumes サイクルは initial marking に戻る (visited set 検出の前提、Termination)

### Bridge 機構

2 つの endpoint (`self_profile_from_login`, `feed_options`) について、Rust solver が返す recipe と Lean 側 `search` / `searchAll` の結果を厳密に突き合わせる機構を提供する (Bridge)。判定は existential / universal 命題として書き下し、compatibility を shape / semantically / fully の 3 段階で分類する。registry には現在この 2 goal と 5 choice が登録されている。

## 4 つの見方

**Tarski 宇宙**: Lexicon のスキーマを型の名前 (code)、endpoint の動作を型の中身 (解釈) と見る。型の名前だけでは解釈が一意に定まらない。注釈が解釈を確定させる。

**Petri net**: endpoint を遷移、型を place、値を token と見る。endpoint を呼ぶと token が移動する。目標の token 配置に到達できるかが到達可能性問題。

**tactic モード**: Lean の証明と同じ構造で API 利用を読む。目標 (欲しいデータ) に対して endpoint を適用し、仮説 (手持ちのデータ) を変形して目標を達成する。到達不能は「この前提では証明できない」に対応する。

**圏論**: endpoint を射、型を対象とする圏を構成する。合成の結合律、恒等射、単位律は証明済み。codegen はこの圏からターゲット言語の圏への関手であり、条件分岐は union 型の dispatch と射の合成から導出される。

## モジュール構成

| ファイル | 役割 |
|---|---|
| `Basic` | Lexicon の型の基本定義 (TypeExpr: atom, array, object, union) |
| `Annotation` | 前提条件 / 状態操作の最小注釈 |
| `AnnotationTable` | endpoint ごとの注釈テーブル |
| `Refinement` | 型構造から機械導出できる部分 |
| `Canonical` | 型構造導出と注釈の合成 |
| `Interpretation` | 型と注釈から手持ちデータ集合への意味を与える |
| `Reachability` | goal に到達できるかの判定 |
| `Search` | 有界探索 |
| `Witness` | 探索結果を到達証明として読む |
| `ConstraintProfiles` | 制約の追加・除去で到達性がどう変わるか |
| `NonRecoverability` | 注釈なしでは制約を復元できないことの証明 |
| `RequirementSatisfaction` | 前提条件の充足源分類 |
| `Needs` | 画面の必要データを到達可能か否かで分類 |
| `Bridge` | Rust solver の探索結果との突き合わせ検証 |
| `Universe` | Lexicon₀/₁ の宇宙レベル分離、encoding の非正準性 |
| `Transition` | 遷移の圏構造、合成等価性、型レベル条件分岐 |
| `Monotonicity` | guard と fire の単調性、inhibitor arc の不在 (WSTS 所属)。RichTransition (consumes あり) の単調性も含む |
| `Termination` | consumes モデルの停止性。visited set による探索終了の形式的裏付け |
| `Collapse` | Lex1 より上の階層は潰れる: 合成・分岐・列挙はすべて Lex1 に留まる |

`*Demo`, `Observe`, `Diff`, `Materialize`, `GoalSelection` は具体例の検証・実験用。上の表には含めていない。

### 依存関係

```text
Basic
├── Annotation
│   └── AnnotationTable
├── Refinement
│   └── Canonical
├── Interpretation
│   ├── Universe
│   └── Transition
├── Reachability
│   ├── Monotonicity [← Transition]
│   │   └── Termination
│   └── Search
│       └── Witness
│           ├── Bridge
│           └── Collapse [← Transition]
├── ConstraintProfiles
├── NonRecoverability
└── RequirementSatisfaction
    └── Needs
```

### Laplan solver との対応

| lean-lexicon | Laplan |
|---|---|
| `Basic` | 型定義 (`.lex` の型宣言) |
| `Annotation` | rule の制約 (capability, consumes) |
| `Search` | solver (BFS 経路探索) |
| `Witness` | recipe |
| `Needs` | `EndpointKind` による endpoint 診断 |
| `Monotonicity` (RichTransition) | solver の Execute モード (consumes あり) |
| `Termination` (RichReachesBy) | solver の visited set 停止性保証 |
| `Collapse` | solver の max_depth パラメータ (有界探索の正当化) |

## ビルド

```bash
lake build
```
