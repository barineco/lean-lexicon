# Lean Lexicon

[English](README.md)

AT Protocol の Lexicon を Lean 4 / Mathlib で形式化するプロジェクト。

**254 定理/補題、zero sorry。** Lean v4.29.0, Mathlib v4.29.0。

## 概要

Lexicon を**型の宇宙**として捉え直す。各 endpoint は型の間の射であり、API を使うことは射を合成して目的地に到達すること。

```
createSession: {identifier, password} → {accessJwt, did, ...}
getProfile:    {accessJwt, actor}     → {profileViewDetailed}
```

2 つを繋ぐと `{identifier, password} → createSession → getProfile → {profileViewDetailed}` という経路が得られる。この経路が操作手順の**証人 (witness)**。

## Lean の役割

経路を見つけるのは [Laplan](https://github.com/barineco/laplan) の solver。Lean は solver が返す結果に**意味論的な保証**を与える proof layer を提供する。対象は経路の正しさ、制約の効果、不足情報の分類。

## 検証された定理

### 経路と到達可能性

| 定理群 | モジュール | 内容 |
|---|---|---|
| 経路は到達証明 | Witness | endpoint 名の列が目標への serial witness になること |
| 制約で到達性が変わる | ConstraintProfiles | 包含関係・所有権の追加で経路数が変化すること |
| 注釈は型から復元不能 | NonRecoverability | 同じ型構造でも注釈の有無で到達性が異なること |

制約の効果の具体例:

| 目標 | 開通条件 | 経路数 |
|---|---|---|
| 自分のプロフィール取得 | 包含関係の追加 | 1 |
| 自分の repo 読み取り | 所有権の追加 | 1 |
| 自分の repo への書き込み | 全制約の追加 | 1 |
| フィード取得 | 制約によらず同じ (構造的同型) | 3 |

### 前提条件と needs assessment

| 定理群 | モジュール | 内容 |
|---|---|---|
| 前提条件 ≠ 入力フィールド | RequirementSatisfaction | JWT 等の暗黙の前提が入力フィールドに現れないこと |
| 5 層の needs assessment | Needs | 画面の必要データを 5 段階で分類 (8 画面で検証) |

前提条件の充足源分類:

| 充足源 | 例 |
|---|---|
| ユーザーが直接与える | パスワード |
| 手持ちに既にある | 前の操作で得た値 |
| 他の endpoint の出力 | createSession が返す認証トークン |
| 所有権から導出 | did から自分のリポジトリ |
| 型の包含関係から導出 | did → at-identifier |

5 層の assessment:

| assessment | 意味 |
|---|---|
| already satisfied | 手持ちに既にある |
| witness available | serial recipe で到達可能 |
| recoverable by recipe | 追加 recipe で回収可能 |
| needs user action | ユーザー操作が必要 |
| pruned by boundary | 注釈側の判別条件が不足 |

### 宇宙分離と圏構造

| 定理群 | モジュール | 内容 |
|---|---|---|
| Lexicon₀/₁ の宇宙分離 | Universe | encoding の非正準性 (提示方法が一意でない) |
| 遷移の圏構造 | Transition | 結合律、単位律、合成等価性 |
| 分岐は型構造の帰結 | Transition | branch = union dispatch + 射の合成 |

主要な個別定理:

| 定理 | 内容 |
|---|---|
| `encoding_noncanonical` | 2 つの encoding が異なる LexValue を返す |
| `no_injection_to_finite` | 有限型への injection は不可能 |
| `Transition.seq_assoc` | 合成の結合律 |
| `Transition.id_seq` / `seq_id` | 左右の単位律 |
| `timeline_equiv_follows_then_feed` | getTimeline ≈ getFollows ; map(getAuthorFeed) |
| `double_refresh_blocked` | refresh token の二重使用は不可能 (linear use) |
| `branch_is_dispatch_then_seq` | 分岐 = union dispatch + 射の合成 |
| `timed_filter_expiry` | 時間制約付き token の失効 |

### 単調性と階層の崩壊

| 定理群 | モジュール | 内容 |
|---|---|---|
| guard/fire の単調性 | Monotonicity | marking の包含に対する単調性 (WSTS 所属) |
| consumes ありの単調性 | Monotonicity | RichTransition.fire = (m \ C) ∪ P が単調 |
| inhibitor arc の不在 | Monotonicity | 正のメンバーシップテストのみ → 遷移を無効化するトークンがない |
| 階層の崩壊 | Collapse | Lex1 より上は潰れる: 合成・分岐・列挙はすべて Lex1 に留まる |

Lex0 (型) と Lex1 (射) の間にのみ実在の壁がある。Lex1 より上の「レベル」(endpoint の合成、条件分岐、ユーザー操作列) はすべて `TypedTransition` に留まる。根拠: `TypedTransition.seq` が `TypedTransition` を返す (合成の閉性)、`branch_is_dispatch_then_seq` (分岐の還元)、`searchAll` (全経路の列挙)。「Lex2 (functor)」と「Lex1 (morph)」の区別は、内部の分岐をどこまで展開するかという観測粒度の問題であり、計算量的性質ではない。

### 停止性 (consumes モデル)

| 定理群 | モジュール | 内容 |
|---|---|---|
| consumes 経路 | Termination | RichReachesBy: consumes ありの遷移経路の帰納的定義 |
| 宇宙閉包 | Termination | fire が有限宇宙内に留まることの保証 |
| visited-set 停止性 | Termination | 探索空間が 2^|U| で有界、各ステップで gap が減少 |
| consumes 循環検出 | Termination | A/B サイクルが visited set で検出されることの証明 |

consumes (排他リソース消費) がある場合、marking は縮小しうるため経路全体の停止性は自明ではない。Rust solver は visited set で同一 marking への再訪を防ぐ。Termination モジュールはこの戦略が有限ステップで必ず停止することを証明する。

主要な個別定理:

| 定理 | 内容 |
|---|---|
| `fire_within_universe` | consumes ありの fire が有限宇宙内に留まる |
| `visited_card_le_powerset` | visited 集合の要素数は 2^|U| 以下 |
| `searchGap_decreases` | 新しい marking 追加で探索ギャップが厳密に減少 |
| `consumes_cycle_revisits` | A;B サイクルが初期 marking に戻る |

## 4 つの見方

**Tarski 宇宙**: Lexicon のスキーマを型の名前 (code)、endpoint の動作を型の中身 (解釈) と見る。型の名前だけでは解釈が一意に定まらない。注釈が解釈を確定させる。

**ペトリネット**: endpoint を遷移、型を場所、値をトークンと見る。endpoint を呼ぶとトークンが移動する。目標のトークン配置に到達できるかが到達可能性問題。

**tactic モード**: Lean の証明と同じ構造で API 利用を読む。目標 (欲しいデータ) に対して endpoint を適用し、仮説 (持っているデータ) を変形して目標を達成する。到達不能は「この前提では証明できない」に対応する。

**圏論**: endpoint を射、型を対象とする圏を構成する。合成の結合律、恒等射、単位律は証明済み。codegen はこの圏からターゲット言語の圏への関手であり、条件分岐は union 型の dispatch と射の合成から導出される。

## モジュール構成

| ファイル | 役割 |
|---|---|
| `Basic` | Lexicon の型の基本定義 (TypeExpr: atom, array, object, union) |
| `Annotation` | 前提条件 / 状態操作の最小注釈 |
| `AnnotationTable` | endpoint ごとの注釈テーブル |
| `Refinement` | 型構造から機械導出できる部分 |
| `Canonical` | 型構造導出 + 注釈の合成 |
| `Interpretation` | 型 + 注釈から手持ちデータ集合への意味を与える |
| `Reachability` | 目標に到達できるかの判定 |
| `Search` | 有界探索 |
| `Witness` | 探索結果を到達証明として読む |
| `ConstraintProfiles` | 制約の追加・除去で到達性がどう変わるか |
| `NonRecoverability` | 注釈なしでは制約を復元できないことの証明 |
| `RequirementSatisfaction` | 前提条件の充足源分類 |
| `Needs` | 画面の必要データを到達可能 / 未到達に分類 |
| `Bridge` | Rust solver の探索結果との突き合わせ検証 |
| `Universe` | Lexicon₀/₁ の宇宙レベル分離、encoding の非正準性 |
| `Transition` | 遷移の圏構造、合成等価性、型レベル条件分岐 |
| `Monotonicity` | guard と fire の単調性、inhibitor arc の不在 (WSTS 所属)。RichTransition (consumes あり) の単調性も証明 |
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
| `Annotation` | morphism の制約 (capability, consumes) |
| `Search` | solver (BFS 経路探索) |
| `Witness` | serial recipe |
| `Needs` | needs assessment (5 層診断) |
| `Monotonicity` (RichTransition) | solver の Execute モード (consumes あり) |
| `Termination` (RichReachesBy) | solver の visited set 停止性保証 |
| `Collapse` | solver の fuel パラメータ (有界探索の正当化) |

## ビルド

```bash
lake build
```
