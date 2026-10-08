# satsuma-rs

[English version here](README.md)

[satsuma](https://github.com/markusa4/satsuma)（v1.4、C++）のピュアRust移植版 —
SAT向け静的対称性破壊プリプロセッサです。

DIMACS CNF式を入力し、任意のSATソルバに渡せる等充足な式を出力します。
2つのモードがあります：

- **`fix`**：反復的な対称性ベースの簡約・固定（デフォルト）。
- **`lex`**：lex-leader対称性破壊制約。

依存クレートゼロ（crates.io依存なし）、edition 2021。

## ステータス

自己完結コアの移植＋実際に動作するピュアRust対称性エンジンを備えます：

- DIMACSパース、watch付きリテラルストア（単位伝播・pureリテラル・
  subsumption・同値リテラル）
- 重複除去節DB＋at-most-one（AMO）補完
- モデルグラフ自己同型探索（individualization–refinement同型探索、
  候補は全て式に対して厳密検証）
- lex-leader破壊制約（チェイン符号化、逆元分、群を保つ積による
  サポート短縮）
- 不動点反復：破壊節を式に戻して伝播
- 証明ログ（SR / binary SR / VeriPBプレースホルダ）、統計トラッカ
- 本家互換CLI（`fix` / `lex`、`--file`、`--out-file`、
  `--proof-file`、`--break-depth`、`--opt`、`--preprocess-cnf`、…）

C++版との既知の差：Johnson/row/row-column構造検出なし、
orbitopal/Schreier fixingなし（lex＋伝播のみ）、VeriPB証明規則は
プレースホルダ、検出はdejavuより低速（時間予算式で調整可）。
詳細は[移植メモ](#移植メモ)。

## ビルド

Rustツールチェイン（1.70+）とCリンカが必要です：

```sh
cargo build --release
```

## CLIの使い方

```sh
# 反復fixing（デフォルトは標準出力へ）
./target/release/satsuma fix examples/php-015-014.cnf > out.cnf

# lex-leader制約
./target/release/satsuma lex formula.cnf --out-file out.cnf

# 標準入力＋証明ログ
cat formula.cnf | ./target/release/satsuma fix --proof-file proof.out > out.cnf
```

主なオプション：

| フラグ | 効果 |
|---|---|
| `--file`、`--out-file`、`--proof-file` | 入力 / 出力 / 証明のパス |
| `--break-depth N` | 生成子あたりのlex位置数（デフォルト512） |
| `--preprocess-cnf` | `lex`モードでのunit＋pure簡約 |
| `--schreier-cuts` / `--binary-clauses` | 互換性のため受理 |
| `--add-reduced-as-unit` | 元の式に有効なモデルを維持 |
| `--opt` / `--no-opt` | 生成子サポート短縮（デフォルトON） |
| `--sym-timeout MS` | ラウンドあたりの検出予算（デフォルト2000） |
| `--sym-pairs N` | セルあたりの最大ペア試行数（デフォルト512） |
| `--sym-nodes N` | ペアあたりの最大探索ノード数（デフォルト50000） |
| `--sr` / `--veripb` / `--bsr` | 証明形式（デフォルトSR） |
| `--silent` / `--verbose` | ログ制御 |

SATソルバとの連携例：

```sh
satsuma fix php-015-014.cnf > php-015-014.break.cnf
cryptominisat5 php-015-014.break.cnf
```

## ライブラリの使い方

```rust
use satsuma::{Mode, Preprocessor, PreprocessorConfig};

let dimacs = "p cnf 2 2\n1 2 0\n-1 -2 0\n";

// デフォルトのfixモード
let mut pp = Preprocessor::fix();
let out = pp.preprocess_str(dimacs).expect("valid dimacs");
println!("{}", out.dimacs); // `p cnf ...`＋破壊節

// 設定のカスタマイズ
let config = PreprocessorConfig::new(Mode::Lex)
    .with_break_depth(64)
    .with_sym_time_budget_ms(2000);
let mut pp = Preprocessor::with_config(config);
let out = pp.preprocess_str(dimacs).unwrap();
assert!(!out.is_unsat());
```

`Output` は `dimacs`、`n_variables`、`n_clauses`、`n_sbp_clauses`、
`n_extra_variables`、`n_generators`、`iterations`、`propagations`、
任意の `proof_text` を持ちます。

独自の対称性バックエンドは `SymmetryProvider` traitで差し替え可能です：

```rust
use satsuma::symmetry::{SymmetryGroup, SymmetryProvider};
use satsuma::Cnf;

struct MyBackend;
impl SymmetryProvider for MyBackend {
    fn detect(&mut self, formula: &Cnf) -> SymmetryGroup {
        // ... 検証済み生成子＋変数順序を返す ...
    }
}
```

## モジュール構成

| モジュール | 内容 |
|---|---|
| `parser` | DIMACS CNFパース（文字列・ファイル・標準入力） |
| `cnf2wl` | watch付きストア：伝播・pure・subsumption・同値 |
| `cnf` | 重複除去節DB＋AMO補完 |
| `graph` | 色付きモデルグラフ＋正準色付けrefinement（WL-1） |
| `automorphism` | 同型探索・厳密検証・`GraphAutomorphismProvider` |
| `predicate` | 対称性破壊述語（lex-leader符号化） |
| `preprocessor` | `PreprocessorConfig`＋パイプライン（fix/lex・反復） |
| `symmetry` | `SymmetryProvider` trait・置換・軌道分割 |
| `proof` | 証明ログ（SR / binary SR / VeriPB） |
| `tracker` | 実行統計 |
| `literal` | SATリテラル⇔グラフ頂点の対応付け |

## 検証

- `cargo test`：単体・結合テスト21件＋doctest。
- C++ビルドとの差分テスト：出力のDIMACS妥当性＋等充足性（DPLL判定）を、
  ランダム・対称性植え付け・鳩の巣・unit系・大規模・エッジケースの
  数百式×両モードで確認し、数千実行で違反ゼロ。

## 移植メモ

- 対称性破壊は（検証済み）部分群に対するもので、検出が部分的でも
  簡約が弱くなるだけで健全性は保たれます。
- 割当済みリテラルはモデルグラフ上で別色にし、現在の部分割当を
  安定化する対称性のみ検出します（簡約後の破壊の健全性に必須。
  BreakIDと同手法）。
- 検出は実時間予算式のため、見つかる生成子集合（＝簡約の強さ）は
  実行ごとに変わり得ます。出力は常に等充足です。
- lex-leader節の証明ログはベストエフォートです（規則レベルのVeriPB
  出力は今後の課題。本家でもexperimental扱いです）。

## 関連文献

上流の設計は以下で解説されています：

- “Satsuma: Structure-based Symmetry Breaking in SAT”（SAT ’24）—
  Markus Anders, Sofia Brenner, Gaurav Rattan
- “Algorithms Transcending the SAT-Symmetry Interface”（SAT ’23）—
  Markus Anders, Mate Soos, Pascal Schweitzer
- “SAT Preprocessors and Symmetry”（SAT ’22）— Markus Anders

## ライセンス

上流に合わせてMIT。上流の著作権はMarkus Anders（markusa4/satsumaの
`LICENSE`参照）。置き換えた`tsl` robin-hoodハッシュヘッダの著者は
Thibaut Goetghebuer-Planchonです。
