# ZFCert

自然演繹と ZFC を基礎にした、小さな OCaml 製の定理証明支援系です。論理核は Coq
で形式化され、抽出された OCaml コードが証明状態と証明書を検査します。

## ビルドとエディタ設定

### 必要なもの

- OCaml 5.x
- Dune 3.17 以上
- Coq（Coq の形式化を検査するとき。`make coq` が `coqc` を呼び出します）
- VS Code 拡張を開発・パッケージ化する場合は Node.js

### 最短手順（ソースから利用する場合）

まずリポジトリのルートで一度だけビルドします。

```sh
dune build
```

その後は、使うエディタに応じて次の設定だけで利用できます。

#### VS Code

1. リポジトリのルートを VS Code で開く。
2. [`zfcert-vscode-0.2.0.vsix`](zfcert-vscode-0.2.0.vsix) を `Extensions: Install from VSIX...` でインストールする。
3. `.zfp` ファイルを開く。サイドバーの **ZFCert Goals** に証明状態が表示される。

カーソル位置まで実行するには macOS では `Cmd+Alt+Enter`、その他では
`Ctrl+Alt+Enter` を押します。全体を検査するには `Shift` も加えます。

#### Emacs

Emacs の設定に次を追加して `.zfp` ファイルを開きます。

```elisp
(add-to-list 'load-path "/absolute/path/to/zfprover/emacs-zfcert")
(require 'zfcert-mode)
```

プロジェクトを自動検出できない場合だけ、次も設定します。

```elisp
(setq zfcert-workspace-root "/absolute/path/to/zfprover")
```

`C-c C-RET` でカーソル行まで、`C-c C-n` で次の行まで、`C-c C-c` でファイル全体を
検査します。証明状態は `*ZFCert Goals*` に表示されます。

### CLI

リポジトリのルートで、抽出カーネルを含む回帰試験を実行できます。

```sh
dune exec src/main.exe -- --self-test
```

単一の `.zfp` ファイルを一度に検査するには `--check` を使います。

```sh
dune exec src/main.exe -- --check examples/specialize.zfp
```

成功時は `OK` を表示して終了コード 0、構文・証明エラー時はファイル名と行番号を表示して
終了コード 1 になります。CI では次のように利用できます。

```sh
dune exec src/main.exe -- --check path/to/proof.zfp
```

`--check` はファイル全体を読み込んで `qed.` まで含めて検査します。

### Coq 形式化と抽出

Coq のすべての形式化を検査するには次を実行します。

```sh
make coq
```

Coq の抽出物を更新した場合は、形式化の検査を含めて次を実行します。

```sh
make extract
dune build
```

生成された `extracted/proof_state.ml` はリポジトリに含まれる抽出物です。通常の利用では
手で編集しません。

### VS Code 拡張（詳細設定）

拡張はワークスペース内の `dune-project` を自動検出します。検出できない場合は
`zfcert.workspaceRoot` に `dune-project` のあるディレクトリを指定してください。

```json
{
  "zfcert.workspaceRoot": "/absolute/path/to/zfprover",
  "zfcert.dunePath": "dune"
}
```

Goals ビューが閉じている場合はコマンドパレットの `ZFCert: Show Goals` で再表示できます。
開発版は `Run and Debug > Run ZFCert Extension` で起動できます。拡張のテストと VSIX の
作成は次のとおりです。

```sh
cd vscode-zfcert
npm test
npm run package
```

### Emacs 拡張（詳細設定）

`zfcert-workspace-root` が `nil` なら現在のファイルから `dune-project` を自動探索します。
長い `resolution` を待つ場合は `M-x customize-variable RET zfcert-request-timeout` で
タイムアウトを変更できます。その他の設定とキーバインドは
[Emacs 拡張の README](emacs-zfcert/README.md) を参照してください。

### WebAssembly 版（任意）

静的サイトで Web UI を動かす場合は、`wasm_of_ocaml` と Binaryen 119 以上が必要です。
macOS では次のように環境を用意できます。

```sh
brew install binaryen
opam switch create zfprover-wasm 5.2.0
opam install --switch=zfprover-wasm dune.3.23.1 wasm_of_ocaml-compiler js_of_ocaml js_of_ocaml-ppx
eval $(opam env --switch=zfprover-wasm)
make wasm
```

生成された `web/wasm/main.bc.wasm.js`、`web/wasm/main_js.bc.js`、
`web/wasm/main.bc.wasm.assets/` を `web/` とともに静的ホスティングへ配置します。

## タクティクの用法

### 基本的な入力

宣言とタクティクはすべて `.` で終わります。文中の改行は空白と同じなので、論理式や
タクティクの引数を複数行に分けられます。`forall x, P` と `exists x, P` の区切りは
ピリオドではなくコンマです。

`(* ... *)` は複数行・入れ子に対応するコメントです。従来の `#` から行末までの
コメントも使えます。

ZFCert の項は変数または関数項です。関数項は `pair(a, b)` のように書き、0 引数の
定数は `empty` のように括弧を省略できます。原子式と論理結合子は次のとおりです。

```text
x = y              # 等号
x in y             # 所属（x ∈ y も可）
not P              # ¬P
P and Q            # P ∧ Q
P or Q             # P ∨ Q
P -> Q             # P → Q（右結合）
P <-> Q            # P ↔ Q
forall x, P        # ∀x, P
exists x, P        # ∃x, P
false              # ⊥
```

### 定理、別名、Choose

```text
alias is_empty x := forall y, not (y in x).
alias empty_alias x := is_empty x.

theorem alias_identity : forall a, (empty_alias a -> is_empty a).
intros a H.
exact H.
qed.
```

`alias` は透明な命題の別名であり、証明済みの事実ではありません。適用時には引数が
同時に代入され、変数捕獲を避けるために必要なら内部で名前が変更されます。引数なしなら
`alias foo := P.` と書けます。`intro x y.` のように `intro` に複数の名前を渡すことは
できません。複数導入には `intros x y.` を使います。

`Choose` は、存在命題の証明書を検査した後で、定数または関数記号と具体化済みの事実を
グローバル環境に追加します。

```text
Choose empty Hempty from empty_set.
Choose pair Hpair from pairing.

theorem pair_shape :
  forall a, forall b, forall x,
    (x in pair(a,b) <-> (x = a or x = b)).
put Hpair.
exact Hpair.
qed.
```

`Choose f H from fact.` は `forall ... exists ...` から関数記号 `f` を導入します。
存在事実に具体化項を指定すると、0 引数の定数を選べます。Choose で追加された事実や
以前の定理は後続の証明状態・`resolution` の探索範囲には自動では入りません。必要なら
`put Hempty.` や `put previous_result.` で現在の仮定に明示的に追加してください。
ただし、`specialize`、`apply`、`exact`、`obtain`、`cases`、`rewrite` など、名前を
指定するタクティクからは参照できます。

`qed.` の後には次の定理や宣言を書けます。

```text
theorem previous_result : forall x, x = x.
intro x.
refl.
qed.

theorem use_previous_result : forall a, a = a.
intro a.
put previous_result.
resolution.
qed.
```

### 導入、適用、分解

```text
theorem implication_identity : forall x, forall y, (x = y -> x = y).
intros.
exact H.
qed.
```

- `intro x.` は含意・否定・全称ゴールを一つ導入します。`intro.` では全称変数の元の
  名前を使います。
- `intros x y H.` は複数の `intro` と同じです。`intros.` は導入可能なものをすべて
  自動導入し、衝突時は `x0`, `x1`, ... のような fresh 名を使います。
- `assumption.` はゴールと一致する仮定を閉じます。
- `exact H.` は仮定・公理・以前の定理をそのままゴールに使います。
- `apply H.` は含意の結論を現在のゴールに合わせます。全称変数をゴールから特定できない
  ときは推測せず失敗します。その場合は `specialize H a as Ha.` のように先に具体化します。
- `apply H0 in H as H1.` は `H0` の一つの含意前提に `H` を適用し、結果を `H1` として
  仮定に追加します。
- `specialize H a b as Hab.` は全称仮定を複数の項で一度に具体化します。
- `obtain p Hp from H.` は存在仮定を具体化し、`p` と `Hp` を追加します。
- `cases H H1 H2.` は連言・同値・選言・存在仮定を分解します。名前を省略できる場合は
  `cases H.` で自動名を使います。
- `split.` は連言または同値ゴール、`left.` / `right.` は選言ゴールを分けます。
- `use t.` は存在ゴールの証人に項 `t` を指定します。

### 等号、規則、公理

```text
theorem and_commutes :
  forall x, forall y, ((x in y and y in x) -> (y in x and x in y)).
intros x y H.
split.
apply H.
apply H.
qed.
```

`rewrite H.` は `H : a = b` を使ってゴール中の `a` を `b` に置換し、`rewrite <- H.`
は逆方向に置換します。現在は名前付き項の等式を対象にしています。

`refl.` は `t = t`、`contradiction.` は矛盾する仮定からの証明に使います。空集合公理は
`empty_set` という名前で登録されています。

```text
theorem empty_set_exists : exists e, forall x, not (x in e).
exact empty_set.
qed.
```

プリミティブ規則は `rule` で直接適用できます。

```text
theorem equality_by_rules : forall x, x = x.
rule all_intro x.
rule equal_refl.
qed.
```

利用できる規則は次のとおりです。

```text
axiom          hypothesis     falsum_elim
impl_intro     impl_elim
conj_intro    conj_elim_l     conj_elim_r
disj_intro_l  disj_intro_r    disj_elim
all_intro     all_elim
ex_intro      ex_elim
equal_refl    equal_elim
cut
```

`Cut` と等号除去の例です。

```text
rule cut H : P.
rule equal_elim s t x : P.
```

分出・置換の公理図式は次のように指定します。分出のソース集合には変数だけでなく
`pair(a, b)` のような一般の項を使えます。

```text
separation S pair(a, b) x : not (x in x).
replacement R a x y : y = x.
```

### `resolution`

`resolution.` は、対応範囲の仮定を命題論理の節へ変換して resolution refutation を
探索し、得られた導出を `cut`、選言除去、含意除去、量化子除去などのプリミティブ規則列へ
変換してから抽出カーネルで検査します。`and`、`or`、`->`、`<->` と複合ゴールを扱い、
先頭の `forall` 仮定は単一化で具体化します。先頭の `exists` 仮定は fresh な変数を
導入してそのスコープ内で証明します。

Skolem 化はまだ行わないため、対応範囲外の量化子は原始命題として扱われます。対応範囲
外の仮定が混ざっていても、必要な仮定だけを使って探索します。長い探索の計測値は次で
表示できます。

```sh
ZFCERT_RESOLUTION_STATS=1 dune exec src/main.exe -- --self-test
```

## ファイル構成と検証の仕組み

### Coq 形式化

- [`coq/FOL.v`](coq/FOL.v): 一階述語論理の構文、代入、Tarski 型意味論、直観主義自然演繹、
  等号規則、`natural_deduction_sound`、相対的無矛盾性。
- [`coq/ProofState.v`](coq/ProofState.v): 抽出可能な de Bruijn ベースの証明状態、
  プリミティブ `rule`、表面 `tactic`、`step`、`run`。`step_sound`、`run_sound`、
  `successful_run_derives` を含みます。
- [`coq/TacticCompleteness.v`](coq/TacticCompleteness.v): プリミティブ規則列の
  `rule_step`、`rule_run` と、完全な公理判定器に対する
  `derives_iff_rule_success`、`derives_has_rule_list`。
- [`coq/NamedProofState.v`](coq/NamedProofState.v): de Bruijn 核を文字列名の変数・
  仮定へ接続する抽出可能な層。`named_start`、`named_goals`、`named_step`、
  `named_rule_run` と各遷移の健全性を定義します。
- [`coq/NamedCommands.v`](coq/NamedCommands.v): 固定 ZFC 公理、分出、置換を名前付き
  プリミティブ規則列へ展開します。
- [`coq/CertifiedSession.v`](coq/CertifiedSession.v): 公理能力を付けた証明書、
  `certified_run`、`certified_finalize` とその健全性。
- [`coq/GlobalEnvironment.v`](coq/GlobalEnvironment.v): 文字列名の定数と事実を保持する
  グローバル環境、`global_declare_choice` と環境遷移の健全性。
- [`coq/ZFC.v`](coq/ZFC.v): 空集合、外延性、対、和、冪集合、正則性、無限、分出、置換、
  選択を論理式として定義します。古典論理は排中律の公理図式として明示的に分離します。
- [`coq/ExtractProofState.v`](coq/ExtractProofState.v): 抽出用エントリポイント。
- [`coq/Audit.v`](coq/Audit.v): 主要定理の仮定を監査します。`make coq` で `Admitted` なし
  の検査を行います。

### 抽出物と OCaml

- `extracted/proof_state.ml`: Coq から抽出された raw 実装。通常は直接編集しません。
- [`extracted/zfcert_kernel.mli`](extracted/zfcert_kernel.mli): アプリケーションに公開する
  facade。`Zfcert_kernel.state` と `environment` は抽象型で、初期化と状態遷移は抽出された
  関数の返り値からしか得られません。
- `src/syntax.ml`: 論理式の構文木、表示、自由変数、捕獲回避代入、α同値。
- `src/parser.ml`: 字句解析、論理式の優先順位、複数行文、終端 `.`、コメント。
- `src/kernel_syntax.ml`: 表面構文と抽出された名前付き構文の変換。
- `src/rule_parser.ml`: `rule` 文を型付きの名前付き規則要求へ変換する純粋なパーサー。
- `src/proof_session.ml`: 別名・Choose の展開、表面タクティクの規則列計画、抽出 API の
  実行、対話的証明状態、`qed` 時の証明書再実行。
- `src/resolution.ml`: `resolution` の節変換、単一化、探索、プリミティブ証明列の生成。
- `src/api_json.ml`: 証明状態、ゴール、エラー、証明書の JSON 表現。
- `src/http_server.ml`: HTTP エンドポイントと静的ファイルの入出力。
- `src/web_api.ml`: Web UI から HTTP 層へ渡す API の薄い接続部。
- `src/self_test.ml`: カーネルと表面構文の回帰試験。
- `src/cli.ml`: コマンドライン引数とサーバー起動。
- `src/main.ml`: `Cli.run` を呼ぶだけのエントリポイント。

### クライアントと依存関係

- `vscode-zfcert/`: VS Code 拡張、サイドバー、カーネルクライアント。
- `emacs-zfcert/zfcert-mode.el`: Emacs の `.zfp` メジャーモードと証明状態表示。
- `web/`: ブラウザ UI と WebAssembly 生成物の配置先。
- `examples/`: `.zfp` の例題。

依存関係は一方向です。

```text
Web / VS Code / Emacs
          |
      HTTP + JSON
          |
    Proof_session
      /       |       \
     v        v        v
 Parser  Rule_parser  Zfcert_kernel facade
              |              |
              v              |
        Kernel_syntax        |
                             |
               Coq-extracted Proof_state (private)
```

OCaml 層は構文解析と表面タクティクの規則列計画を行います。証明状態とグローバル環境の
変更、規則列の実行、`qed` 時の再検査は、Coq から抽出されたカーネルだけが行います。
`Proof_state` は Dune の private module であり、アプリケーション層には公開されません。
Web UI で `Show checked primitive rules` を開くと、終了時に再検査された証明書を確認できます。
