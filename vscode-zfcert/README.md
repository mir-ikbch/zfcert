# ZFCert for VS Code

`.zfp`ファイルを編集しながら、OCamlカーネルで一手ずつ証明を検査するVS Code拡張です。

## VSIXのインストール

リポジトリ直下の `zfcert-vscode-0.2.0.vsix` をVS Codeの
`Extensions: Install from VSIX...` で選択します。

## 開発版の起動

1. ZFCertリポジトリをVS Codeで開きます。
2. `Run and Debug`から `Run ZFCert Extension` を実行します。
3. 開いたExtension Development Hostで `examples/specialize.zfp` を開きます。
4. カーソルを証明の途中へ移動すると、ZFCertサイドバーにその位置のゴールが出ます。

コマンドパレットから次の操作もできます。

- `ZFCert: Run to Cursor`
- `ZFCert: Check Entire Proof`
- `ZFCert: Restart Kernel`
- `ZFCert: Stop Kernel`

カーソル位置までの実行はmacOSで `Cmd+Alt+Enter`、その他では
`Ctrl+Alt+Enter`です。全体検証はさらにShiftを加えます。

拡張は既定でワークスペース直下から次を自動起動します。

```sh
dune exec src/main.exe -- --port 8099
```

既存サーバーを利用する場合は `zfcert.serverUrl` を変更し、
`zfcert.autoStartKernel` を無効にしてください。

`.zfp`ファイルの親フォルダから `dune-project` を自動探索します。別の場所に
証明ファイルを置く場合は、コマンドパレットの
`ZFCert: Select Project Folder` からこのリポジトリを選択してください。
Goalsビューが閉じている場合は `ZFCert: Show Goals` で再表示できます。

命題にはCoq風の透明な名前を付けられます。`Definition`だけを書いた時点でも
Goalsビューに読み込まれた定義が表示されます。

```text
Definition is_empty x := forall y, not (y in x).
```

プリミティブな自然演繹規則は`rule`で直接適用できます。

```text
theorem equality_by_rules :
  forall x, x = x.
rule all_intro x.
rule equal_refl.
qed.
```
