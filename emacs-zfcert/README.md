# ZFCert Emacs mode

`zfcert-mode.el`は、ZFCertの`.zfp`証明ファイルを編集・検査するための
Emacsメジャーモードです。追加パッケージには依存しません。

## インストール

次をEmacsの設定へ追加します。パスはZFCertを配置した場所に合わせてください。

```elisp
(add-to-list 'load-path "/path/to/ZFCert/emacs-zfcert")
(require 'zfcert-mode)
```

`.zfp`を開くと`zfcert-mode`が有効になります。最初の検査時にプロジェクトの
`dune-project`を探索し、必要ならローカルカーネルを自動起動します。

別の場所にプロジェクトがある場合は次のように指定できます。

```elisp
(setq zfcert-workspace-root "/path/to/ZFCert")
```

## 操作

| キー | コマンド | 動作 |
|---|---|---|
| `C-c C-RET` | `zfcert-run-to-point` | カーソルのある行まで実行 |
| `C-c C-n` | `zfcert-run-next-line` | 次の行まで実行し、その行へ移動 |
| `C-c C-c` | `zfcert-check-buffer` | 証明全体を検査 |
| `C-c C-g` | `zfcert-show-goals` | 現在の証明状態を表示 |
| `C-c C-r` | `zfcert-restart-kernel` | カーネルを再起動 |
| `C-c C-k` | `zfcert-stop-kernel` | カーネルを停止 |

仮定とゴールは`*ZFCert Goals*`バッファへ表示されます。エラー時は該当行も
強調表示されます。

`resolution`など時間のかかる証明にも対応するため、HTTPリクエストの既定の
タイムアウトは60秒です。さらに長い証明では`M-x customize-variable RET
zfcert-request-timeout`で値を増やすか、`nil`にして無制限に待機できます。

コメントは`(* ... *)`で囲み、複数行・入れ子にもできます。`#`から行末までの
行コメントも利用できます。Emacsのコメント操作では`(* ... *)`を挿入します。

編集後の自動検査を有効にする場合は次を設定します。

```elisp
(setq zfcert-auto-refresh t)
```

## テスト

プロジェクトルートで次を実行します。

```sh
emacs -Q --batch \
  -L emacs-zfcert \
  -l emacs-zfcert/test/zfcert-mode-test.el \
  -f ert-run-tests-batch-and-exit
```

カーネルの自動起動を含む結合試験は次で実行できます。

```sh
emacs -Q --batch \
  -L emacs-zfcert \
  -l emacs-zfcert/test/integration-test.el
```
