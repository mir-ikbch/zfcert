;;; integration-test.el --- ZFCert Emacs integration test -*- lexical-binding: t; -*-

(require 'zfcert-mode)

(setq zfcert-workspace-root default-directory)
(setq zfcert-server-url
      (or (getenv "ZFCERT_SERVER_URL") "http://127.0.0.1:8103"))
(setq zfcert-auto-start-kernel t)

(unwind-protect
    (progn
      (zfcert--ensure-kernel)
      (with-temp-buffer
        (insert-file-contents "examples/specialize.zfp")
        (let ((complete
               (zfcert--request
                "POST" "api/check"
                (buffer-substring-no-properties (point-min) (point-max)))))
          (unless (and (alist-get 'ok complete)
                       (equal (alist-get 'theorem complete)
                              "universal_contradiction")
                       (string-match-p
                        "∀a, ∀b,"
                        (alist-get 'statement complete))
                       (equal (alist-get 'message complete)
                              "証明がカーネルによって検証されました"))
            (error "Complete proof was rejected: %S" complete)))
        (goto-char (point-min))
        (search-forward "specialize H a as Hna.")
        (let ((state
               (zfcert--request
                "POST" "api/step"
                (buffer-substring-no-properties
                 (point-min) (line-end-position)))))
          (unless (and (alist-get 'ok state)
                       (alist-get 'goals state)
                       (string-match-p
                        "∈"
                        (alist-get
                         'target
                         (car (alist-get 'goals state)))))
            (error "Interactive proof state was rejected: %S" state))))
      (princ "ZFCert Emacs integration test passed\n"))
  (zfcert-stop-kernel))

;;; integration-test.el ends here
