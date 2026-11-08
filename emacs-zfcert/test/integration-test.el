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
                              "The proof was verified by the extracted kernel."))
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
      (let ((directory (make-temp-file "zfcert input 証明 #100%-" t)))
        (unwind-protect
            (progn
              (make-directory (expand-file-name "lib" directory))
              (with-temp-file (expand-file-name "lib/base.zfp" directory)
                (insert "theorem imported_identity : forall x, x = x.\n"
                        "intro x.\nrefl.\nqed.\n"))
              (with-temp-file (expand-file-name "lib/middle.zfp" directory)
                (insert "input \"base.zfp\".\n"))
              (with-temp-file (expand-file-name "main.zfp" directory)
                (insert "bogus.\n"))
              (with-temp-buffer
                (setq buffer-file-name (expand-file-name "main.zfp" directory))
                (insert "input \"lib/middle.zfp\".\n"
                        "theorem from_input : forall x, x = x.\n"
                        "put imported_identity.\n"
                        "exact imported_identity.\nqed.\n")
                (let ((complete (zfcert--request
                                 "POST" "api/check" (buffer-string))))
                  (unless (and (alist-get 'ok complete)
                               (equal (alist-get 'theorem complete) "from_input"))
                    (error "Nested input proof was rejected: %S" complete)))
                (goto-char (point-min))
                (forward-line 2)
                (let ((state (zfcert--request
                              "POST" "api/step" (zfcert--buffer-through-line))))
                  (unless (and
                           (alist-get 'ok state)
                           (cl-find "imported_identity"
                                    (alist-get 'context (car (alist-get 'goals state)))
                                    :key (lambda (entry) (alist-get 'name entry))
                                    :test #'equal))
                    (error "Nested input proof state was rejected: %S" state)))))
          (delete-directory directory t)))
      (princ "ZFCert Emacs integration test passed\n"))
  (zfcert-stop-kernel))

;;; integration-test.el ends here
