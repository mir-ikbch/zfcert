;;; zfcert-mode-test.el --- Tests for zfcert-mode -*- lexical-binding: t; -*-

(require 'ert)
(require 'zfcert-mode)

(ert-deftest zfcert-mode-is-selected-for-proof-files ()
  (should (eq (cdr (assoc "\\.zfp\\'" auto-mode-alist))
              'zfcert-mode)))

(ert-deftest zfcert-buffer-through-line-includes-the-current-line ()
  (with-temp-buffer
    (zfcert-mode)
    (insert "theorem identity : forall x, x = x.\n")
    (insert "rule all_intro x.\n")
    (insert "rule equal_refl.\n")
    (goto-char (point-min))
    (forward-line 1)
    (should
     (equal
      (zfcert--buffer-through-line)
      (concat "theorem identity : forall x, x = x.\n"
              "rule all_intro x.")))))

(ert-deftest zfcert-mode-binds-current-and-next-line-commands ()
  (should (eq (lookup-key zfcert-mode-map (kbd "C-c C-<return>"))
              #'zfcert-run-to-point))
  (should (eq (lookup-key zfcert-mode-map (kbd "C-c C-RET"))
              #'zfcert-run-to-point))
  (should (eq (lookup-key zfcert-mode-map (kbd "C-c C-n"))
              #'zfcert-run-next-line)))

(ert-deftest zfcert-run-next-line-checks-and-moves-to-the-next-line ()
  (with-temp-buffer
    (zfcert-mode)
    (insert "theorem identity : forall x, x = x.\n")
    (insert "rule all_intro x.\n")
    (insert "rule equal_refl.")
    (goto-char (point-min))
    (let (request-body)
      (cl-letf (((symbol-function 'zfcert--ensure-kernel) #'ignore)
                ((symbol-function 'zfcert--request)
                 (lambda (_method _endpoint body &optional _timeout)
                   (setq request-body body)
                   '((ok . t))))
                ((symbol-function 'zfcert--apply-result)
                 (lambda (result &optional _display) result)))
        (zfcert-run-next-line))
      (should (= (line-number-at-pos) 2))
      (should (= (current-column) 0))
      (should
       (equal request-body
              (concat "theorem identity : forall x, x = x.\n"
                      "rule all_intro x."))))))

(ert-deftest zfcert-run-next-line-stays-put-at-the-last-line ()
  (with-temp-buffer
    (zfcert-mode)
    (insert "theorem identity : forall x, x = x.")
    (goto-char (point-min))
    (let ((origin (point)))
      (should-error (zfcert-run-next-line) :type 'user-error)
      (should (= (point) origin)))))

(ert-deftest zfcert-decodes-raw-utf8-http-response ()
  (let ((raw (apply #'string '(226 136 128 120 44 32 194 172))))
    (should (equal (zfcert--decode-utf8-response raw) "∀x, ¬"))))

(ert-deftest zfcert-mode-recognizes-nested-block-comments ()
  (with-temp-buffer
    (zfcert-mode)
    (insert "theorem t : (* outer (* inner *) comment *) false.")
    (goto-char (point-min))
    (search-forward "inner")
    (should (nth 4 (syntax-ppss)))
    (should (equal comment-start "(* "))
    (should (equal comment-end " *)"))))

(ert-deftest zfcert-render-result-shows-goal-and-context ()
  (let ((result
         '((ok . t)
           (steps . 2)
           (complete . nil)
           (qed . nil)
           (goals
            . (((target . "a ∈ b")
                (context
                 . (((name . "H")
                     (formula . "∀x, ¬x ∈ b"))))))))))
    (zfcert--render-result result)
    (with-current-buffer "*ZFCert Goals*"
      (should (string-match-p "GOAL 1 / 1" (buffer-string)))
      (should (string-match-p "H : ∀x, ¬x ∈ b" (buffer-string)))
      (should (string-match-p "⊢ a ∈ b" (buffer-string))))))

(ert-deftest zfcert-render-result-shows-rejection ()
  (zfcert--render-result
   '((ok . nil) (line . 3) (message . "Unknown tactic.")))
  (with-current-buffer "*ZFCert Goals*"
    (should (string-match-p "Rejected · line 3" (buffer-string)))
    (should (string-match-p "Unknown tactic." (buffer-string)))))

(ert-deftest zfcert-render-result-shows-aliases ()
  (zfcert--render-result
   '((ok . t)
     (aliasesOnly . t)
     (aliases . (((name . "is_empty")
                  (parameters . ("x"))
                  (statement . "forall y, not (y in x)"))))))
  (with-current-buffer "*ZFCert Goals*"
    (should (string-match-p "1 aliases" (buffer-string)))
    (should (string-match-p "is_empty x" (buffer-string)))))

(ert-deftest zfcert-render-result-shows-global-choices ()
  (zfcert--render-result
   '((ok . t)
     (aliasesOnly . t)
     (aliases . nil)
     (constants . ("empty"))
     (facts . (((name . "Hempty")
                (formula . "∀y, ¬y ∈ empty"))))))
  (with-current-buffer "*ZFCert Goals*"
    (should (string-match-p "1 constants" (buffer-string)))
    (should (string-match-p "empty (constant)" (buffer-string)))
    (should (string-match-p "Hempty : ∀y, ¬y ∈ empty" (buffer-string)))))

;;; zfcert-mode-test.el ends here
