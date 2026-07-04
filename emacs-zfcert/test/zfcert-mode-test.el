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

(ert-deftest zfcert-decodes-raw-utf8-http-response ()
  (let ((raw (apply #'string '(226 136 128 120 44 32 194 172))))
    (should (equal (zfcert--decode-utf8-response raw) "∀x, ¬"))))

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
   '((ok . nil) (line . 3) (message . "未知のタクティクです")))
  (with-current-buffer "*ZFCert Goals*"
    (should (string-match-p "Rejected · line 3" (buffer-string)))
    (should (string-match-p "未知のタクティクです" (buffer-string)))))

;;; zfcert-mode-test.el ends here
