;;; zfcert-mode.el --- Interactive editing for ZFCert proofs -*- lexical-binding: t; -*-

;; Copyright (C) 2026
;; Version: 0.1.0
;; Package-Requires: ((emacs "26.1"))
;; Keywords: languages, tools, theorem-proving

;;; Commentary:

;; A major mode and HTTP client for ZFCert proof files.  It can start the
;; local OCaml server, check a complete proof, and show the proof state at
;; the current line.

;;; Code:

(require 'cl-lib)
(require 'easymenu)
(require 'json)
(require 'url)
(require 'url-http)
(require 'url-parse)

(defgroup zfcert nil
  "Interactive support for ZFCert proofs."
  :group 'languages
  :prefix "zfcert-")

(defcustom zfcert-server-url "http://127.0.0.1:8099"
  "Base URL of the ZFCert kernel."
  :type 'string
  :group 'zfcert)

(defcustom zfcert-workspace-root nil
  "ZFCert project directory.
When nil, search upwards for `dune-project' from the current buffer."
  :type '(choice (const :tag "Discover automatically" nil) directory)
  :group 'zfcert)

(defcustom zfcert-dune-executable "dune"
  "Dune executable used to start the local kernel."
  :type 'string
  :group 'zfcert)

(defcustom zfcert-auto-start-kernel t
  "Whether commands should start an unavailable local kernel."
  :type 'boolean
  :group 'zfcert)

(defcustom zfcert-auto-refresh nil
  "Whether to refresh the proof state after edits.
Automatic refresh is deliberately disabled by default because checking uses
a synchronous local HTTP request."
  :type 'boolean
  :group 'zfcert)

(defcustom zfcert-auto-refresh-delay 0.35
  "Idle time in seconds before automatically refreshing the proof state."
  :type 'number
  :group 'zfcert)

(defcustom zfcert-request-timeout 3
  "HTTP timeout in seconds for kernel requests."
  :type 'number
  :group 'zfcert)

(defvar zfcert--kernel-process nil)
(defvar zfcert--refresh-timer nil)
(defvar-local zfcert--error-overlay nil)

(defconst zfcert--font-lock-keywords
  `((,(regexp-opt '("Definition" "theorem" "qed") 'symbols)
     . font-lock-keyword-face)
    (,(regexp-opt
       '("rule" "intro" "exact" "apply" "specialize" "cases" "use"
         "refl" "split" "constructor" "assumption" "contradiction"
         "left" "right" "separation" "replacement")
       'symbols)
     . font-lock-builtin-face)
    (,(regexp-opt
       '("axiom" "hypothesis" "falsum_elim" "impl_intro" "impl_elim"
         "conj_intro" "conj_elim_l" "conj_elim_r" "disj_intro_l"
         "disj_intro_r" "disj_elim" "all_intro" "all_elim" "ex_intro"
         "ex_elim" "equal_refl" "equal_elim" "cut")
       'symbols)
     . font-lock-function-name-face)
    (,(regexp-opt
       '("forall" "exists" "not" "and" "or" "in" "false")
       'symbols)
     . font-lock-constant-face)
    (,(regexp-opt
       '("empty_set" "extensionality" "pairing" "union" "power_set"
         "infinity" "foundation" "choice")
       'symbols)
     . font-lock-variable-name-face)
    ("\\_<theorem\\_>[[:space:]]+\\([[:word:]_']+\\)"
     1 font-lock-function-name-face)
    ("\\_<Definition\\_>[[:space:]]+\\([[:word:]_']+\\)"
     1 font-lock-variable-name-face)))

(defvar zfcert-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?# "<" table)
    (modify-syntax-entry ?\n ">" table)
    (modify-syntax-entry ?' "w" table)
    table)
  "Syntax table for `zfcert-mode'.")

(defvar zfcert-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-n") #'zfcert-run-to-point)
    (define-key map (kbd "C-c C-c") #'zfcert-check-buffer)
    (define-key map (kbd "C-c C-g") #'zfcert-show-goals)
    (define-key map (kbd "C-c C-r") #'zfcert-restart-kernel)
    (define-key map (kbd "C-c C-k") #'zfcert-stop-kernel)
    map)
  "Keymap for `zfcert-mode'.")

(define-derived-mode zfcert-goals-mode special-mode "ZFCert-Goals"
  "Mode for displaying ZFCert proof states."
  (setq-local truncate-lines nil))

(defun zfcert--base-url ()
  (replace-regexp-in-string "/+\\'" "" zfcert-server-url))

(defun zfcert--decode-utf8-response (text)
  "Decode raw UTF-8 response TEXT returned by Emacs' URL library."
  (decode-coding-string
   (if (multibyte-string-p text)
       (encode-coding-string text 'iso-latin-1-unix)
     text)
   'utf-8-unix))

(defun zfcert--request (method endpoint &optional body timeout)
  "Send METHOD request to ENDPOINT with BODY and decode its JSON response."
  (let* ((url-request-method method)
         (url-request-data
          (and body (encode-coding-string body 'utf-8)))
         (url-request-extra-headers
          '(("Content-Type" . "text/plain; charset=utf-8")))
         (url-show-status nil)
         (target (concat (zfcert--base-url) "/" endpoint))
         (response
          (url-retrieve-synchronously
           target t t (or timeout zfcert-request-timeout))))
    (unless response
      (error "ZFCert kernel request timed out"))
    (unwind-protect
        (with-current-buffer response
          (unless (and (boundp 'url-http-response-status)
                       (numberp url-http-response-status)
                       (<= 200 url-http-response-status)
                       (< url-http-response-status 300))
            (error "ZFCert kernel returned HTTP %s"
                   (or (and (boundp 'url-http-response-status)
                            url-http-response-status)
                       "?")))
          (goto-char (or (and (boundp 'url-http-end-of-headers)
                              url-http-end-of-headers)
                         (point-min)))
          (let* ((raw
                  (buffer-substring-no-properties
                   (point) (point-max)))
                 (decoded (zfcert--decode-utf8-response raw))
                 (json-object-type 'alist)
                 (json-array-type 'list)
                 (json-key-type 'symbol)
                 (json-false nil))
            (json-read-from-string decoded)))
      (kill-buffer response))))

(defun zfcert--healthy-p ()
  (condition-case nil
      (equal (alist-get 'service
                        (zfcert--request "GET" "api/health" nil 0.4))
             "zfcert")
    (error nil)))

(defun zfcert--project-root ()
  (or (and zfcert-workspace-root
           (expand-file-name zfcert-workspace-root))
      (let ((start
             (if buffer-file-name
                 (file-name-directory buffer-file-name)
               default-directory)))
        (locate-dominating-file start "dune-project"))))

(defun zfcert--kernel-port ()
  (let* ((parsed (url-generic-parse-url zfcert-server-url))
         (scheme (url-type parsed)))
    (or (url-port parsed)
        (if (equal scheme "https") 443 80))))

(defun zfcert--local-server-p ()
  (member (url-host (url-generic-parse-url zfcert-server-url))
          '("127.0.0.1" "localhost" "::1")))

(defun zfcert--start-kernel ()
  (unless (zfcert--local-server-p)
    (user-error
     "Automatic kernel startup is only available for localhost URLs"))
  (let ((root (zfcert--project-root)))
    (unless (and root (file-exists-p (expand-file-name "dune-project" root)))
      (user-error
       "Cannot find dune-project; customize `zfcert-workspace-root'"))
    (when (process-live-p zfcert--kernel-process)
      (delete-process zfcert--kernel-process))
    (let ((default-directory root)
          (output (get-buffer-create "*ZFCert Kernel*")))
      (setq zfcert--kernel-process
            (make-process
             :name "zfcert-kernel"
             :buffer output
             :command
             (list zfcert-dune-executable
                   "exec" "src/main.exe" "--"
                   "--port" (number-to-string (zfcert--kernel-port)))
             :connection-type 'pipe
             :noquery t
             :sentinel
             (lambda (process event)
               (when (buffer-live-p (process-buffer process))
                 (with-current-buffer (process-buffer process)
                   (goto-char (point-max))
                   (insert (format "\nKernel %s" event))))))))
    (let ((attempt 0))
      (while (and (< attempt 40)
                  (process-live-p zfcert--kernel-process)
                  (not (zfcert--healthy-p)))
        (setq attempt (1+ attempt))
        (accept-process-output zfcert--kernel-process 0.1))
      (unless (zfcert--healthy-p)
        (display-buffer "*ZFCert Kernel*")
        (error "The ZFCert kernel did not become ready")))))

(defun zfcert--ensure-kernel ()
  (unless (zfcert--healthy-p)
    (if zfcert-auto-start-kernel
        (zfcert--start-kernel)
      (user-error
       "ZFCert kernel is unavailable; run `zfcert-restart-kernel'"))))

(defun zfcert-stop-kernel ()
  "Stop the kernel process started by this Emacs instance."
  (interactive)
  (when (process-live-p zfcert--kernel-process)
    (delete-process zfcert--kernel-process))
  (setq zfcert--kernel-process nil)
  (message "ZFCert kernel stopped"))

(defun zfcert-restart-kernel ()
  "Restart the local ZFCert kernel."
  (interactive)
  (zfcert-stop-kernel)
  (zfcert--start-kernel)
  (message "ZFCert kernel restarted"))

(defun zfcert--clear-error-overlay ()
  (when (overlayp zfcert--error-overlay)
    (delete-overlay zfcert--error-overlay))
  (setq zfcert--error-overlay nil))

(defun zfcert--mark-error (line message)
  (zfcert--clear-error-overlay)
  (save-excursion
    (goto-char (point-min))
    (forward-line (max 0 (1- (or line 1))))
    (setq zfcert--error-overlay
          (make-overlay (line-beginning-position) (line-end-position)))
    (overlay-put zfcert--error-overlay 'face 'error)
    (overlay-put zfcert--error-overlay 'help-echo message)))

(defun zfcert--insert-definitions (definitions)
  (dolist (definition definitions)
    (insert
     (propertize
      (mapconcat #'identity
                 (cons (alist-get 'name definition)
                       (alist-get 'parameters definition))
                 " ")
      'face 'font-lock-variable-name-face)
     " := " (or (alist-get 'statement definition) "") "\n")))

(defun zfcert--render-result (result)
  (let ((buffer (get-buffer-create "*ZFCert Goals*")))
    (with-current-buffer buffer
      (let ((inhibit-read-only t))
        (erase-buffer)
        (zfcert-goals-mode)
        (cond
         ((not (alist-get 'ok result))
          (insert (propertize
                   (format "Rejected · line %s\n\n"
                           (or (alist-get 'line result) "?"))
                   'face 'error)
                  (or (alist-get 'message result) "Unknown error") "\n"))
         ((alist-get 'definitionsOnly result)
          (let ((definitions (alist-get 'definitions result)))
            (insert (propertize
                     (format "%d definitions\n\n" (length definitions))
                     'face 'success))
            (zfcert--insert-definitions definitions)))
         ((or (alist-get 'qed result)
              (not (assq 'goals result)))
          (insert (propertize
                   (format "Verified · %s steps\n\n"
                           (or (alist-get 'steps result) 0))
                   'face 'success)
                  (or (alist-get 'theorem result) "") "\n"
                  (or (alist-get 'statement result) "") "\n"))
         ((alist-get 'complete result)
          (insert (propertize "0 goals\n\n" 'face 'success)
                  "All goals solved. Add qed. to finish.\n"))
         (t
          (let ((goals (alist-get 'goals result))
                (steps (or (alist-get 'steps result) 0)))
            (insert (format "%d steps · %d goals\n\n"
                            steps (length goals)))
            (cl-loop
             for goal in goals
             for index from 1
             do
             (insert (propertize
                      (format "GOAL %d / %d\n" index (length goals))
                      'face 'font-lock-keyword-face))
             (let ((context (alist-get 'context goal)))
               (if context
                   (dolist (entry context)
                     (insert
                      (propertize (alist-get 'name entry)
                                  'face 'font-lock-variable-name-face)
                      " : " (alist-get 'formula entry) "\n"))
                 (insert (propertize "No assumptions\n"
                                     'face 'shadow))))
             (insert "\n⊢ "
                     (propertize (alist-get 'target goal)
                                 'face 'font-lock-function-name-face)
                     "\n\n")))))
        (goto-char (point-min))))
    buffer))

(defun zfcert--apply-result (result &optional display)
  (if (alist-get 'ok result)
      (zfcert--clear-error-overlay)
    (zfcert--mark-error
     (alist-get 'line result)
     (or (alist-get 'message result) "ZFCert error")))
  (let ((goals-buffer (zfcert--render-result result)))
    (when display
      (display-buffer goals-buffer)))
  (if (alist-get 'ok result)
      (message "%s" (or (alist-get 'message result) "ZFCert accepted"))
    (message "ZFCert: line %s: %s"
             (or (alist-get 'line result) "?")
             (or (alist-get 'message result) "Rejected")))
  result)

(defun zfcert--buffer-through-line ()
  (buffer-substring-no-properties
   (point-min)
   (line-end-position)))

(defun zfcert-run-to-point ()
  "Check the current proof through the line containing point."
  (interactive)
  (zfcert--ensure-kernel)
  (zfcert--apply-result
   (zfcert--request "POST" "api/step" (zfcert--buffer-through-line))
   t))

(defun zfcert-check-buffer ()
  "Check the complete proof in the current buffer."
  (interactive)
  (zfcert--ensure-kernel)
  (zfcert--apply-result
   (zfcert--request
    "POST" "api/check"
    (buffer-substring-no-properties (point-min) (point-max)))
   t))

(defun zfcert-show-goals ()
  "Refresh and display the proof state at point."
  (interactive)
  (zfcert-run-to-point))

(defun zfcert--refresh-current-buffer (buffer)
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (when (and zfcert-auto-refresh
                 (derived-mode-p 'zfcert-mode))
        (condition-case error-data
            (progn
              (zfcert--ensure-kernel)
              (zfcert--apply-result
               (zfcert--request
                "POST" "api/step" (zfcert--buffer-through-line))
               nil))
          (error
           (message "ZFCert: %s" (error-message-string error-data))))))))

(defun zfcert--schedule-refresh (&rest _)
  (when (timerp zfcert--refresh-timer)
    (cancel-timer zfcert--refresh-timer))
  (when zfcert-auto-refresh
    (setq zfcert--refresh-timer
          (run-with-idle-timer
           zfcert-auto-refresh-delay nil
           #'zfcert--refresh-current-buffer (current-buffer)))))

(defun zfcert--cancel-refresh ()
  (when (timerp zfcert--refresh-timer)
    (cancel-timer zfcert--refresh-timer)
    (setq zfcert--refresh-timer nil)))

;;;###autoload
(define-derived-mode zfcert-mode prog-mode "ZFCert"
  "Major mode for editing and checking ZFCert proof scripts."
  :syntax-table zfcert-mode-syntax-table
  (setq-local font-lock-defaults '(zfcert--font-lock-keywords))
  (setq-local comment-start "# ")
  (setq-local comment-end "")
  (setq-local indent-tabs-mode nil)
  (add-hook 'after-change-functions #'zfcert--schedule-refresh nil t)
  (add-hook 'kill-buffer-hook #'zfcert--cancel-refresh nil t))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.zfp\\'" . zfcert-mode))

(easy-menu-define zfcert-mode-menu zfcert-mode-map
  "Menu for ZFCert proof buffers."
  '("ZFCert"
    ["Run to Point" zfcert-run-to-point t]
    ["Check Buffer" zfcert-check-buffer t]
    ["Show Goals" zfcert-show-goals t]
    "---"
    ["Restart Kernel" zfcert-restart-kernel t]
    ["Stop Kernel" zfcert-stop-kernel t]))

(provide 'zfcert-mode)

;;; zfcert-mode.el ends here
