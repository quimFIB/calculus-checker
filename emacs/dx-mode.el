;;; dx-mode.el --- Rocq-style mode for calculus-checker .dx files, over LSP -*- lexical-binding: t; -*-

;; Requires Emacs 29 or later (eglot).  See app/LSP.md in the repository.

;;; Commentary:

;; A .dx file is a tactic script (app/SCRIPT.md) whose first sentence names
;; the goal: `problem ID.' or `goal G [functions f/1, ...].'.  As coq-lsp
;; does for Rocq, the checker's language server (`./calc --lsp') checks
;; the whole buffer as you type: the checked prefix is shaded, a refused
;; sentence is a flymake error, and *dx-goals* shows the goal at point.
;;
;; Untrusted, like all of the app: every verdict shown is a string the
;; kernel produced.
;;
;; Keys:
;;   C-c C-l             show the goals and response windows
;;   C-c C-t             the next hint rung at point (a numeric prefix picks it)
;;   C-c C-a             use the refusal's suggestion (an eglot quickfix)
;;   C-c C-e             evaluate the integral at point, or in the region
;;                       (C-u: insert the proof at point)
;;   C-c C-p             toggle the pretty display
;;   C-c TAB             complete a move name into its template
;; Diagnostics, completion-at-point and code actions are eglot's own.
;; Doom Emacs users: see emacs/doom/dx/README.org for the :lang dx module.

;;; Code:

(require 'cl-lib)
(require 'subr-x)
(require 'seq)
(require 'eglot)
(require 'jsonrpc)
(require 'flymake)

(defgroup dx nil
  "Checking calculus-checker .dx scripts."
  :group 'languages
  :prefix "dx-")

(defconst dx--here
  (file-name-directory
   ;; the real file: a linked dx-mode.el still finds ../calc
   (file-truename (or load-file-name buffer-file-name default-directory)))
  "The directory this file was loaded from.")

(defcustom dx-calc-program
  (let ((local (expand-file-name "../calc" dx--here)))
    (if (file-executable-p local) local "calc"))
  "The checker to run: the repository's ./calc by default."
  :type 'string)

(defcustom dx-calc-args '("--lsp")
  "Arguments for `dx-calc-program'."
  :type '(repeat string))

(defcustom dx-eglot-auto t
  "Non-nil connects a .dx buffer to the checker when it is opened."
  :type 'boolean)

(defcustom dx-pretty t
  "Non-nil turns on the pretty display (`prettify-symbols-mode')."
  :type 'boolean)

(defcustom dx-goals-2d t
  "Non-nil draws the goal in *dx-goals* in two dimensions: fractions
stacked, roots with a bar, integrals with their limits (app/GOALS2D.md).
The one-line goal is shown instead when the drawing is wider than the
goals window."
  :type 'boolean)

(defcustom dx-goals-delay 0.2
  "Seconds point must rest before *dx-goals* follows it."
  :type 'number)

(defface dx-locked-face
  '((((background dark)) :background "#1f3a2a" :extend t)
    (t :background "#dcefe2" :extend t))
  "The checked sentences.")

(defface dx-pending-face
  '((((background dark)) :background "#3d3418")
    (t :background "#fdf0c9"))
  "The sentence being checked.")

(defconst dx-moves
  '("ftc" "int_improper" "close" "rewrite" "fact" "int_subst" "int_flip"
    "int_parts" "taylor_lagrange" "bound" "verify")
  "The moves, as app/SCRIPT.md names them.")

(defconst dx-templates
  '(("ftc" . "ftc _ by ring.")
    ("int_improper" . "int_improper _ by field.")
    ("close" . "close _ by ring.")
    ("rewrite" . "rewrite entry at _.")
    ("fact" . "fact h := entry with a := _.")
    ("int_subst" . "int_subst x := _ as t from _ to _ by ring.")
    ("int_flip" . "int_flip.")
    ("int_parts" . "int_parts in x with u := _; v := _ by ring.")
    ("taylor_lagrange" . "taylor_lagrange h := lower of _ in u from _ to _ at _ derivs _; _ increasing by field.")
    ("bound" . "bound by field using h.")
    ("verify" . "verify by field."))
  "Each move's shape, as script.TEMPLATES has it (app/PRETTY.md).")

(defconst dx-pretty-symbols
  (append
   '(("Int" . ?∫) ("sqrt" . ?√) ("pi" . ?π) ("oo" . ?∞) ("<=" . ?≤)
     (">=" . ?≥) ("==" . ?≐) (":=" . ?≔) ("->" . ?→) ("/\\" . ?∧))
   (mapcar (lambda (g) (cons (car g) (cdr g)))
           '(("alpha" . ?α) ("beta" . ?β) ("gamma" . ?γ) ("delta" . ?δ)
             ("epsilon" . ?ε) ("zeta" . ?ζ) ("eta" . ?η) ("theta" . ?θ)
             ("iota" . ?ι) ("kappa" . ?κ) ("lambda" . ?λ) ("mu" . ?μ)
             ("nu" . ?ν) ("xi" . ?ξ) ("rho" . ?ρ) ("sigma" . ?σ)
             ("tau" . ?τ) ("upsilon" . ?υ) ("phi" . ?φ) ("chi" . ?χ)
             ("psi" . ?ψ) ("omega" . ?ω))))
  "What the pretty display draws in place of the grammar's words.
Only the drawing changes: the buffer, what is saved and what is sent stay
plain text (app/DX.md).  `*' is left alone: it would draw `(*' as `(·'.")

;;;; Eglot (app/LSP.md)

(defun dx--contact (&rest _)
  (cons dx-calc-program dx-calc-args))

(add-to-list 'eglot-server-programs '(dx-mode . dx--contact))

(defun dx--point (pos)
  "The buffer position of the LSP position POS."
  (if (fboundp 'eglot-lsp-position-to-point)
      (eglot-lsp-position-to-point pos)
    (eglot--lsp-position-to-point pos)))

(defun dx--line-end (pos)
  "POS, or past its newline when only a newline follows: a full-width band."
  (if (eq (char-after pos) ?\n) (1+ pos) pos))

(defun dx--docver ()
  "The version eglot last sent of this buffer's text.
Newer eglot (Doom pins 1.24) renamed `eglot--versioned-identifier' to `eglot--docver'."
  (if (boundp 'eglot--docver) (symbol-value 'eglot--docver)
    (bound-and-true-p eglot--versioned-identifier)))

(defun dx--buffer-of (uri)
  "The live dx-mode buffer visiting URI, or nil."
  (let* ((path (if (fboundp 'eglot-uri-to-path) (eglot-uri-to-path uri)
                 (eglot--uri-to-path uri)))
         (buf (find-buffer-visiting path)))
    (and buf (with-current-buffer buf (derived-mode-p 'dx-mode)) buf)))

(defvar-local dx--checked-ov nil)
(defvar-local dx--running-ov nil)
(defvar-local dx--goals-seq 0 "The latest dx/goals request; older replies are dropped.")
(defvar-local dx--goals-at nil "(TICK . POINT) the goals window shows.")
(defvar-local dx--hint nil "(NODE . RUNG) of the last hint.")

(defun dx--overlay (sym start end face)
  "Put the overlay held in SYM on START..END with FACE, or remove it."
  (let ((ov (symbol-value sym)))
    (cond
     ((or (null start) (null end) (>= start end))
      (when (overlayp ov) (delete-overlay ov))
      (set sym nil))
     (t
      (if (overlayp ov) (move-overlay ov start end)
        (setq ov (make-overlay start end nil nil nil))
        (overlay-put ov 'priority -50)
        (set sym ov))
      (overlay-put ov 'face face)))))

(cl-defmethod eglot-handle-notification
  (_server (_method (eql dx/progress)) &key uri version checkedEnd running
           &allow-other-keys)
  "Shade the checked prefix and the sentence being checked."
  (when-let ((buf (dx--buffer-of uri)))
    (with-current-buffer buf
      (when (eql version (dx--docver)) ; else a stale text
        (dx--overlay 'dx--checked-ov (point-min)
                     (and checkedEnd (dx--line-end (dx--point checkedEnd)))
                     'dx-locked-face)
        (dx--overlay 'dx--running-ov
                     (and running (dx--point (plist-get running :start)))
                     (and running (dx--point (plist-get running :end)))
                     'dx-pending-face)
        (setq dx--goals-at nil)
        (dx--goals-refresh)))))

(defun dx--position-params ()
  (list :textDocument (eglot--TextDocumentIdentifier)
        :position (eglot--pos-to-lsp-position)))

(defun dx--request (method params then)
  "Send METHOD with PARAMS; THEN gets the result in this buffer."
  (let ((buf (current-buffer)))
    (jsonrpc-async-request
     (eglot--current-server-or-lose) method params
     :success-fn (lambda (result)
                   (when (buffer-live-p buf)
                     (with-current-buffer buf (funcall then result))))
     :error-fn (lambda (err)
                 (when (buffer-live-p buf)
                   (dx--show-response
                    (format "dx: %s" (plist-get err :message)))))
     :deferred method)))

(defun dx--goals-refresh ()
  "Ask for the goal at point, unless *dx-goals* already shows it."
  (when (and (derived-mode-p 'dx-mode) (eglot-current-server))
    (let ((at (cons (buffer-modified-tick) (point))))
      (unless (equal at dx--goals-at)
        (setq dx--goals-at at)
        (dx--show-diagnostics-here)
        (let ((seq (setq dx--goals-seq (1+ dx--goals-seq))))
          (dx--request :dx/goals (dx--position-params)
                       (lambda (node)
                         (when (= seq dx--goals-seq)
                           (dx--show-goals
                            (if node (dx--node-text node)
                              "No goal: the header is not checked."))))))))))

(declare-function flycheck-overlay-errors-in "ext:flycheck")
(declare-function flycheck-error-message "ext:flycheck")

(defun dx--diagnostics-here ()
  "The messages of the diagnostics on point's line: flymake's, or
flycheck's when it shows eglot's instead (as Doom Emacs sets it up)."
  (let ((beg (line-beginning-position)) (end (line-end-position)))
    (cond
     ((bound-and-true-p flymake-mode)
      (mapcar #'flymake-diagnostic-text (flymake-diagnostics beg end)))
     ((and (bound-and-true-p flycheck-mode)
           (fboundp 'flycheck-overlay-errors-in))
      ;; an empty line has no overlay in it: look one past its end
      (mapcar #'flycheck-error-message
              (flycheck-overlay-errors-in beg (min (1+ end) (point-max))))))))

(defun dx--show-diagnostics-here ()
  "Show the full message of a refusal on point's line in *dx-response*."
  (when-let ((ds (dx--diagnostics-here)))
    (dx--show-response (string-join (delete-dups ds) "\n"))))

(defvar dx--idle-timer nil)

(defun dx--idle ()
  (when (derived-mode-p 'dx-mode) (dx--goals-refresh)))

;;;; Commands

(defun dx-hint (&optional rung)
  "Ask for a hint on the goal at point: the next rung, or RUNG (1 to 3)."
  (interactive "P")
  (let ((ask (lambda (r)
               (dx--request
                :dx/hint (append (dx--position-params) (list :rung r))
                (lambda (body)
                  (let ((ref (plist-get body :refusal)))
                    (setq dx--hint (cons (plist-get body :node) r))
                    (dx--show-response
                     (if ref (format "%s: %s" (plist-get ref :code)
                                     (plist-get ref :message))
                       (format "Hint %s · %s\n%s\nCosts: %s"
                               (make-string r ??)
                               (plist-get body :integral)
                               (plist-get body :text)
                               (plist-get body :cost))))))))))
    (if rung (funcall ask (max 1 (min 3 (prefix-numeric-value rung))))
      ;; the next rung for the same node: ask the node first
      (dx--request :dx/goals (dx--position-params)
                   (lambda (node)
                     (let ((id (plist-get node :node)))
                       (funcall ask (if (equal (car dx--hint) id)
                                        (min 3 (1+ (cdr dx--hint)))
                                      1))))))))

(defconst dx--eval-words
  '(("proved" . "Proved by the kernel")
    ("unverified" . "SymPy's answer, not verified")
    ("outside-grammar" . "Outside the grammar")
    ("not-found" . "Not found")
    ("no-proposer" . "SymPy is not installed")
    ("has-parameters" . "Has parameters")
    ("no-goal" . "No goal yet: the header is not checked"))
  "Headlines for dx/evaluate's statuses (app/EVAL.md).")

(defun dx--evaluation-text (r)
  (let ((status (plist-get r :status))
        (num (plist-get r :numeric)))
    (concat
     (or (cdr (assoc status dx--eval-words)) status) "\n"
     (when (plist-get r :term) (format "%s\n" (plist-get r :term)))
     (when (plist-get r :value)
       (format "\n  %s %s\n" (if (equal status "proved") "=" "≟")
               (plist-get r :value)))
     (when (plist-get r :antiderivative)
       (format "\nF (%s) = %s\n"
               (if (eq (plist-get r :antiderivative_checked) t)
                   "checked by ftc" "SymPy's")
               (plist-get r :antiderivative)))
     (when (and num (plist-get num :value))
       (format "\n≈ %s  ~ (numeric, not a proof)\n" (plist-get num :value)))
     (unless (or (equal status "proved")
                 (string-empty-p (or (plist-get r :message) "")))
       (format "\n%s\n" (plist-get r :message)))
     (let ((ss (append (plist-get r :sentences) nil)))
       (when ss
         (concat "\n" (mapconcat #'identity ss "\n") "\n"
                 (when (equal status "proved")
                   "\n(C-u C-c C-e inserts these at point)\n")))))))

(defun dx-evaluate (&optional insert)
  "Evaluate the integral goal at point; SymPy proposes, the kernel proves.
With an active region, evaluate the region's text as an integral.  With a
prefix argument INSERT, put a proved result's sentences at point, which
is right after the sentence they were checked from (app/EVAL.md)."
  (interactive "P")
  (let* ((region (use-region-p))
         (params (if region
                     (list :textDocument (eglot--TextDocumentIdentifier)
                           :term (buffer-substring-no-properties
                                  (region-beginning) (region-end)))
                   (dx--position-params)))
         (at (point-marker)))
    (dx--show-response "Evaluating…")
    (dx--request
     :dx/evaluate params
     (lambda (r)
       (dx--show-response (dx--evaluation-text r))
       (when (and insert (not region) (equal (plist-get r :status) "proved"))
         (dx--request
          :dx/goals (list :textDocument (eglot--TextDocumentIdentifier)
                          :position (eglot--pos-to-lsp-position at))
          (lambda (node)
            (if (not (and node (eq (plist-get node :checked) t)
                          (equal (plist-get node :node) (plist-get r :node))))
                (message "Not inserted: point has moved past what is checked")
              (save-excursion
                (goto-char at)
                (unless (bolp) (insert "\n"))
                (insert (mapconcat #'identity
                                   (append (plist-get r :sentences) nil)
                                   "\n")
                        "\n"))))))))))

(defun dx-use-suggestion ()
  "Replace the refused sentence at point with the checker's suggestion."
  (interactive)
  (eglot-code-action-quickfix (point-min) (point-max)))

(defun dx-complete ()
  "Complete the move name before point into its template (app/PRETTY.md)."
  (interactive)
  (let* ((end (point))
         (start (save-excursion (skip-chars-backward "a-z_") (point)))
         (prefix (buffer-substring-no-properties start end))
         (choice (completing-read "Tactic: " dx-templates nil t prefix)))
    (when-let ((tpl (cdr (assoc choice dx-templates))))
      (delete-region start end)
      (insert tpl)
      (goto-char start)
      (when (search-forward "_" (+ start (length tpl)) t)
        (backward-char)))))

;;;; The goals and response windows

(defun dx--special-buffer (name)
  (let ((buf (get-buffer-create name)))
    (with-current-buffer buf
      (unless (derived-mode-p 'dx-goals-mode) (dx-goals-mode)))
    buf))

(defun dx--show-goals (text)
  (with-current-buffer (dx--special-buffer "*dx-goals*")
    (let ((inhibit-read-only t))
      (erase-buffer)
      (insert text)
      (goto-char (point-min)))))

(defun dx--show-response (text)
  (with-current-buffer (dx--special-buffer "*dx-response*")
    (let ((inhibit-read-only t))
      (erase-buffer)
      (insert (or text ""))
      (goto-char (point-min)))))

(defun dx--term-block (line drawing)
  "LINE, or DRAWING (the node's 2D field) when `dx-goals-2d' is on and it
fits the goals window; indented two spaces."
  (let* ((win (get-buffer-window "*dx-goals*" t))
         (width (if win (window-body-width win) 80))
         (rows (and dx-goals-2d (stringp drawing)
                    (split-string drawing "\n"))))
    (if (and rows (<= (+ 2 (apply #'max (mapcar #'string-width rows)))
                      width))
        (mapconcat (lambda (r) (concat "  " (string-trim-right r)))
                   rows "\n")
      (concat "  " line))))

(defun dx--node-text (n)
  "The goals text of the rendered node N (app/API.md), a plist."
  (concat
   (plist-get n :report)
   (when (eq (plist-get n :checked) :json-false)
     "\n(point is past what is checked: this is the last checked goal)")
   "\n"
   (when (plist-get n :goal)
     (format "\nGoal\n%s\n"
             (dx--term-block (plist-get n :goal) (plist-get n :goal_2d))))
   (when (plist-get n :theorem)
     (format "\nTheorem\n%s\n"
             (dx--term-block (plist-get n :theorem)
                             (plist-get n :theorem_2d))))
   (when (> (length (plist-get n :handles)) 0)
     (format "\nFacts: %s\n"
             (string-join (append (plist-get n :handles) nil) ", ")))
   (let ((obs (append (plist-get n :obligations) nil)))
     (format "\nObligations (%d)\n%s" (length obs)
             (mapconcat
              (lambda (o)
                (format "  %-10s %s%s  [%s]"
                        (plist-get o :status) (plist-get o :key)
                        (if (eq (plist-get o :new) t) " (new)" "")
                        (string-join
                         (delq nil (cons (plist-get o :method)
                                         (append (plist-get o :cites) nil)))
                         ", ")))
              obs "\n")))))

(defun dx-layout ()
  "Show the script, the goals and the response side by side."
  (interactive)
  (let ((script (current-buffer)))
    (delete-other-windows)
    (let* ((right (split-window-right))
           (below (with-selected-window right (split-window-below))))
      (set-window-buffer right (dx--special-buffer "*dx-goals*"))
      (set-window-buffer below (dx--special-buffer "*dx-response*"))
      (switch-to-buffer script)
      (setq dx--goals-at nil)
      (dx--goals-refresh))))

;;;; Modes

(defvar dx-mode-syntax-table
  (let ((st (make-syntax-table)))
    ;; (* comments *), which do not nest (no `n' flag), as the splitters say
    (modify-syntax-entry ?\( "()1" st)
    (modify-syntax-entry ?* ". 23" st)
    (modify-syntax-entry ?\) ")(4" st)
    (modify-syntax-entry ?_ "_" st)
    (modify-syntax-entry ?' "_" st)
    (dolist (c '(?+ ?- ?/ ?^ ?= ?< ?> ?# ?@ ?: ?\;))
      (modify-syntax-entry c "." st))
    st)
  "Syntax table for `dx-mode'.")

(defconst dx-font-lock-keywords
  `((,(regexp-opt '("problem" "goal" "functions") 'symbols)
     . font-lock-preprocessor-face)
    (,(regexp-opt dx-moves 'symbols) . font-lock-keyword-face)
    (,(regexp-opt '("by" "using" "with" "at" "occurrence" "as" "from" "to"
                    "reverse" "in" "derivs" "increasing" "decreasing" "strictly" "scale"
                    "lower" "upper" "of")
                  'symbols)
     . font-lock-builtin-face)
    (,(regexp-opt '("ring" "field") 'symbols) . font-lock-constant-face)
    ("\\_<rewrite\\s-+\\(\\(?:\\sw\\|\\s_\\)+\\)" 1 font-lock-function-name-face)
    ("\\_<fact\\s-+\\(?:\\sw\\|\\s_\\)+\\s-*:=\\s-*\\(\\(?:\\sw\\|\\s_\\)+\\)"
     1 font-lock-function-name-face)
    (,(regexp-opt '("Int" "D" "sqrt" "sin" "cos" "tan" "asin" "acos" "atan"
                    "exp" "ln" "abs" "sinh" "cosh" "tanh" "asinh" "acosh"
                    "atanh" "pi" "oo" "e_const")
                  'symbols)
     . font-lock-type-face))
  "Highlighting for `dx-mode'.")

(defun dx--pretty-setup ()
  (setq-local prettify-symbols-alist dx-pretty-symbols)
  (setq-local prettify-symbols-unprettify-at-point 'right-edge)
  (when dx-pretty (prettify-symbols-mode 1)))

(defvar dx-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m (kbd "C-c C-l") #'dx-layout)
    (define-key m (kbd "C-c C-t") #'dx-hint)
    (define-key m (kbd "C-c C-a") #'dx-use-suggestion)
    (define-key m (kbd "C-c C-e") #'dx-evaluate)
    (define-key m (kbd "C-c C-p") #'prettify-symbols-mode)
    (define-key m (kbd "C-c TAB") #'dx-complete)
    m)
  "Keys for `dx-mode'.")

;;;###autoload
(define-derived-mode dx-mode prog-mode "dx"
  "Check a calculus-checker .dx script as you type, through eglot.

\\{dx-mode-map}"
  :syntax-table dx-mode-syntax-table
  (setq-local comment-start "(* ")
  (setq-local comment-end " *)")
  (setq-local comment-start-skip "(\\*+\\s-*")
  (setq-local font-lock-defaults '(dx-font-lock-keywords))
  (dx--pretty-setup)
  (unless dx--idle-timer
    (setq dx--idle-timer (run-with-idle-timer dx-goals-delay t #'dx--idle)))
  (when (and dx-eglot-auto buffer-file-name)
    (eglot-ensure)))

(define-derived-mode dx-goals-mode special-mode "dx-goals"
  "The goals and responses of a `dx-mode' buffer."
  (setq-local font-lock-defaults '(dx-font-lock-keywords))
  (dx--pretty-setup))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.dx\\'" . dx-mode))

(provide 'dx-mode)
;;; dx-mode.el ends here
